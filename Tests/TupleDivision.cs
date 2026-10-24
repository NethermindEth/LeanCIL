#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics.X86;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/TupleDivision");
Directory.CreateDirectory(root);
const string profile = "x64-bmi2";
string Selector(string name) => $"TupleDivision::{name}(ulong,ulong,ulong)";

// ValueTuple`2 is auto layout: equal widths keep declaration order, mixed widths are reordered.
static long Offset<A, B>(bool second)
{
    var tuple = default(ValueTuple<A, B>);
    ref var start = ref Unsafe.As<ValueTuple<A, B>, byte>(ref tuple);
    return second ? Unsafe.ByteOffset(ref start, ref Unsafe.As<B, byte>(ref tuple.Item2))
        : Unsafe.ByteOffset(ref start, ref Unsafe.As<A, byte>(ref tuple.Item1));
}
if (typeof(ValueTuple<,>).IsAutoLayout != true || Unsafe.SizeOf<(ulong, ulong)>() != 16 ||
    Offset<ulong, ulong>(false) != 0 || Offset<ulong, ulong>(true) != 8 || Offset<uint, ulong>(false) != 8 || Offset<uint, ulong>(true) != 0)
    throw new InvalidOperationException("Runtime ValueTuple layout differs from the admitted auto-layout rule");
Console.WriteLine("PASS runtime ValueTuple<ulong, ulong> offsets 0 and 8; (uint, ulong) is reordered");

var hardware = X86Base.X64.IsSupported;
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.TupleDivision")!;
if (!hardware) Console.WriteLine("SKIP hardware comparison: X86Base.X64 is unsupported on this machine; using the UInt128 oracle only");

// The oracle is exact 128-by-64 division; the hardware result must agree with it.
static (ulong Quotient, ulong Remainder)? Oracle(ulong lower, ulong upper, ulong divisor)
{
    if (divisor == 0 || upper >= divisor) return null;
    var dividend = ((UInt128)upper << 64) | lower;
    return ((ulong)(dividend / divisor), (ulong)(dividend % divisor));
}
static string Bytes(ulong quotient, ulong remainder) =>
    "[" + string.Join(", ", BitConverter.GetBytes(quotient).Concat(BitConverter.GetBytes(remainder))) + "]";

ulong[] lowers = [0, 1, 1UL << 63, ulong.MaxValue];
ulong[] uppers = [0, 1, 1UL << 63, ulong.MaxValue - 1, ulong.MaxValue];
ulong[] divisors = [0, 1, 3, 1UL << 63, ulong.MaxValue];
var methods = new (string Name, Func<ulong, ulong, string> Result)[]
{
    ("Quotient", (q, r) => $".scalar (.i64 {q})"),
    ("Remainder", (q, r) => $".scalar (.i64 {r})"),
    ("Deconstruct", (q, r) => $".scalar (.i64 {q ^ r})"),
    ("Local", (q, r) => $".scalar (.i64 {unchecked(q - r)})"),
    ("Pair", (q, r) => $".scalar (.aggregate {Bytes(q, r)})")
};
// A balanced tree retains every claim without a linear-depth proof term.
string Balanced(IReadOnlyList<string> entries, bool proof)
{
    string Build(int start, int count)
    {
        if (count == 1) return entries[start];
        var half = count / 2;
        var left = Build(start, half);
        var right = Build(start + half, count - half);
        return proof ? $"⟨{left}, {right}⟩" : $"({left} ∧ {right})";
    }
    return Build(0, entries.Count);
}
var requests = new List<GeneratedVerification>();
var cases = 0;
foreach (var (name, result) in methods)
{
    var method = runtime.GetMethod(name)!;
    var claims = new List<string>();
    foreach (var lower in lowers)
    foreach (var upper in uppers)
    foreach (var divisor in divisors)
    {
        var expected = Oracle(lower, upper, divisor);
        if (hardware)
        {
            object? actual;
            try { actual = method.Invoke(null, [lower, upper, divisor]); }
            catch (TargetInvocationException error) when (error.InnerException is DivideByZeroException or OverflowException)
            {
                if (expected is not null || (divisor == 0) != error.InnerException is DivideByZeroException)
                    throw new InvalidOperationException($"Unexpected hardware fault for {name}({lower}, {upper}, {divisor})");
                actual = null;
            }
            var oracle = expected is not { } pair ? null : name switch
            {
                "Quotient" => pair.Quotient, "Remainder" => pair.Remainder, "Deconstruct" => pair.Quotient ^ pair.Remainder,
                "Local" => unchecked(pair.Quotient - pair.Remainder), _ => (object)pair
            };
            if (!Equals(actual, oracle)) throw new InvalidOperationException($"Hardware result differs for {name}({lower}, {upper}, {divisor})");
            if (actual is ValueTuple<ulong, ulong> tuple && Bytes(tuple.Item1, tuple.Item2) !=
                "[" + string.Join(", ", MemoryMarshal.AsBytes(MemoryMarshal.CreateReadOnlySpan(ref tuple, 1)).ToArray()) + "]")
                throw new InvalidOperationException("Runtime tuple bytes differ from Item1 at 0 and Item2 at 8");
        }
        var outcome = expected is { } value ? $".ok [{result(value.Quotient, value.Remainder)}]"
            : $".error ⟨0, 3, .arithmetic .{(divisor == 0 ? "divideByZero" : "overflow")}⟩";
        claims.Add($"(CIL.Safety.invoke Extracted.program 16 0 [.scalar (.i64 {lower}), .scalar (.i64 {upper}), .scalar (.i64 {divisor})] Examples.empty).map Prod.snd = {outcome}");
    }
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        string.Join("", claims.Select((claim, index) => $"theorem case{index} : {claim} := by rfl\n")) +
        "theorem correctness :\n" + Balanced(claims, false) + " :=\n" +
        Balanced(Enumerable.Range(0, claims.Count).Select(index => "case" + index).ToArray(), true) + "\nend ExampleProof\n");
    requests.Add(new GeneratedVerification(Selector(name), proof, output));
    cases += claims.Count;
}
verification.VerifyGeneratedBatch(assembly, "Examples", requests, profile);
Console.WriteLine($"PASS {cases} DivRem tuple comparisons over five Item1/Item2 read shapes" + (hardware ? " against hardware" : ""));

var contract = At("Examples/Proofs/DivRemQuotient.lean");
verification.Verify(assembly, "Examples", Selector("Quotient"), contract, Path.Combine(root, "Universal"), profile);
verification.Verify(assembly, "Examples", Selector("Quotient"), contract, Path.Combine(root, "Universal"), profile, check: true);
Console.WriteLine("PASS universal DivRem quotient and divide-error fault contract");
var wrongOutput = Path.Combine(root, "WrongQuotient");
var rejected = false;
try
{
    verification.Verify(assembly, "Examples", Selector("WrongQuotient"), contract, wrongOutput, profile);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}
if (!rejected || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Remainder implementation accepted as the quotient");
Console.WriteLine("PASS remainder implementation rejected by the quotient contract");

// A forged call, scope or tuple layout must never reach the model.
foreach (var (mutation, method, marker) in new[]
{
    ("scalar", "Quotient", "Reachable intrinsic lacks X86Base64"),
    ("scope", "Quotient", "Unresolved call"),
    ("version", "Quotient", "Unsupported runtime assembly scope"),
    ("signed", "Quotient", "External managed dependency"),
    ("return", "Quotient", "Rejected external call"),
    ("mixed", "Local", "auto layout reorders fields of different widths"),
    ("tuple-version", "Local", "Unsupported type"),
    ("field", "Quotient", "Unresolved tuple field")
})
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var body = module.GetType("Examples.TupleDivision").Methods.Single(m => m.Name == method).Body;
        var call = (MethodReference)body.Instructions.Single(i => i.Operand is MethodReference { Name: "DivRem" }).Operand;
        GenericInstanceType Tuple(TypeReference first, TypeReference second)
        {
            var tuple = new GenericInstanceType(((GenericInstanceType)call.ReturnType).ElementType);
            tuple.GenericArguments.Add(first);
            tuple.GenericArguments.Add(second);
            return tuple;
        }
        switch (mutation)
        {
            case "scope": call.DeclaringType.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
            case "signed":
                call.Parameters[1].ParameterType = module.TypeSystem.Int64;
                call.Parameters[2].ParameterType = module.TypeSystem.Int64;
                call.ReturnType = Tuple(module.TypeSystem.Int64, module.TypeSystem.Int64);
                break;
            case "return": call.ReturnType = Tuple(module.TypeSystem.UInt64, module.TypeSystem.Int64); break;
            case "mixed": body.Variables[0].VariableType = Tuple(module.TypeSystem.UInt32, module.TypeSystem.UInt64); break;
            case "tuple-version":
                var forged = new AssemblyNameReference("System.Runtime", new Version(9, 0, 0, 0)) { PublicKeyToken = [0xb0, 0x3f, 0x5f, 0x7f, 0x11, 0xd5, 0x0a, 0x3a] };
                module.AssemblyReferences.Add(forged);
                ((GenericInstanceType)body.Variables[0].VariableType).ElementType.Scope = forged;
                break;
            case "field":
                var load = body.Instructions.Single(i => i.OpCode.Code == Code.Ldfld);
                var original = (FieldReference)load.Operand;
                load.Operand = new FieldReference("Item3", original.FieldType, original.DeclaringType);
                break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", mutation == "scalar" ? assembly : dll, "Examples", Selector(method), output,
        mutation == "scalar" ? "scalar" : profile));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect DivRem rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
