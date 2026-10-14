#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/IntegerMath");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.IntegerMath")!;
var cases = 0;
object Value(Type type, ulong bits)
{
    if (type == typeof(sbyte)) return unchecked((sbyte)bits);
    if (type == typeof(byte)) return unchecked((byte)bits);
    if (type == typeof(nint)) return unchecked((nint)bits);
    if (type == typeof(nuint)) return unchecked((nuint)bits);
    if (type == typeof(short)) return unchecked((short)bits);
    if (type == typeof(ushort)) return unchecked((ushort)bits);
    if (type == typeof(int)) return unchecked((int)bits);
    if (type == typeof(uint)) return unchecked((uint)bits);
    if (type == typeof(long)) return unchecked((long)bits);
    if (type == typeof(ulong)) return bits;
    throw new InvalidOperationException("Unexpected fixture type: " + type);
}

string LeanValue(object value) => value switch
{
    bool x => $".scalar (.i32 {(x ? 1 : 0)})",
    sbyte x => $".scalar (.i32 {unchecked((uint)x)})",
    byte x => $".scalar (.i32 {x})",
    nint x => $".scalar (.i64 {unchecked((ulong)x)})",
    nuint x => $".scalar (.i64 {(ulong)x})",
    short x => $".scalar (.i32 {unchecked((uint)x)})",
    ushort x => $".scalar (.i32 {x})",
    int x => $".scalar (.i32 {unchecked((uint)x)})",
    uint x => $".scalar (.i32 {x})",
    long x => $".scalar (.i64 {unchecked((ulong)x)})",
    ulong x => $".scalar (.i64 {x})",
    _ => throw new InvalidOperationException("Unexpected value: " + value)
};

// Compare all overloads against the runtime, including exceptional outcomes.
foreach (var method in runtime.GetMethods(BindingFlags.Public | BindingFlags.Static).Where(m => !m.Name.StartsWith("Wrong", StringComparison.Ordinal)))
{
    var output = Path.Combine(root, method.Name);
    Directory.CreateDirectory(output);
    var parameters = method.GetParameters();
    var type = parameters[0].ParameterType;
    var values = new ulong[] { 0, 1, 2, 127, 128, 255, 32767, 32768, 65535, int.MaxValue, 1UL << 31, uint.MaxValue, long.MaxValue, 1UL << 63, ulong.MaxValue }
        .Select(x => Value(type, x)).Distinct().ToArray();
    var claims = new List<string>();
    foreach (var x in values)
    foreach (var y in parameters.Length > 1 ? values : values.Take(1))
    foreach (var z in parameters.Length > 2 ? values : values.Take(1))
    {
        object[] inputs = parameters.Length switch { 1 => [x], 2 => [x, y], _ => [x, y, z] };
        string expected;
        try
        {
            expected = $".ok [{LeanValue(method.Invoke(null, inputs)!)}]";
        }
        catch (TargetInvocationException error) when (error.InnerException is OverflowException or ArgumentException)
        {
            var fault = error.InnerException is OverflowException ? "overflow" : "invalidBounds";
            expected = $".error ⟨0, {parameters.Length}, .arithmetic .{fault}⟩";
        }
        claims.Add($"(CIL.Safety.invoke Extracted.program 8 0 [{string.Join(", ", inputs.Select(LeanValue))}] Examples.empty).map Prod.snd = {expected}");
    }

    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    var selector = $"IntegerMath::{method.Name}({string.Join(",", parameters.Select(p => p.ParameterType.FullName))})";
    verification.Verify(assembly, "Examples", selector, proof, output);
    cases += claims.Count;
    Console.WriteLine($"PASS {method.Name}: {claims.Count} runtime comparisons");
}

// A runtime helper model must never accept a forged identity or signature.
foreach (var mutation in new[] { "scope", "version", "instance", "return", "argument", "generic", "unsupported" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.IntegerMath").Methods.Single(m => m.Name == "MinInt32");
        var call = (MethodReference)method.Body.Instructions.Single(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Call).Operand;
        switch (mutation)
        {
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
            case "instance": call.HasThis = true; break;
            case "return": call.ReturnType = module.TypeSystem.Int64; break;
            case "argument": call.Parameters[1].ParameterType = module.TypeSystem.Int64; break;
            case "generic": call.GenericParameters.Add(new GenericParameter("T", call)); break;
            case "unsupported": call.Name = "CopySign"; break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", "IntegerMath::MinInt32(int,int)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !(result.Output.Contains("Unsupported") || result.Output.Contains("Unmodelled") ||
          result.Output.Contains("Unresolved call") ||
          mutation == "instance" && result.Output.Contains("Invalid evaluation stack during reachability")))
        throw new InvalidOperationException("Incorrect runtime rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
// The same universal specification must reject a maximum implementation.
var contract = At("Examples/Proofs/IntegerMinimum.lean");
verification.Verify(assembly, "Examples", "IntegerMath::MinInt64(long,long)", contract, Path.Combine(root, "UniversalMin"));
var wrongOutput = Path.Combine(root, "WrongMin");
var rejected = false;
try
{
    verification.Verify(assembly, "Examples", "IntegerMath::WrongMin(long,long)", contract, wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}
if (!rejected || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Maximum implementation accepted as minimum");

Console.WriteLine($"PASS {cases} integer Math runtime comparisons, universal minimum and incorrect implementation rejection");
