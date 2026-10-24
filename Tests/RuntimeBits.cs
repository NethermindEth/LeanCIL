#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/RuntimeBits");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Bits")!;
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);

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

// Every supported overload is extracted from compiled C#, then compared with .NET.
foreach (var method in runtime.GetMethods(BindingFlags.Public | BindingFlags.Static)
    .Where(m => !m.Name.Contains("RoundTrip") && !m.Name.StartsWith("Wrong", StringComparison.Ordinal)))
{
    var output = Path.Combine(root, method.Name);
    Directory.CreateDirectory(output);
    var parameters = method.GetParameters();
    var rotations = parameters.Length == 2;
    var values = new ulong[] { 0, 1, 2, 127, 128, 255, 256, 32767, 32768, 65535, uint.MaxValue, 1UL << 32, 1UL << 63, ulong.MaxValue, 0x0123456789abcdef, 0xaaaaaaaaaaaaaaaa };
    if (!rotations)
        values = values.Concat(Enumerable.Range(0, 64).SelectMany(i =>
            new[] { (1UL << i) - 1, 1UL << i, unchecked((1UL << i) + 1) })).Distinct().ToArray();
    var counts = rotations ? new[] { int.MinValue, -65, -33, -1, 0, 1, 31, 32, 33, 63, 64, 65, int.MaxValue } : new[] { 0 };
    var claims = new List<string>();
    foreach (var bits in values)
    foreach (var count in counts)
    {
        var value = Value(parameters[0].ParameterType, bits);
        object[] inputs = rotations ? [value, count] : [value];
        var expected = method.Invoke(null, inputs)!;
        claims.Add($"(CIL.Safety.invoke Extracted.program 8 0 [{string.Join(", ", inputs.Select(LeanValue))}] Examples.empty).map Prod.snd = .ok [{LeanValue(expected)}]");
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    var selector = $"Bits::{method.Name}({string.Join(",", parameters.Select(p => p.ParameterType.FullName))})";
    var comparisons = claims.Count;
    queue.Add(new(selector, proof, output), () =>
    {
        cases += comparisons;
        Console.WriteLine($"PASS {method.Name}: {comparisons} runtime comparisons");
    });
}
queue.Flush();

// A universal identity and a deliberately incorrect inverse use the same contract.
var contract = At("Examples/Proofs/RotateRoundTrip.lean");
verification.Verify(assembly, "Examples", "Bits::RoundTrip(ulong)", contract, Path.Combine(root, "RoundTrip"));
var wrongOutput = Path.Combine(root, "WrongRoundTrip");
var failed = false;
try
{
    verification.Verify(assembly, "Examples", "Bits::WrongRoundTrip(ulong)", contract, wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect rotation inverse accepted");

var logarithm = At("Examples/Proofs/IntegerLog2.lean");
verification.Verify(assembly, "Examples", "Bits::Log64(ulong)", logarithm, Path.Combine(root, "UniversalLog"));
var wrongLog = Path.Combine(root, "WrongLog");
failed = false;
try
{
    verification.Verify(assembly, "Examples", "Bits::WrongLog64(ulong)", logarithm, wrongLog);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongLog, "verified.json")))
    throw new InvalidOperationException("Incorrect integer logarithm accepted");

// Preserve exact runtime identity and signature checks for the new allowlist.
foreach (var mutation in new[] { "scope", "version", "instance", "return", "argument", "generic", "unsupported", "memory-scope", "memory-key" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string expectedDiagnostic;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Bits").Methods.Single(m => m.Name ==
            (mutation.StartsWith("memory-", StringComparison.Ordinal) ? "ReverseU64" : "Left64"));
        var call = (MethodReference)method.Body.Instructions.Single(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Call).Operand;
        switch (mutation)
        {
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
            case "instance": call.HasThis = true; break;
            case "return": call.ReturnType = module.TypeSystem.Int64; break;
            case "argument": call.Parameters[1].ParameterType = module.TypeSystem.Int64; break;
            case "generic": call.GenericParameters.Add(new GenericParameter("T", call)); break;
            case "unsupported": call.Name = "Log2"; break;
            case "memory-scope": call.DeclaringType.Scope = module.TypeSystem.CoreLibrary; break;
            case "memory-key": ((AssemblyNameReference)call.DeclaringType.Scope).PublicKeyToken = []; break;
        }
        expectedDiagnostic = mutation switch
        {
            "scope" => "Unresolved call: " + call.FullName,
            "version" => "Unsupported type identity: System.UInt64 [System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a]",
            "memory-key" => "Unsupported runtime assembly scope: " + call.FullName,
            "instance" => "Invalid evaluation stack during reachability",
            "generic" => "Contract imports require an exact closed generic instantiation on a non-generic declaring type.",
            "return" or "argument" or "unsupported" or "memory-scope" => "External managed dependency: " + call.FullName,
            _ => throw new InvalidOperationException("Unknown runtime rejection fixture: " + mutation)
        };
        module.Write(dll);
    }
    var selector = mutation.StartsWith("memory-", StringComparison.Ordinal) ? "Bits::ReverseU64(ulong)" : "Bits::Left64(ulong,int)";
    var rejected = Execute(Extract("extract", dll, "Examples", selector, output));
    if (rejected.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) || File.Exists(Path.Combine(output, "verified.json")) ||
        !rejected.Output.Contains(expectedDiagnostic, StringComparison.Ordinal))
        throw new InvalidOperationException("Incorrect runtime rejection: " + mutation + "\n" + rejected.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}

Console.WriteLine($"Runtime helpers passed: {cases} comparisons; universal rotation and logarithm proofs; two incorrect implementations and nine invalid calls rejected.");
