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
// Raw CIL may pass noncanonical int32 bits to narrow helpers; the helper must normalize them.
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var removed = 0;
    foreach (var method in module.GetType("Examples.Bits").Methods
        .Where(method => method.Name.StartsWith("PrimitiveNarrow", StringComparison.Ordinal)))
    foreach (var instruction in method.Body.Instructions)
        if (instruction.OpCode.Code is Mono.Cecil.Cil.Code.Conv_U1 or Mono.Cecil.Cil.Code.Conv_U2 or
            Mono.Cecil.Cil.Code.Conv_I1 or Mono.Cecil.Cil.Code.Conv_I2)
        {
            instruction.OpCode = Mono.Cecil.Cil.OpCodes.Nop;
            removed++;
        }
    if (removed != 22) throw new InvalidOperationException("Unexpected narrow helper conversion count: " + removed);
    assembly = Path.Combine(root, "Examples.dll");
    module.Write(assembly);
}
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
    // Primitive aliases share models covered by the full BitOperations matrix.
    if (method.Name.StartsWith("Primitive", StringComparison.Ordinal))
    {
        values = rotations ? [0, 0x8000000180000001, ulong.MaxValue] :
            [0, 1, 2, 1UL << 31, 1UL << 63, ulong.MaxValue];
        counts = rotations ? [-1, 0, 65] : [0];
    }
    var claims = new List<string>();
    var narrow = method.Name.StartsWith("PrimitiveNarrow", StringComparison.Ordinal);
    if (narrow) values = [0, 1, 2, 127, 128, 255, 256, 32767, 32768, 65535, 65536, uint.MaxValue];
    if (narrow && rotations)
    {
        values = [0, 1, 128, 255, 256, 32768, 65535, 65536];
        counts = [-17, -1, 0, 17];
    }
    // Different source bit patterns can become the same narrow runtime argument.
    var arguments = values.Select(bits => Value(parameters[0].ParameterType, bits)).Distinct();
    foreach (var value in arguments)
    foreach (var count in counts)
    {
        object[] inputs = rotations ? [value, count] : [value];
        var expected = method.Invoke(null, inputs)!;
        var fuel = narrow ? 96 : method.Name.StartsWith("PrimitiveCounts", StringComparison.Ordinal) ? 32 : 8;
        claims.Add($"(CIL.Safety.invoke Extracted.program {fuel} 0 " +
            $"[{string.Join(", ", inputs.Select(LeanValue))}] Examples.empty).map Prod.snd = " +
            $".ok [{LeanValue(expected)}]");
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) +
        "⟩\n#print axioms correctness\nend ExampleProof\n");
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
foreach (var mutation in new[] { "scope", "version", "instance", "return", "argument", "generic", "unsupported",
    "memory-scope", "memory-key", "signed-log", "wide-count", "native-count",
    "narrow-rotate-signed", "narrow-signed-log", "narrow-return" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string expectedDiagnostic;
    var fixture = mutation switch
    {
        "signed-log" => "PrimitivePopulation32",
        "wide-count" => "PrimitivePower64",
        "native-count" => "PrimitivePowerNative",
        "narrow-return" => "PrimitiveNarrow8",
        "narrow-rotate-signed" => "PrimitiveNarrowRotate8",
        "narrow-signed-log" => "PrimitiveNarrowSigned",
        "memory-scope" or "memory-key" => "ReverseU64",
        _ => "PrimitiveLeftU64"
    };
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Bits").Methods.Single(m => m.Name == fixture);
        selector = $"Bits::{fixture}({string.Join(",", method.Parameters.Select(p => p.ParameterType.FullName))})";
        var call = (MethodReference)method.Body.Instructions.First(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Call).Operand;
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
            case "signed-log": call.Name = "Log2"; break;
            case "narrow-rotate-signed":
                call.DeclaringType = module.TypeSystem.SByte;
                call.ReturnType = module.TypeSystem.SByte;
                call.Parameters[0].ParameterType = module.TypeSystem.SByte;
                break;
            case "narrow-return": call.ReturnType = module.TypeSystem.Int32; break;
            case "narrow-signed-log":
                call.Name = "Log2";
                call.ReturnType = call.Parameters[0].ParameterType;
                break;
            case "wide-count":
            case "native-count":
                call.Name = "PopCount";
                call.ReturnType = module.TypeSystem.Int32;
                break;
        }
        expectedDiagnostic = mutation switch
        {
            "scope" => "Unresolved call: " + call.FullName,
            "version" => "Unsupported type identity: System.UInt64 [System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a]",
            "memory-key" => "Unsupported runtime assembly scope: " + call.FullName,
            "instance" => "Invalid evaluation stack during reachability",
            "generic" => "Contract imports require an exact closed generic instantiation on a non-generic declaring type.",
            "return" or "argument" or "unsupported" or "memory-scope" or
                "signed-log" or "wide-count" or "native-count" or "narrow-rotate-signed" or
                "narrow-signed-log" or "narrow-return" => "External managed dependency: " + call.FullName,
            _ => throw new InvalidOperationException("Unknown runtime rejection fixture: " + mutation)
        };
        module.Write(dll);
    }
    var rejected = Execute(Extract("extract", dll, "Examples", selector, output));
    if (rejected.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) || File.Exists(Path.Combine(output, "verified.json")) ||
        !rejected.Output.Contains(expectedDiagnostic, StringComparison.Ordinal))
        throw new InvalidOperationException("Incorrect runtime rejection: " + mutation + "\n" + rejected.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}

Console.WriteLine($"Runtime helpers passed: {cases} comparisons; universal rotation and logarithm proofs; two incorrect implementations and fifteen invalid calls rejected.");
