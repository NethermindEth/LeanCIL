#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include ../scripts/Checking/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include ModelOperandChecks.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/BinarySpans");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.BinarySpans")!;
var queue = new GeneratedQueue(verification, assembly);
var methods = metadata.GetType("Examples.BinarySpans").Methods.Where(method => method.IsPublic).ToArray();
foreach (var method in methods)
{
    var name = method.Name;
    var read = name.Contains("Read", StringComparison.Ordinal);
    var trying = name.StartsWith("Try", StringComparison.Ordinal);
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var claims = new List<string>();
    var lengths = trying ? new[] { 0, 1, 2, 4, 8 } : new[] { read ? 8 : 44 };
    foreach (var length in lengths)
    {
        var bytes = Enumerable.Range(0, 48).Select(index => (byte)(index * 37 + 128)).ToArray();
        var values = "[]";
        var runtimeMethod = runtime.GetMethod(name)!;
        if (read)
            values = $"[.scalar (.i64 {runtimeMethod.CreateDelegate<ReadBytes>()(bytes.AsSpan(1, length))})]";
        else if (trying)
            values = $"[.scalar (.i32 {runtimeMethod.CreateDelegate<TryWriteBytes>()(bytes.AsSpan(1, length))})]";
        else runtimeMethod.CreateDelegate<WriteBytes>()(bytes.AsSpan(1, length));
        var run = "CIL.Safety.invoke Extracted.program 512 0 " +
            $"[.bufferSpan ⟨.address ⟨0, 1⟩, {length}, 1, {(!read).ToString().ToLowerInvariant()}⟩] memory";
        if (read) claims.Add($"({run}).map Prod.snd = .ok {values}");
        else claims.Add($"({run}).map (fun result => (result.2, " +
            $"(CIL.Safety.read result.1 ⟨0, 0⟩ 48 1).toOption)) = .ok ({values}, " +
            $"some [{string.Join(", ", bytes)}])");
    }
    if (name == "ReadLittle")
    {
        foreach (var (length, storage, fault) in new[]
        {
            (1, "memory", ".thrown .argumentOutOfRange"),
            (8, "uninitialized", ".memory .uninitialized _ _")
        })
            claims.Add("(match CIL.Safety.invoke Extracted.program 512 0 " +
                $"[.bufferSpan ⟨.address ⟨0, 1⟩, {length}, 1, false⟩] {storage} with " +
                $"| .error ⟨_, _, {fault}⟩ => true | _ => false) = true");
    }
    if (name == "WriteLittle")
        claims.Add("(match CIL.Safety.invoke Extracted.program 512 0 " +
            "[.bufferSpan ⟨.address ⟨0, 1⟩, 28, 1, true⟩] readOnlyMemory with " +
            "| .error ⟨_, _, .memory .unwritable _ _⟩ => true | _ => false) = true");
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nnamespace ExampleProof\n" + """
        /-- Misaligned caller storage exposes signed high bits and neighboring sentinel bytes. -/
        def memory : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨48, 1, []⟩, true, [48]⟩ else none
          cells := fun _ offset => ⟨BitVec.ofNat 8 (offset * 37 + 128), true⟩
          views := [⟨0, 0, 48, true, true⟩]
          nextIdentity := 1 }
        /-- Missing initialization is distinct from a short buffer. -/
        def uninitialized : CIL.Safety.Memory := { memory with
          cells := fun _ offset => ⟨BitVec.ofNat 8 (offset * 37 + 128), false⟩ }
        /-- A writable span value grants no storage authority. -/
        def readOnlyMemory : CIL.Safety.Memory := { memory with
          views := [⟨0, 0, 48, true, false⟩] }
        /-- All admitted integer overloads agree with runtime results, including short try operations. -/
        """ + "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  repeat' apply And.intro\n  all_goals rfl\n" +
        "#print axioms correctness\nend ExampleProof\n");
    ModelOperandChecks.Append(proof, method, EndianModel);
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS endian transfers: " + name));
}
queue.Flush();

// The primitive's CLI type gives the expected width and sign independently of the model table.
static string? EndianModel(MethodReference call)
{
    if (call.DeclaringType.FullName != "System.Buffers.Binary.BinaryPrimitives") return null;
    bool read = call.Name.Contains("Read", StringComparison.Ordinal);
    bool trying = call.Name.StartsWith("Try", StringComparison.Ordinal);
    var integer = read && !trying ? call.ReturnType : call.Parameters[^1].ParameterType.GetElementType();
    var (width, signed) = integer.MetadataType switch
    {
        MetadataType.Int16 => (2, "true"), MetadataType.UInt16 => (2, "false"),
        MetadataType.Int32 => (4, "true"), MetadataType.UInt32 => (4, "false"),
        MetadataType.Int64 or MetadataType.IntPtr => (8, "true"),
        MetadataType.UInt64 or MetadataType.UIntPtr => (8, "false"),
        _ => throw new InvalidDataException($"Unexpected endian operand {integer}")
    };
    var order = call.Name.EndsWith("BigEndian", StringComparison.Ordinal) ? "true" : "false";
    var attempt = trying ? "true" : "false";
    return read ? $".memory (.binaryRead {width} {signed} {order} {attempt})"
        : $".memory (.binaryWrite {width} {order} {attempt})";
}

partial class Program
{
    delegate ulong ReadBytes(ReadOnlySpan<byte> bytes);
    delegate void WriteBytes(Span<byte> bytes);
    delegate int TryWriteBytes(Span<byte> bytes);
}
