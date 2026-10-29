#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/BinarySpans");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.BinarySpans")!;
var queue = new GeneratedQueue(verification, assembly);
foreach (var method in metadata.GetType("Examples.BinarySpans").Methods.Where(method => method.IsPublic))
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
            (1, "memory", ".thrown \"System.ArgumentOutOfRangeException\""),
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
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + """
        /-- Successful observations identify the checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- Misaligned caller storage exposes signed high bits and neighboring sentinel bytes. -/
        def memory : CIL.Safety.Memory := { Examples.empty with
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
        " := by\n  repeat constructor\n  all_goals first | (apply result_of_toOption; decide +kernel) | decide +kernel\n#print axioms correctness\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS endian transfers: " + name));
}
queue.Flush();
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
var controls = new GeneratedEvidence(Path.Combine(root, "EvidenceControls"));
var controlled = new HashSet<string>(StringComparer.Ordinal);
var index = 0;
foreach (var (name, before, after) in new[]
{
    ("ReadBig", ".binaryRead 2 true true false", ".binaryRead 2 false true false"),
    ("ReadBig", "returnType := .atom Extraction.runtimeScope \"System.IntPtr\", parameterTypes :=",
        "returnType := .atom Extraction.runtimeScope \"System.UIntPtr\", parameterTypes :="),
    ("ReadLittle", "ReadIntPtrLittleEndian", "ReadInt32LittleEndian"),
    ("TryReadBig", "TryReadUIntPtrBigEndian", "TryReadIntPtrBigEndian"),
    ("ReadBig", ".binaryRead 2 true true false", ".binaryRead 2 true false false"),
    ("ReadLittle", ".binaryRead 8 false false false", ".binaryRead 4 false false false"),
    ("TryReadBig", ".binaryRead 2 true true true", ".binaryRead 2 true true false"),
    ("WriteBig", ".binaryWrite 2 true false", ".binaryWrite 2 false false"),
    ("TryWriteLittle", ".binaryWrite 2 false true", ".binaryWrite 2 false false")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")),
        "method0_unsafe_validated");
    if (controlled.Add(source))
    {
        var controlPath = Path.Combine(root, name, "EvidenceControl.lean");
        File.WriteAllText(controlPath, source);
        controls.Add(controlPath, "PASS exact endian evidence control: " + name, "method0_unsafe_validated");
    }
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing endian mutation: " + before);
    var path = Path.Combine(root, $"Rejected{index++}.lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS exact endian evidence rejection: " + name, "UnsafeCallsValid");
}
controls.Check(replay: false);
rejected.Check();

partial class Program
{
    delegate ulong ReadBytes(ReadOnlySpan<byte> bytes);
    delegate void WriteBytes(Span<byte> bytes);
    delegate int TryWriteBytes(Span<byte> bytes);
}
