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
#:include BulkCallEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/SpanCopies");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var methods = metadata.GetType("Examples.SpanCopies").Methods;
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.SpanCopies")!;
RuntimeChecks(runtime);
var queue = new GeneratedQueue(verification, assembly);
foreach (var method in methods.Where(method => method.IsPublic))
{
    var name = method.Name;
    var trying = name.StartsWith("Try", StringComparison.Ordinal);
    var width = name.EndsWith("Enum", StringComparison.Ordinal) ? 2 : name == "CopyLongs" ? 8 : 1;
    var writable = name is "Copy" or "TryCopy";
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var claims = new List<string>();
    string Run(int source, int length, int target, int capacity, string memory = "memory",
        bool destinationWritable = true) =>
        "CIL.Safety.invoke Extracted.program 32 0 [" +
        $".bufferSpan ⟨.address ⟨0, {source}⟩, {length}, {width}, {writable.ToString().ToLowerInvariant()}⟩, " +
        $".bufferSpan ⟨.address ⟨0, {target}⟩, {capacity}, {width}, " +
        $"{destinationWritable.ToString().ToLowerInvariant()}⟩] {memory}";
    void Success(int source, int length, int target, int capacity)
    {
        var fits = length <= capacity;
        var bytes = Enumerable.Range(0, 32).Select(index =>
            fits && target <= index && index < target + length * width ? source + index - target : index);
        var returned = trying ? $"[.scalar (.i32 {(fits ? 1 : 0)})]" : "[]";
        claims.Add($"({Run(source, length, target, capacity)}).map (fun result => " +
            $"(result.2, (CIL.Safety.read result.1 ⟨0, 0⟩ 32 1).toOption)) = " +
            $".ok ({returned}, some [{string.Join(", ", bytes)}])");
    }
    Success(0, 2, 16, 2);
    if (name == "TryCopyReadOnly")
    {
        Success(1, 6, 3, 6);
        Success(3, 6, 1, 6);
        Success(3, 6, 3, 6);
        Success(2, 5, 20, 3);
        Success(32, 0, 32, 0);
        claims.Add("(CIL.Safety.invoke Extracted.program 32 0 " +
            "[.bufferSpan ⟨.null, 0, 1, false⟩, .bufferSpan ⟨.null, 0, 1, true⟩] memory).map Prod.snd = " +
            ".ok [.scalar (.i32 1)]");
        claims.Add($"({Run(2, 5, 20, 3, "uninitialized")}).map Prod.snd = .ok [.scalar (.i32 0)]");
        claims.Add($"({Run(2, 5, 20, 5, "uninitialized")}).map Prod.snd = " +
            ".error ⟨0, 2, .memory .uninitialized (.address ⟨0, 2⟩) 5⟩");
        claims.Add($"({Run(2, 5, 20, 5, "readOnlyMemory")}).map Prod.snd = " +
            ".error ⟨0, 2, .memory .unwritable (.address ⟨0, 20⟩) 5⟩");
        claims.Add($"({Run(2, 5, 20, 5, destinationWritable: false)}).map Prod.snd = " +
            ".error ⟨0, 2, .invalidState⟩");
    }
    if (name == "CopyReadOnly")
    {
        claims.Add($"({Run(2, 5, 20, 3, "uninitialized")}).map Prod.snd = " +
            ".error ⟨0, 2, .thrown .argument⟩");
    }
File.WriteAllText(proof, $$"""
        import Extracted
        import CIL.Safety.StepComposition
        namespace ExampleProof
        /-- One allocation exposes overlapping and disjoint slices plus neighboring bytes. -/
        def memory : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
          cells := fun _ offset => ⟨BitVec.ofNat 8 offset, true⟩
          views := [⟨0, 0, 32, true, true⟩]
          nextIdentity := 1 }
        /-- Uninitialized source bytes cannot be copied even when destination bytes are writable. -/
        def uninitialized : CIL.Safety.Memory := { memory with
          cells := fun _ offset => ⟨BitVec.ofNat 8 offset, false⟩ }
        /-- A writable view value never creates write authority. -/
        def readOnlyMemory : CIL.Safety.Memory := { memory with views := [⟨0, 0, 32, true, false⟩] }
        /-- Copying preserves exact snapshot bytes, surrounding storage, and failure behavior. -/
        theorem correctness :
        {{string.Join(" \u2227\n", claims)}} := by and_intros <;> rfl
        #print axioms correctness
        end ExampleProof
        """);
    var mode = trying ? "true" : "false";
    File.AppendAllText(proof, BulkCallEvidence(0, 2, $".spanCopy {width} {mode}"));
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS checked span copy: " + name));
}
queue.Flush();

partial class Program
{
    delegate void CopyBytes(ReadOnlySpan<byte> source, Span<byte> destination);
    delegate bool TryCopyBytes(ReadOnlySpan<byte> source, Span<byte> destination);

    static void RuntimeChecks(Type runtime)
    {
        var copy = runtime.GetMethod("CopyReadOnly")!.CreateDelegate<CopyBytes>();
        var tryCopy = runtime.GetMethod("TryCopyReadOnly")!.CreateDelegate<TryCopyBytes>();
        foreach (var (source, destination, length) in new[]
            { (1, 3, 6), (3, 1, 6), (3, 3, 6), (0, 16, 2), (32, 32, 0) })
        {
            var bytes = Enumerable.Range(0, 32).Select(index => (byte)index).ToArray();
            var expected = bytes.ToArray();
            Array.Copy(expected, source, expected, destination, length);
            if (!tryCopy(bytes.AsSpan(source, length), bytes.AsSpan(destination, length)) ||
                !bytes.SequenceEqual(expected)) throw new Exception("Runtime overlap differs");
        }
        var shortBytes = Enumerable.Range(0, 32).Select(index => (byte)index).ToArray();
        var unchanged = shortBytes.ToArray();
        if (tryCopy(shortBytes.AsSpan(2, 5), shortBytes.AsSpan(20, 3)) || !shortBytes.SequenceEqual(unchanged))
            throw new Exception("Short try-copy changed memory");
        try { copy(shortBytes.AsSpan(2, 5), shortBytes.AsSpan(20, 3)); throw new Exception("Short copy accepted"); }
        catch (ArgumentException) { }
        if (!shortBytes.SequenceEqual(unchanged)) throw new Exception("Throwing copy changed memory");
    }
}
