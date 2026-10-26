#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/MemorySpans");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution");

foreach (var (name, signature, arguments, expected) in new[]
{
    ("SliceRead", "System.ReadOnlySpan`1<System.Int32>,System.Int32,System.Int32,System.Int32",
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 3, 4, false⟩, .scalar (.i32 1), " +
        ".scalar (.i32 2), .scalar (.i32 0)]", 9),
    ("SliceWrite", "System.Span`1<System.Int32>,System.Int32,System.Int32,System.Int32,System.Int32",
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 3, 4, true⟩, .scalar (.i32 1), " +
        ".scalar (.i32 2), .scalar (.i32 0), .scalar (.i32 11)]", 11),
    ("Existing", "System.Int32&,System.Int32,System.Int32",
        "[.reference (.address ⟨0, 0⟩), .scalar (.i32 3), .scalar (.i32 1)]", 7)
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"MemorySpans::{name}({signature})", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def spanMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨12, 1, []⟩, true, []⟩ else none
          cells := fun _ offset => ⟨if offset == 4 then 7 else 0, true⟩
          views := [⟨0, 0, 12, true, true⟩]
          nextIdentity := 1 }

        theorem compiled_span_result :
            (CIL.Safety.invoke Extracted.program 64 0 {{arguments}} spanMemory).map Prod.snd =
              .ok [.scalar (.i32 {{expected}})] := rfl
        #print axioms compiled_span_result
        """);
    evidence.Add(proof, "PASS compiled span certificate and execution: " + name);
}

var original = File.ReadAllText(Path.Combine(root, "SliceRead", "Extracted.lean"));
var argumentStart = original.IndexOf("def method0RawArguments :", StringComparison.Ordinal);
if (argumentStart < 0) throw new Exception("Missing span argument evidence");
var argumentEnd = original.IndexOf('\n', argumentStart);
var argumentDefinition = original[argumentStart..argumentEnd];
foreach (var (name, before, after) in new[]
{
    ("element-width", ".span 4 false", ".span 8 false"),
    ("write-authority", ".span 4 false", ".span 4 true")
})
{
    if (!argumentDefinition.Contains(before, StringComparison.Ordinal))
        throw new Exception("Missing span argument mutation: " + name);
    var proof = Path.Combine(root, "Forged-" + name + ".lean");
    // Keep both raw methods intact: rejection must bind argument evidence to the closed signature.
    File.WriteAllText(proof, original[..argumentStart] +
        argumentDefinition.Replace(before, after, StringComparison.Ordinal) + original[argumentEnd..]);
    var result = Execute(["lake", "env", "lean", proof], cwd: FixturePackage());
    var rejectedGoal = "⊢ Extraction.closedArguments rawLayouts method0Closed = some method0RawArguments";
    if (result.Code == 0 || !result.Output.Contains(rejectedGoal, StringComparison.Ordinal))
        throw new Exception("Incorrect span evidence rejection: " + name + "\n" + result.Output);
    Console.WriteLine("PASS independent span evidence rejection: " + name);
}

RequireLeanFixtures("CIL.Safety.MethodContract", "CIL.Safety.BufferContents");
foreach (var (method, proof) in new[]
{
    ("SliceRead", "Tests/MemorySpanContracts.lean"),
    ("SliceWrite", "Tests/MemorySpanWriteContracts.lean")
})
{
    var contractOutput = Path.Combine(root, method);
    Run(["lake", "env", "lean", "-o", Path.Combine(contractOutput, "Extracted.olean"),
        Path.Combine(contractOutput, "Extracted.lean")], cwd: FixturePackage());
    var contracts = Run(["lake", "env", "lean", At(proof)], cwd: FixturePackage(), leanPath: contractOutput);
    if (contracts.Contains("sorryAx", StringComparison.Ordinal)) throw new Exception("Untrusted span contract");
}
Console.WriteLine("PASS compiled span helper contract and caller composition");

foreach (var (signature, marker) in new[]
{
    ("ByRefSpan(System.Span`1<System.Int32>&)", "Unsupported by-reference span"),
    ("FloatingSpan(System.ReadOnlySpan`1<System.Double>)", "Unsupported type")
})
{
    var result = Execute(["dotnet", ExtractorPath, "extract", assembly, "MemorySpans::" + signature,
        Path.Combine(root, "Rejected-" + signature.Split('(')[0])]);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect unsupported span signature rejection: " + signature + "\n" + result.Output);
    Console.WriteLine("PASS unsupported span signature: " + signature);
}

evidence.Check(replay: false);
