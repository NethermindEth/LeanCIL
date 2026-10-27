#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs

using System.Text.RegularExpressions;

var output = At("artifacts/LayoutEvidence");
Directory.CreateDirectory(output);
var rejected = new RejectedEvidence(output);
var evidence = new GeneratedEvidence(output, args.Contains("--measure", StringComparer.Ordinal));
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution");
RequireLeanFixtures("Tests.ExtractionLayout");
var samples = new[]
{
    "Sequential::ReadWrite(Examples.Record&,uint)",
    "Nested::Extract(Examples.NestedRecord)",
    "Nested::Snapshot(ulong)",
    "Nested::Sized(ulong)",
    "Constructors::Return(ulong)",
    "UnsafeLayouts::Size15()",
    "UnsafeLayouts::Add15int(Examples.NestedRecord&,int)"
};
ExtractBatch("extract", "Examples", samples.Select((selector, index) =>
    new GeneratedExtraction(At("Examples/Assembly/bin/Examples.dll"), selector, Path.Combine(output, index.ToString()))));
foreach (var (selector, index) in samples.Select((selector, index) => (selector, index)))
{
    var folder = Path.Combine(output, index.ToString());
    evidence.Add(Path.Combine(folder, "Extracted.lean"), "PASS checked extraction: " + selector);
}

evidence.Check();
var baseline = File.ReadAllText(Path.Combine(output, "0", "Extracted.lean"));
void Reject(string name, string mutated)
{
    if (mutated == baseline) throw new InvalidOperationException("Mutation did not change generated source: " + name);
    var path = Path.Combine(output, name + ".lean");
    File.WriteAllText(path, mutated);
    rejected.Add(path, "PASS layout evidence rejects " + name, "decide");
}

// Change lookup lemmas and instructions together: lookup rfl lemmas still hold.
Reject("field-offset", Regex.Replace(baseline, @"\.fieldAt 4 4", ".fieldAt 3 4"));
// Offset 3 remains within the 8-byte aggregate, so old bounds-only validation passes.
Reject("computed-offset", baseline.Replace("⟨4, 4, false⟩", "⟨3, 4, false⟩"));
Reject("packing", baseline.Replace("packing := -1", "packing := 3").Replace("packing := 0", "packing := 3"));
Reject("omitted-layout-uses", Regex.Replace(baseline, @"def method0LayoutUses : List Extraction.LayoutUse := [^\r\n]*", "def method0LayoutUses : List Extraction.LayoutUse := []"));
rejected.Check();
Console.WriteLine("PASS raw sequential/nested layout recomputation and output binding");
