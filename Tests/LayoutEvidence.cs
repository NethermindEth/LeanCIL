#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include GeneratedEvidence.cs

using System.Text.RegularExpressions;

var output = At("artifacts/LayoutEvidence");
Directory.CreateDirectory(output);
var evidence = new GeneratedEvidence(output, args.Contains("--measure", StringComparer.Ordinal));
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution"]);
Run(["lake", "env", "lean", "Tests/ExtractionLayout.lean"]);
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
foreach (var (selector, index) in samples.Select((selector, index) => (selector, index)))
{
    var folder = Path.Combine(output, index.ToString());
    Run(Extract("extract", At("Examples/Assembly/bin/Examples.dll"), "Examples", selector, folder));
    evidence.Add(Path.Combine(folder, "Extracted.lean"), "PASS checked extraction: " + selector);
}

evidence.Check();
var baseline = File.ReadAllText(Path.Combine(output, "0", "Extracted.lean"));
void Reject(string name, string mutated)
{
    if (mutated == baseline) throw new InvalidOperationException("Mutation did not change generated source: " + name);
    var path = Path.Combine(output, name + ".lean");
    File.WriteAllText(path, mutated);
    var result = Execute(["lake", "env", "lean", path]);
    if (result.Code == 0 || !result.Output.Contains("decide"))
        throw new InvalidOperationException("Malformed extraction evidence was not rejected by its validator: " + name + "\n" + result.Output);
    Console.WriteLine("PASS layout evidence rejects " + name);
}

// Change lookup lemmas and instructions together: lookup rfl lemmas still hold.
Reject("field-offset", Regex.Replace(baseline, @"\.fieldAt 4 4", ".fieldAt 3 4"));
// Offset 3 remains within the 8-byte aggregate, so old bounds-only validation passes.
Reject("computed-offset", baseline.Replace("⟨4, 4, false⟩", "⟨3, 4, false⟩"));
Reject("packing", baseline.Replace("packing := -1", "packing := 3").Replace("packing := 0", "packing := 3"));
Reject("omitted-layout-uses", Regex.Replace(baseline, @"def method0LayoutUses : List Extraction.LayoutUse := [^\r\n]*", "def method0LayoutUses : List Extraction.LayoutUse := []"));
Console.WriteLine("PASS raw sequential/nested layout recomputation and output binding");
