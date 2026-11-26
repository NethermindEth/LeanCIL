#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
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
var snapshot = File.ReadAllText(Path.Combine(output, "2", "Extracted.lean"));
void Reject(string name, string source, string mutated, string marker = "decide")
{
    if (mutated == source)
        throw new InvalidOperationException($"""Mutation did not change generated source: {name}""");
    var path = Path.Combine(output, $"""{name}.lean""");
    File.WriteAllText(path, mutated);
    rejected.Add(path, $"""PASS layout evidence rejects {name}""", marker);
}

// A field operand naming another field of the struct no longer matches the decoded body.
Reject("field-index", baseline, baseline.Replace("index := 1, type := .primitive", "index := 0, type := .primitive"),
    "the decoded method has no field operand");
// Offset 3 remains within the 8-byte aggregate, so old bounds-only validation passes.
Reject("computed-offset", baseline, baseline.Replace("⟨4, 4, false⟩", "⟨3, 4, false⟩"));
Reject("packing", baseline,
    baseline.Replace("packing := -1", "packing := 3").Replace("packing := 0", "packing := 3"));
// A struct field access reads its layout from the checked environment, so the omitted uses are a local's.
Reject("omitted-layout-uses", snapshot,
    LayoutUsesDefinition.Replace(snapshot, "def method0LayoutUses : List Extraction.LayoutUse := []"));
rejected.Check();
Console.WriteLine("PASS raw sequential/nested layout recomputation and output binding");

partial class Program
{
    [GeneratedRegex(@"def method0LayoutUses : List Extraction.LayoutUse := [^\r\n]*")]
    internal static partial Regex LayoutUsesDefinition { get; }
}
