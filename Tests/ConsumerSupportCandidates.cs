#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

var root = Path.Combine(Path.GetTempPath(), "leancil-support-candidates-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
try
{
    string Source(string module, string contents)
    {
        var path = Path.Combine(root, module + ".lean");
        File.WriteAllText(path, contents);
        return path;
    }
    Source("Early", "/- import Extracted /- nested -/ -/\ntheorem early : True := True.intro\n");
    Source("Late", "theorem late : True := True.intro\n");
    Source("Dependent", "import Extracted\n");
    Source("Indirect", "public meta import Dependent\n");
    Source("Unknown", "import Missing\n");
    Source("Symbols", "import ExtractedSymbols\n");
    Source("Published", "import ImportedInterface\n");
    var first = Source("FirstProof", "import Early\nimport Indirect\nimport Unknown\n");
    var second = Source("SecondProof", "public import all Early /- nested /- comment -/ -/ import Late -- comment\n" +
        "import Symbols\nimport Published\n");
    foreach (var proofs in new[] { new[] { first, second }, new[] { second, first } })
    {
        var modules = ConsumerSupportCandidates(proofs, [root], ["ImportedInterface"], Path.Combine(root, "Toolchain"));
        if (!modules.SequenceEqual(new[] { "Early", "Late" }))
            throw new Exception("Unexpected candidate union: " + string.Join(',', modules));
    }
    Console.WriteLine("PASS candidate union is order independent and excludes transitive generated imports");
}
finally { Directory.Delete(root, true); }

foreach (var reverse in new[] { false, true })
{
    var edges = new Dictionary<string, string[]>(StringComparer.Ordinal)
    {
        ["Leaf"] = ["Middle", "Middle"], ["Middle"] = ["Root"], ["CycleA"] = ["CycleB", "Root"],
        ["CycleB"] = ["CycleA"], ["MissingUser"] = ["Missing"], ["Independent"] = [],
        ["CaseSensitive"] = ["root"]
    };
    var graph = (reverse ? edges.Reverse() : edges).ToDictionary(StringComparer.Ordinal);
    if (!DependentModules(graph, ["Root", "Missing"]).SetEquals(
        ["Root", "Missing", "Leaf", "Middle", "CycleA", "CycleB", "MissingUser"]))
        throw new Exception("Incorrect dependent closure for cycles, missing roots or duplicate edges");
    if (DependentModules(graph, []).Count != 0)
        throw new Exception("An unseeded cycle must not invalidate itself");
}
var chain = Enumerable.Range(0, 4096).Reverse().ToDictionary(index => "M" + index,
    index => index == 0 ? Array.Empty<string>() : ["M" + (index - 1)], StringComparer.Ordinal);
if (DependentModules(chain, ["M0"]).Count != chain.Count)
    throw new Exception("Reverse-ordered dependency chain lost an importer");
Console.WriteLine("PASS linear dependency closure covers ordering, cycles, missing roots and deep chains");
using var verification = new Program();
// Missing toolchain imports are tested without depending on an installed Lean toolchain.
verification.resolvedToolchain = Path.Combine(root, "UnusedToolchain");
var sources = new Dictionary<string, string>(StringComparer.Ordinal)
{
    ["source"] = "current", [ExtractedSourceKey] = "program"
};
ConsumerSupportModule Module(string[] imports, bool bound = false, bool changed = false) => new(
    new SortedDictionary<string, string>(StringComparer.Ordinal)
    {
        [bound ? ExtractedSourceKey : "source"] = bound ? "program" : changed ? "old" : "current"
    }, imports, []);
var record = new SortedDictionary<string, ConsumerSupportModule>(StringComparer.Ordinal)
{
    ["MissingUser"] = Module(["Missing"]), ["MissingDependent"] = Module(["MissingUser"]),
    ["Changed"] = Module([], changed: true), ["ChangedDependent"] = Module(["Changed"]),
    ["Bound"] = Module(["Extracted"], bound: true), ["Unbound"] = Module(["Extracted"]),
    ["Certified"] = Module(["CIL.Safety.Execution"]), ["Independent"] = Module([]),
    ["CycleA"] = Module(["CycleB"]), ["CycleB"] = Module(["CycleA"])
};
if (!verification.RestorableConsumerSupport(record, sources).SetEquals(
    ["Bound", "Certified", "Independent", "CycleA", "CycleB"]))
    throw new Exception("Support closure changed source bindings or external-module exemptions");
Console.WriteLine("PASS support invalidation preserves certified imports and extraction source bindings");
var componentSource = "import CIL\nnamespace Extracted\n" +
    "def method0Signature : String := \"zero\"\ndef zero := 0\ndef aliasZero := zero\n" +
    "def method1Signature : String := \"one\"\ndef one := 1\n" +
    "def method2Signature : String := \"one zero aliasZero one Unknown\"\n" +
    "-- one zero method3Signature\ndef two := zero\n" +
    "def method3Signature : String := \"three\"\ndef three := 3\n" +
    "def specializedMethods : List Nat := []\nend Extracted\n";
var components = SplitExtractionComponents(componentSource);
var componentNames = components.Sources.Keys.ToArray();
var expectedImports = new[] { new[] { 0 }, new[] { 0 }, new[] { 0, 1, 2 }, new[] { 0 } };
for (var methodIndex = 0; methodIndex < expectedImports.Length; methodIndex++)
{
    var actual = components.Sources[componentNames[methodIndex + 1]].Split('\n')
        .Where(line => line.StartsWith("import ", StringComparison.Ordinal));
    var expected = expectedImports[methodIndex].Select(index => "import " + componentNames[index]);
    if (!actual.SequenceEqual(expected))
        throw new Exception("Component imports lost declaration order, deduplication or conservative text dependencies");
}
Console.WriteLine("PASS component imports preserve order, literal dependencies and prior declarations only");
