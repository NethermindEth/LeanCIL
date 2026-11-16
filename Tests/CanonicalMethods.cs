#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include StableNames.cs

using System.Security.Cryptography;
using System.Text.Json;

// The methods of the self-admission corpus whose extraction defines them from their decoder, against a checked-in
// list that only grows: a listed method that is no longer defined from its decoder fails, and so does an addition
// until --update records it. Prints, for the methods kept as literals, how many each first refusal keeps. Reads the
// extractions Tests/SelfAdmission.cs ran with the current extractor and the report Tests/Blockers.cs writes for its
// fixture, and checks example methods that must be defined the same way.
const string Usage = "Usage: CanonicalMethods.cs [--update]";
var update = args switch { [] => false, ["--update"] => true, _ => throw new ArgumentException(Usage) };
var listPath = At("Tests/canonical-methods.txt");
var reportPath = At("artifacts/SelfAdmission/blockers.json");
if (!File.Exists(reportPath))
    throw new InvalidOperationException(
        $"Missing {reportPath}; run `dotnet run --file Tests/SelfAdmission.cs` first.");
using var document = JsonDocument.Parse(File.ReadAllText(reportPath));
var root = document.RootElement;
// A report from another extractor describes another emission.
var extractorHash = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(ExtractorPath)));
if (root.GetProperty("extractorSha256").GetString() != extractorHash)
    throw new InvalidOperationException(
        $"{reportPath} was written by another extractor; run Tests/SelfAdmission.cs again.");

var admittedEntries = root.GetProperty("entries").EnumerateArray()
    .Where(entry => entry.GetProperty("status").GetString() == "admitted").ToArray();
// A method extracted by several entries counts once; a generated method counts toward its source method.
var decodedNames = admittedEntries
    .SelectMany(entry => entry.GetProperty("decodedMethods").EnumerateArray().Select(method => method.GetString()!))
    .ToHashSet(StringComparer.Ordinal);
var literals = new Dictionary<string, JsonElement>(StringComparer.Ordinal);
foreach (var refusal in admittedEntries.SelectMany(entry => entry.GetProperty("literalMethods").EnumerateArray()))
    literals.TryAdd(refusal.GetProperty("method").GetString()!, refusal);
// The decision reads only the method's own body and reachability, so no extraction may decide it differently.
var split = decodedNames.Where(literals.ContainsKey).Order(StringComparer.Ordinal).ToArray();
if (split.Length != 0)
    throw new InvalidOperationException("Methods defined from their decoder in one extraction and as a literal in " +
        "another:\n" + string.Join('\n', split));
var decoded = decodedNames.Select(StableNames.Of).Order(StringComparer.Ordinal).ToArray();
var listed = File.Exists(listPath) ? File.ReadAllLines(listPath).Where(line => line.Length != 0).ToArray() : [];
var decodedCounts = StableNames.Counts(decoded);
var listedCounts = StableNames.Counts(listed);
string[] Excess(Dictionary<string, int> counts, Dictionary<string, int> bound) =>
    [.. counts.SelectMany(pair =>
        Enumerable.Repeat(pair.Key, Math.Max(0, pair.Value - bound.GetValueOrDefault(pair.Key))))
        .Order(StringComparer.Ordinal)];
var lost = Excess(listedCounts, decodedCounts);
var added = Excess(decodedCounts, listedCounts);

string Reason(JsonElement refusal) => refusal.GetProperty("refusal").GetString() switch
{
    "hole" => "hole: " + refusal.GetProperty("family").GetString(),
    "translated" => "translated call or construction",
    "unreachablePc" => "unreachable pc",
    var kind => throw new InvalidDataException("Unknown refusal kind: " + kind)
};
string Opcodes(IEnumerable<JsonElement> refusals) => string.Join(", ", refusals
    .GroupBy(refusal => refusal.GetProperty("opcode").GetString()!, StringComparer.Ordinal)
    .OrderByDescending(group => group.Count()).ThenBy(group => group.Key, StringComparer.Ordinal)
    .Select(group => $"{group.Key} {group.Count()}"));
var summary = new List<string>
{
    $"{decoded.Length} of the {decoded.Length + literals.Count} methods extracted for the {admittedEntries.Length} " +
        "admitted entries of the self-admission corpus are defined from their decoder.", "",
    "| First refusal | Methods | Opcodes |", "| --- | ---: | --- |"
};
// Each literal method counts once, under the first pc that keeps its literal.
summary.AddRange(literals.Values.GroupBy(Reason, StringComparer.Ordinal)
    .OrderByDescending(group => group.Count()).ThenBy(group => group.Key, StringComparer.Ordinal)
    .Select(group => $"| {group.Key} | {group.Count()} | {Opcodes(group)} |"));
Console.WriteLine(string.Join('\n', summary));
if (Environment.GetEnvironmentVariable("GITHUB_STEP_SUMMARY") is { Length: > 0 } stepSummary)
    File.AppendAllLines(stepSummary, ["", .. summary]);
foreach (var method in added) Console.WriteLine("  added: " + method);
if (lost.Length != 0)
    throw new InvalidOperationException($"Methods listed in {listPath} are no longer defined from their decoder:\n" +
        string.Join('\n', lost));

// Examples and the blockers fixture whose bodies decode in full must be defined from their decoder: a fallback to a
// literal would leave their proofs passing over a method that no decoder produced.
var requiredDirectory = At("artifacts/CanonicalMethods");
Directory.CreateDirectory(requiredDirectory);
var requiredManifest = Path.Combine(requiredDirectory, "manifest.json");
string[] requiredExamples =
[
    "System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)",
    "System.UInt64 Examples.Arithmetic::Choose(System.Boolean,System.UInt64,System.UInt64)",
    "System.UInt32 Examples.Loops::Countdown(System.UInt32)",
    // Calls decodes through its two direct calls, whose targets are the links of their pcs.
    "System.UInt64 Examples.Arithmetic::Calls(System.UInt64)"
];
// SameText keeps its literal for the string literal it loads first; Mutate, a callee of Calls, decodes through an
// integer indirect load and store.
const string literalExample = "System.Boolean Examples.Strings::SameText()";
const string indirectCallee = "System.Void Examples.Arithmetic::Mutate(System.UInt64&)";
File.WriteAllText(requiredManifest, JsonSerializer.Serialize(new
{
    entries = requiredExamples.Append(literalExample).Select(signature => new { signature, profile = "scalar" })
}));
var examplesReport = Path.Combine(requiredDirectory, "blockers.json");
Run(["dotnet", ExtractorPath, "blockers", At("Examples/Assembly/bin/Examples.dll"), "--manifest", requiredManifest,
    "--output", examplesReport]);
var fixtureReport = At("artifacts/Blockers/blockers.json");
if (!File.Exists(fixtureReport))
    throw new InvalidOperationException($"Missing {fixtureReport}; run Tests/Blockers.cs, which writes it.");
foreach (var (report, signature) in requiredExamples.Append(indirectCallee)
    .Select(signature => (examplesReport, signature))
    .Append((fixtureReport, "System.UInt64 Fixture::Admitted(System.UInt64,System.UInt64)")))
{
    using var required = JsonDocument.Parse(File.ReadAllText(report));
    if (required.RootElement.GetProperty("extractorSha256").GetString() != extractorHash)
        throw new InvalidOperationException($"{report} was written by another extractor.");
    var decodedHere = required.RootElement.GetProperty("entries").EnumerateArray()
        .Where(entry => entry.GetProperty("status").GetString() == "admitted")
        .SelectMany(entry => entry.GetProperty("decodedMethods").EnumerateArray())
        .Select(method => method.GetString()!).ToHashSet(StringComparer.Ordinal);
    if (!decodedHere.Contains(signature))
        throw new InvalidOperationException($"{signature} is not defined from its decoder in {report}.");
}
Console.WriteLine($"PASS {requiredExamples.Length + 2} example and fixture methods are defined from their decoder");
using (var examples = JsonDocument.Parse(File.ReadAllText(examplesReport)))
{
    var refusal = examples.RootElement.GetProperty("entries").EnumerateArray()
        .SelectMany(entry => entry.GetProperty("literalMethods").EnumerateArray())
        .FirstOrDefault(literal => literal.GetProperty("method").GetString() == literalExample);
    var stated = refusal.ValueKind != JsonValueKind.Object ? "no refusal" :
        $"{refusal.GetProperty("ilOffset").GetInt32()} {refusal.GetProperty("opcode").GetString()} " +
        $"{Reason(refusal)}";
    if (stated != "0 ldstr hole: tokens")
        throw new InvalidOperationException($"{literalExample} must keep its literal for the string load at " +
            $"IL_0000, found: {stated}.");
}
Console.WriteLine("PASS the example kept as a literal reports its first hole");
if (update)
{
    File.WriteAllText(listPath, string.Concat(decoded.Select(method => method + "\n")));
    Console.WriteLine($"Recorded {added.Length} additions in {listPath}.");
    return;
}
if (added.Length != 0)
    throw new InvalidOperationException($"{added.Length} methods are newly defined from their decoder. Review " +
        "them, then record them with `dotnet run --file Tests/CanonicalMethods.cs -- --update`.");
Console.WriteLine($"PASS canonical methods: {decoded.Length} defined from their decoder, matching the list");
