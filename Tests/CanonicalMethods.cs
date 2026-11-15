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
// until --update records it. Reads the extractions Tests/SelfAdmission.cs ran with the current extractor and the
// report Tests/Blockers.cs writes for its fixture, and checks example methods that must be defined the same way.
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

var entries = root.GetProperty("entries").EnumerateArray().ToArray();
// A method extracted by several entries counts once; a generated method counts toward its source method.
var decoded = entries.Where(entry => entry.GetProperty("status").GetString() == "admitted")
    .SelectMany(entry => entry.GetProperty("decodedMethods").EnumerateArray().Select(method => method.GetString()!))
    .Distinct(StringComparer.Ordinal).Select(StableNames.Of).Order(StringComparer.Ordinal).ToArray();
var listed = File.Exists(listPath) ? File.ReadAllLines(listPath).Where(line => line.Length != 0).ToArray() : [];
var decodedCounts = StableNames.Counts(decoded);
var listedCounts = StableNames.Counts(listed);
string[] Excess(Dictionary<string, int> counts, Dictionary<string, int> bound) =>
    [.. counts.SelectMany(pair =>
        Enumerable.Repeat(pair.Key, Math.Max(0, pair.Value - bound.GetValueOrDefault(pair.Key))))
        .Order(StringComparer.Ordinal)];
var lost = Excess(listedCounts, decodedCounts);
var added = Excess(decodedCounts, listedCounts);

Console.WriteLine($"{decoded.Length} of the {entries.Length} methods of the self-admission corpus are defined " +
    "from their decoder.");
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
    "System.UInt32 Examples.Loops::Countdown(System.UInt32)"
];
File.WriteAllText(requiredManifest, JsonSerializer.Serialize(new
{
    entries = requiredExamples.Select(signature => new { signature, profile = "scalar" })
}));
var examplesReport = Path.Combine(requiredDirectory, "blockers.json");
Run(["dotnet", ExtractorPath, "blockers", At("Examples/Assembly/bin/Examples.dll"), "--manifest", requiredManifest,
    "--output", examplesReport]);
var fixtureReport = At("artifacts/Blockers/blockers.json");
if (!File.Exists(fixtureReport))
    throw new InvalidOperationException($"Missing {fixtureReport}; run Tests/Blockers.cs, which writes it.");
foreach (var (report, signature) in requiredExamples.Select(signature => (examplesReport, signature))
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
Console.WriteLine($"PASS {requiredExamples.Length + 1} example and fixture methods are defined from their decoder");
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
