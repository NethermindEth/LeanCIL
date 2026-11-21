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

// The methods of the self-admission corpus, and of the examples assembly under each CI profile, whose extraction
// defines them from their decoder, against checked-in lists that only grow: a listed method that is no longer
// extracted fails, and so does an addition until --update records it. Reads the extractions Tests/SelfAdmission.cs
// ran with the current extractor and the report Tests/Blockers.cs writes for its fixture, and runs the examples'
// admission itself.
const string Usage = "Usage: CanonicalMethods.cs [--update]";
const string UpdateCommand = "dotnet run --file Tests/CanonicalMethods.cs -- --update";
var update = args switch { [] => false, ["--update"] => true, _ => throw new ArgumentException(Usage) };
var listPath = At("Tests/canonical-methods.txt");
var reportPath = At("artifacts/SelfAdmission/blockers.json");
if (!File.Exists(reportPath))
    throw new InvalidOperationException(
        $"Missing {reportPath}; run `dotnet run --file Tests/SelfAdmission.cs` first.");
using var document = JsonDocument.Parse(File.ReadAllText(reportPath));
var root = document.RootElement;
// A report from another extractor describes another emission.
string ExtractorHash() => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(ExtractorPath)));
var extractorHash = ExtractorHash();
if (root.GetProperty("extractorSha256").GetString() != extractorHash)
    throw new InvalidOperationException(
        $"{reportPath} was written by another extractor; run Tests/SelfAdmission.cs again.");

// The methods an admission report defines from their decoder, and its admitted entries.
(HashSet<string> Decoded, int Admitted) Read(string path, JsonElement report)
{
    if (report.GetProperty("extractorSha256").GetString() != extractorHash)
        throw new InvalidOperationException($"{path} was written by another extractor.");
    var admitted = report.GetProperty("entries").EnumerateArray()
        .Where(entry => entry.GetProperty("status").GetString() == "admitted").ToArray();
    // A method extracted by several entries counts once.
    var names = admitted
        .SelectMany(entry => entry.GetProperty("decodedMethods").EnumerateArray())
        .Select(method => method.GetString()!).ToHashSet(StringComparer.Ordinal);
    return (names, admitted.Length);
}
string[] Excess(Dictionary<string, int> counts, Dictionary<string, int> bound) =>
    [.. counts.SelectMany(pair =>
        Enumerable.Repeat(pair.Key, Math.Max(0, pair.Value - bound.GetValueOrDefault(pair.Key))))
        .Order(StringComparer.Ordinal)];
// What a checked-in list names that is no longer decoded, and what is decoded that it does not yet name.
(string[] Lost, string[] Added) Compare(string path, string[] names)
{
    var listed = File.Exists(path) ? File.ReadAllLines(path).Where(line => line.Length != 0).ToArray() : [];
    var nameCounts = StableNames.Counts(names);
    var listedCounts = StableNames.Counts(listed);
    return (Excess(listedCounts, nameCounts), Excess(nameCounts, listedCounts));
}

var (decodedNames, admittedCount) = Read(reportPath, root);
// A generated method counts toward its source method.
var decoded = decodedNames.Select(StableNames.Of).Order(StringComparer.Ordinal).ToArray();
var (lost, added) = Compare(listPath, decoded);

Console.WriteLine($"{decoded.Length} methods extracted for the {admittedCount} admitted entries of the " +
    "self-admission corpus, each defined from its decoder.");
foreach (var method in added) Console.WriteLine("  added: " + method);
if (lost.Length != 0)
    throw new InvalidOperationException($"Methods listed in {listPath} are no longer extracted:\n" +
        string.Join('\n', lost));

// Every method of the examples assembly under each admitted profile, so a change that stops defining an example
// from its decoder fails even when no proof of it runs.
var examplesListPath = At("Tests/canonical-examples.txt");
var examplesAssembly = At("Examples/Assembly/bin/Examples.dll");
string[] profiles = ["scalar", "x64-sse42", "x64-v3", "x64-v4", "arm64-advsimd"];
var examplesDirectory = At("artifacts/CanonicalMethods");
Directory.CreateDirectory(examplesDirectory);
var listing = Run(["dotnet", ExtractorPath, "list", examplesAssembly]).Split('\n')
    .Select(line => line.Trim()).ToArray();
var header = listing.FirstOrDefault(line => line.StartsWith("Methods in ", StringComparison.Ordinal)) ??
    throw new InvalidDataException("leancil list printed no method count for " + examplesAssembly);
var listedCount = int.Parse(header[(header.LastIndexOf('(') + 1)..header.LastIndexOf(')')],
    System.Globalization.CultureInfo.InvariantCulture);
var methods = listing.Where(line => line.Contains("::", StringComparison.Ordinal)).ToArray();
if (methods.Length != listedCount)
    throw new InvalidDataException($"leancil list counted {listedCount} methods of {examplesAssembly} but printed " +
        $"{methods.Length}.");
// The runs only read the built extractor, so they run at once; one rebuilt meanwhile would mix two emissions.
var reports = await Task.WhenAll(profiles.Select(profile => Task.Run(() =>
{
    var manifest = Path.Combine(examplesDirectory, profile + "-manifest.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        entries = methods.Select(signature => new { signature, profile })
    }));
    var output = Path.Combine(examplesDirectory, profile + "-blockers.json");
    Run(["dotnet", ExtractorPath, "blockers", examplesAssembly, "--manifest", manifest, "--output", output]);
    return (Profile: profile, Path: output);
})));
if (ExtractorHash() != extractorHash)
    throw new InvalidOperationException("The extractor changed while the examples' admission ran.");

string[] decodedExamples =
[
    "System.Void Examples.Arithmetic::Mutate(System.UInt64&)",
    "System.Int32 Examples.Capabilities::Endian()",
    "System.ReadOnlySpan`1<System.Byte> Examples.StaticSpans::get_Lookup()",
    "System.ReadOnlySpan`1<System.UInt32> Examples.SpanTables::get_Words()",
    "System.ReadOnlySpan`1<System.UInt64> Examples.SpanTables::get_Powers()"
];
const string avx2And = "System.UInt64 Examples.DivisionIntrinsics::And(System.UInt64,System.UInt64)";
var examplesDecoded = new List<string>();
foreach (var (profile, path) in reports)
{
    using var report = JsonDocument.Parse(File.ReadAllText(path));
    var (names, _) = Read(path, report.RootElement);
    examplesDecoded.AddRange(names.Select(name => profile + " " + StableNames.Of(name)));
    Console.WriteLine($"{profile}: {names.Count} methods extracted for the {methods.Length} methods of the examples " +
        "assembly, each defined from its decoder.");
    foreach (var example in decodedExamples)
        if (!names.Contains(example))
            throw new InvalidOperationException($"{example} is not defined from its decoder in {path}.");
    if (profile == "x64-v3" && !names.Contains(avx2And))
        throw new InvalidOperationException($"{avx2And} must decode under {profile} in {path}.");
}
Console.WriteLine("PASS field sites and Mutate decode across profiles and Avx2.And decodes under x64-v3");
var examples = examplesDecoded.Order(StringComparer.Ordinal).ToArray();
var (examplesLost, examplesAdded) = Compare(examplesListPath, examples);
foreach (var method in examplesAdded) Console.WriteLine("  added: " + method);
if (examplesLost.Length != 0)
    throw new InvalidOperationException($"Methods listed in {examplesListPath} are no longer extracted:\n" +
        string.Join('\n', examplesLost));

// The blockers fixture's admitted method is extracted, so its proof runs over the method its decoder produced.
var fixtureReport = At("artifacts/Blockers/blockers.json");
if (!File.Exists(fixtureReport))
    throw new InvalidOperationException($"Missing {fixtureReport}; run Tests/Blockers.cs, which writes it.");
using (var fixture = JsonDocument.Parse(File.ReadAllText(fixtureReport)))
{
    const string admittedFixture = "System.UInt64 Fixture::Admitted(System.UInt64,System.UInt64)";
    if (!Read(fixtureReport, fixture.RootElement).Decoded.Contains(admittedFixture))
        throw new InvalidOperationException($"{admittedFixture} is not defined from its decoder in {fixtureReport}.");
}
Console.WriteLine("PASS the blockers fixture's admitted method is defined from its decoder");
if (update)
{
    File.WriteAllText(listPath, string.Concat(decoded.Select(method => method + "\n")));
    File.WriteAllText(examplesListPath, string.Concat(examples.Select(method => method + "\n")));
    Console.WriteLine($"Recorded {added.Length} additions in {listPath} and {examplesAdded.Length} in " +
        $"{examplesListPath}.");
    return;
}
if (added.Length + examplesAdded.Length != 0)
    throw new InvalidOperationException($"{added.Length} self-admitted and {examplesAdded.Length} example methods " +
        $"are newly defined from their decoder. Review them, then record them in {listPath} and {examplesListPath} " +
        $"with `{UpdateCommand}`.");
Console.WriteLine($"PASS canonical methods: {decoded.Length} self-admitted and {examples.Length} example methods " +
    "defined from their decoder, matching the lists");
