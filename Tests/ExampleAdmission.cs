#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include StableNames.cs

using System.Security.Cryptography;
using System.Text.Json;

// The methods extracted for the admitted entries of the examples assembly under each CI profile, against a
// checked-in baseline: a baseline method no longer extracted fails, and so does an addition until --update
// records it, so a change that stops admitting an example fails even when no proof of it runs.
const string Usage = "Usage: ExampleAdmission.cs [--update]";
const string UpdateCommand = "dotnet run --file Tests/ExampleAdmission.cs -- --update";
var update = args switch { [] => false, ["--update"] => true, _ => throw new ArgumentException(Usage) };
// A report from another extractor describes another extraction.
string ExtractorHash() => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(ExtractorPath)));
var extractorHash = ExtractorHash();

// The methods extracted for an admission report's admitted entries; one extracted by several entries counts once.
HashSet<string> Extracted(string path, JsonElement report)
{
    if (report.GetProperty("extractorSha256").GetString() != extractorHash)
        throw new InvalidOperationException($"{path} was written by another extractor.");
    return report.GetProperty("entries").EnumerateArray()
        .Where(entry => entry.GetProperty("status").GetString() == "admitted")
        .SelectMany(entry => entry.GetProperty("decodedMethods").EnumerateArray())
        .Select(method => method.GetString()!).ToHashSet(StringComparer.Ordinal);
}
string[] Excess(Dictionary<string, int> counts, Dictionary<string, int> bound) =>
    [.. counts.SelectMany(pair =>
        Enumerable.Repeat(pair.Key, Math.Max(0, pair.Value - bound.GetValueOrDefault(pair.Key))))
        .Order(StringComparer.Ordinal)];

var baselinePath = At("Tests/ExampleAdmissionBaseline.txt");
var examplesAssembly = At("Examples/Assembly/bin/Examples.dll");
string[] profiles = ["scalar", "x64-sse42", "x64-v3", "x64-v4", "arm64-advsimd"];
var examplesDirectory = At("artifacts/ExampleAdmission");
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
// The runs only read the built extractor, so they run at once; one rebuilt meanwhile would mix two extractions.
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

string[] everyProfile =
[
    "System.Void Examples.Arithmetic::Mutate(System.UInt64&)",
    "System.Int32 Examples.Capabilities::Endian()",
    "System.ReadOnlySpan`1<System.Byte> Examples.StaticSpans::get_Lookup()",
    "System.ReadOnlySpan`1<System.UInt32> Examples.SpanTables::get_Words()",
    "System.ReadOnlySpan`1<System.UInt64> Examples.SpanTables::get_Powers()"
];
const string avx2And = "System.UInt64 Examples.DivisionIntrinsics::And(System.UInt64,System.UInt64)";
var extracted = new List<string>();
foreach (var (profile, path) in reports)
{
    using var report = JsonDocument.Parse(File.ReadAllText(path));
    var names = Extracted(path, report.RootElement);
    // A generated method counts toward its source method.
    extracted.AddRange(names.Select(name => profile + " " + StableNames.Of(name)));
    Console.WriteLine($"{profile}: {names.Count} methods extracted for the admitted entries among the " +
        $"{methods.Length} methods of the examples assembly.");
    foreach (var example in everyProfile)
        if (!names.Contains(example))
            throw new InvalidOperationException($"{example} is not extracted in {path}.");
    if (profile == "x64-v3" && !names.Contains(avx2And))
        throw new InvalidOperationException($"{avx2And} must be extracted under {profile} in {path}.");
}
Console.WriteLine("PASS field sites and Mutate are extracted under every profile and Avx2.And under x64-v3");
var current = extracted.Order(StringComparer.Ordinal).ToArray();
var baseline = File.Exists(baselinePath) ? File.ReadAllLines(baselinePath).Where(line => line.Length != 0) : [];
var currentCounts = StableNames.Counts(current);
var baselineCounts = StableNames.Counts(baseline);
var presentByProfile = StableNames.Counts(profiles.SelectMany(profile =>
    methods.Select(method => profile + " " + StableNames.Of(method))));
var missing = Excess(baselineCounts, currentCounts);
// Only fail on methods that still exist in Examples.dll and regressed; removed methods and gains are reported.
var lost = missing.Where(entry => presentByProfile.ContainsKey(entry)).ToArray();
var removed = missing.Where(entry => !presentByProfile.ContainsKey(entry)).ToArray();
var added = Excess(currentCounts, baselineCounts);
foreach (var method in added) Console.WriteLine("  added: " + method);
if (lost.Length != 0)
    throw new InvalidOperationException($"Methods listed in {baselinePath} are no longer extracted:\n" +
        string.Join('\n', lost));
if (update)
{
    File.WriteAllText(baselinePath, string.Concat(current.Select(method => method + "\n")));
    Console.WriteLine($"Recorded {added.Length} additions and {removed.Length} removals in {baselinePath}.");
    return;
}
if (added.Length != 0 || removed.Length != 0)
    Console.WriteLine($"NOTE {baselinePath}: {added.Length} newly extracted and {removed.Length} removed methods " +
        $"(refresh with `{UpdateCommand}`).");
Console.WriteLine($"PASS example admission: {current.Length} methods extracted across the profiles with no regressions");
