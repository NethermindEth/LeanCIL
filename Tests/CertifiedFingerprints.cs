#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

using System.Text.Json;
using System.Text.RegularExpressions;

if (args is ["--worker", var specification, var output])
{
    var job = JsonSerializer.Deserialize<FingerprintBaseJob>(File.ReadAllText(specification))!;
    Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", job.Library);
    Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY_SHA256", job.Digest);
    using var worker = new Program();
    var session = worker.Library(Inputs(At("CIL.lean")));
    if (job.WithoutMetadata) worker.certifiedFingerprintsSha = null;
    if (job.Toolchain is not null) worker.resolvedToolchain = job.Toolchain;
    if (job.ChangeMetadata) File.AppendAllText(Path.Combine(worker.library!, CertifiedFingerprintsName), "\n");
    // The producer can be a file-based app while the receiver is the packaged CLI.
    worker.verificationPolicy = "different-receiver-policy";
    var result = worker.PortableConsumerModuleParts(session, job.Modules);
    File.WriteAllText(output, JsonSerializer.Serialize(result));
    return;
}

if (args is not ([] or ["--measure"])) throw new ArgumentException("Expected --measure or no arguments.");
var measure = args.Length != 0;
var directory = At("artifacts/CertifiedFingerprints-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(directory);
Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
var prepared = Path.Combine(directory, "Prepared");
string digest;
using (var producer = new Program())
{
    producer.PrepareCertifiedFingerprints();
    digest = producer.PrepareLibrary(prepared);
    if (!measure)
    {
        File.AppendAllText(Path.Combine(producer.library!, CertifiedFingerprintsName), "\n");
        try
        {
            producer.PrepareLibrary(Path.Combine(directory, "RejectedPublication"));
            throw new Exception("Changed fingerprint metadata was published.");
        }
        catch (InvalidDataException error) when (error.Message.Contains("metadata changed while publishing",
                   StringComparison.Ordinal)) { }
    }
}
var compiled = Path.Combine(prepared, ".lake/build/lib/lean");
var paths = measure ? Directory.EnumerateFiles(compiled, "*.olean", SearchOption.AllDirectories)
    : new[] { Path.Combine(compiled, "CIL.olean"), Path.Combine(compiled, "CIL/Interface/Closure.olean") };
var modules = paths
    .ToDictionary(path => ModuleName(Path.GetRelativePath(compiled, path).Replace('\\', '/')), path => path,
        StringComparer.Ordinal);
var baseCount = modules.Count;
var fixture = Path.Combine(directory, "FingerprintFixture.lean");
File.WriteAllText(fixture, """
    module
    public import Lean
    public def fingerprintText : String := "consumer contents"
    public theorem fingerprintText_eq : fingerprintText = fingerprintText := rfl
    #print axioms fingerprintText_eq
    """);
Run(["lean", "--root=" + directory, "-o", Path.ChangeExtension(fixture, ".olean"), fixture]);
modules.Add("FingerprintFixture", Path.ChangeExtension(fixture, ".olean"));
var measurements = new List<object>();
var workerAssembly = typeof(Program).Assembly.Location;
Dictionary<string, SortedDictionary<string, string>> Invoke(string name, int serialized,
    bool withoutMetadata = false, string? toolchain = null, bool changeMetadata = false)
{
    var specification = Path.Combine(directory, name + ".job.json");
    var output = Path.Combine(directory, name + ".result.json");
    var trace = Path.Combine(directory, name + ".trace");
    File.WriteAllText(specification, JsonSerializer.Serialize(new FingerprintBaseJob(
        prepared, digest, modules, withoutMetadata, toolchain, changeMetadata)));
    var timer = System.Diagnostics.Stopwatch.StartNew();
    var result = Execute(["dotnet", workerAssembly, "--worker", specification, output],
        environment: new Dictionary<string, string> { ["LEANCIL_TRACE_DIRECTORY"] = trace });
    File.WriteAllText(Path.Combine(directory, name + ".log"), result.Output);
    if (changeMetadata)
    {
        if (result.Code == 0 || !result.Output.Contains("fingerprint metadata changed", StringComparison.Ordinal))
            throw new InvalidOperationException("Changed private fingerprint metadata was accepted.");
        return [];
    }
    if (result.Code != 0) throw new InvalidOperationException(name + " failed: " + result.Output);
    var count = Regex.Match(result.Output, @"canonical module fingerprints \((\d+) reused, (\d+) serialized\)");
    if (!count.Success || int.Parse(count.Groups[2].Value) != serialized)
        throw new InvalidOperationException(name + " serialized an unexpected module count: " + result.Output);
    var stages = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
    var fingerprintStage = stages.Single(stage => stage.GetProperty("stage").GetString() ==
        "Canonical module fingerprints");
    measurements.Add(new
    {
        name, wallSeconds = timer.Elapsed.TotalSeconds, reused = int.Parse(count.Groups[1].Value), serialized,
        fingerprintSeconds = fingerprintStage.GetProperty("durationSeconds").GetDouble()
    });
    Console.WriteLine($"PASS {name}: {count.Value}");
    return JsonSerializer.Deserialize<Dictionary<string, SortedDictionary<string, string>>>(
        File.ReadAllText(output))!;
}
void Equal(Dictionary<string, SortedDictionary<string, string>> expected,
    Dictionary<string, SortedDictionary<string, string>> actual)
{
    if (expected.Count != actual.Count || expected.Any(pair =>
            !actual.TryGetValue(pair.Key, out var parts) || !Same(pair.Value, parts)))
        throw new InvalidOperationException("Certified base reuse changed canonical fingerprints.");
}
var initial = Invoke("baseline", modules.Count, withoutMetadata: true);
Equal(initial, Invoke("prepared", 1));
Equal(initial, Invoke("prepared-another-process", 1));
if (measure)
{
    Equal(initial, Invoke("baseline-second", modules.Count, withoutMetadata: true));
    Equal(initial, Invoke("prepared-third", 1));
}
else
{
    var fixtureModule = modules["FingerprintFixture"];
    modules.Remove("FingerprintFixture");
    Equal(initial.Where(pair => pair.Key != "FingerprintFixture").ToDictionary(StringComparer.Ordinal),
        Invoke("all-certified", 0));
    modules.Add("FingerprintFixture", fixtureModule);
    modules.Add("RenamedCIL", modules["CIL"]);
    modules.Remove("CIL");
    Equal(Invoke("renamed-base-baseline", modules.Count, withoutMetadata: true), Invoke("renamed-base", 2));
    modules["CIL"] = modules["RenamedCIL"];
    modules.Remove("RenamedCIL");
    var relocated = Path.Combine(directory, "Relocated");
    Directory.CreateDirectory(relocated);
    foreach (var suffix in new[] { "", ".server", ".private" })
        if (File.Exists(modules["CIL"] + suffix))
            File.Copy(modules["CIL"] + suffix, Path.Combine(relocated, "CIL.olean" + suffix));
    modules["CIL"] = Path.Combine(relocated, "CIL.olean");
    Equal(initial, Invoke("relocated-base", 1));
    using (var file = File.Open(modules["CIL"], FileMode.Append)) file.WriteByte((byte)'\n');
    Equal(Invoke("changed-part-baseline", modules.Count, withoutMetadata: true), Invoke("changed-part", 2));
    modules["CIL"] = Path.Combine(compiled, "CIL.olean");
    var tools = Path.Combine(directory, "ChangedToolchain");
    Directory.CreateDirectory(Path.Combine(tools, "bin"));
    using (var context = new Program())
        File.Copy(context.LeanExecutable, Path.Combine(tools, "bin", Path.GetFileName(context.LeanExecutable)));
    Equal(initial, Invoke("changed-tools", modules.Count, toolchain: tools));
    Invoke("changed-private-metadata", 0, changeMetadata: true);
    var metadata = Path.Combine(prepared, CertifiedFingerprintsName);
    File.AppendAllText(metadata, "\n");
    var manifest = Path.Combine(prepared, "cache-manifest.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(CacheFiles(prepared)));
    var files = CacheFiles(prepared);
    var key = File.ReadAllText(Path.Combine(prepared, "library-key.txt"));
    if (ValidCertifiedLibrary(prepared, digest, key, LibrarySources(files)))
        throw new InvalidOperationException("Self-rehashed metadata bypassed the trusted library digest.");
    Console.WriteLine("PASS source-bound metadata integrity, changed tools and changed module parts");
}
File.WriteAllText(Path.Combine(directory, "timings.json"), JsonSerializer.Serialize(new
{
    baseCount, modules = modules.Count, measurements
}, Json));
Console.WriteLine("Certified fingerprint measurements: " + directory);

sealed record FingerprintBaseJob(string Library, string Digest, Dictionary<string, string> Modules,
    bool WithoutMetadata = false, string? Toolchain = null, bool ChangeMetadata = false);
