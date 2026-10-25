#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/LibraryAudit.cs

using System.Text.Json;

if (args is ["--worker", var specification, var output])
{
    var job = JsonSerializer.Deserialize<FingerprintJob>(File.ReadAllText(specification))!;
    using var worker = new Program { freshLibrary = job.Fresh };
    worker.auditExecutable = job.Auditor;
    worker.auditExecutableSha = Sha(job.Auditor);
    worker.resolvedToolchain = job.Toolchain;
    var result = worker.PortableConsumerModuleParts(Path.GetDirectoryName(specification)!, job.Modules);
    File.WriteAllText(output, JsonSerializer.Serialize(result));
    return;
}

var measure = args.Contains("--measure", StringComparer.Ordinal);
var baselineWorker = args.FirstOrDefault(argument => argument != "--measure");
var measureOnly = baselineWorker is not null;
var workerAssembly = baselineWorker ?? typeof(Program).Assembly.Location;
var directory = At("artifacts/ConsumerFingerprintReuse-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(directory);
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", Path.Combine(directory, "Cache"));
Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
string? toolchain = null;
var auditor = At(".lake/build/bin/leancil-audit" + (OperatingSystem.IsWindows() ? ".exe" : ""));
var moduleDirectory = At(".lake/build/lib/lean");
var paths = measure
    ? Directory.EnumerateFiles(Path.Combine(moduleDirectory, "CIL"), "*.olean", SearchOption.AllDirectories)
        .Append(Path.Combine(moduleDirectory, "CIL.olean")).ToArray()
    : new[] { Path.Combine(moduleDirectory, "CIL.olean"),
        Path.Combine(moduleDirectory, "CIL/Interface/Closure.olean") };
var modules = paths.Order(StringComparer.Ordinal).ToDictionary(
    path => ModuleName(Path.GetRelativePath(moduleDirectory, path).Replace('\\', '/')),
    path => path, StringComparer.Ordinal);
var source = Path.Combine(directory, "FingerprintFixture.lean");
var compiled = Path.ChangeExtension(source, ".olean");
modules.Add("FingerprintFixture", compiled);
var original = """
    module
    public import Lean
    public section
    def fingerprintValue : String := "Lean.Linter.lintLogExt first"
    theorem fingerprintValue_eq : fingerprintValue = fingerprintValue := rfl
    #print axioms fingerprintValue_eq
    """;
void Compile(string text)
{
    File.WriteAllText(source, text);
    Run(["lean", "--root=" + directory, "-o", compiled, source]);
}
Compile(original);
var measurements = new List<object>();
Dictionary<string, SortedDictionary<string, string>> Invoke(string label, int expectedSerialized, bool fresh = false)
{
    var specification = Path.Combine(directory, label + ".job.json");
    var output = Path.Combine(directory, label + ".result.json");
    var trace = Path.Combine(directory, label + ".trace");
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    var rawInputBytes = modules.Values.Sum(path => new[] { "", ".server", ".private" }
        .Where(suffix => File.Exists(path + suffix)).Sum(suffix => new FileInfo(path + suffix).Length));
    File.WriteAllText(specification, JsonSerializer.Serialize(new FingerprintJob(auditor, modules, fresh, toolchain)));
    var entriesBefore = Directory.Exists(SuccessCacheRoot) ? Directory.GetDirectories(SuccessCacheRoot).Length : 0;
    var timer = System.Diagnostics.Stopwatch.StartNew();
    var result = Execute(["dotnet", workerAssembly, "--worker", specification, output]);
    timer.Stop();
    File.WriteAllText(Path.Combine(directory, label + ".log"), result.Output);
    if (result.Code != 0) throw new InvalidOperationException(label + " failed:\n" + result.Output);
    var publishedEntry = Directory.Exists(SuccessCacheRoot) &&
        Directory.GetDirectories(SuccessCacheRoot).Length != entriesBefore;
    if (fresh && publishedEntry)
        throw new InvalidOperationException("Fresh normalization published a cache entry.");
    var count = System.Text.RegularExpressions.Regex.Match(result.Output,
        @"canonical module fingerprints \(\d+ reused, (\d+) serialized\)");
    if (!measureOnly && !count.Success)
        throw new InvalidOperationException("Missing fingerprint serialization count: " + label);
    var serialized = count.Success ? int.Parse(count.Groups[1].Value) : modules.Count;
    if (!measureOnly && serialized != expectedSerialized)
        throw new InvalidOperationException($"{label}: expected {expectedSerialized} serializations, got {serialized}");
    var fingerprints = JsonSerializer.Deserialize<Dictionary<string, SortedDictionary<string, string>>>(
        File.ReadAllText(output))!;
    var normalization = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
        .Where(stage => stage.GetProperty("stage").GetString() == "Fingerprinting portable consumer modules")
        .ToArray();
    if (normalization.Length != (serialized > 0 ? 1 : 0))
        throw new InvalidOperationException("Unexpected normalization process count: " + label);
    measurements.Add(new { label, seconds = timer.Elapsed.TotalSeconds, serialized, modules = modules.Count,
        rawInputBytes, normalizationCalls = normalization.Length,
        normalizationSeconds = normalization.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()) });
    Console.WriteLine($"PASS {label}: {serialized} serialized, {timer.Elapsed.TotalSeconds:F3}s");
    return fingerprints;
}
void Equal(Dictionary<string, SortedDictionary<string, string>> expected,
    Dictionary<string, SortedDictionary<string, string>> actual)
{
    if (expected.Count != actual.Count || expected.Any(pair =>
            !actual.TryGetValue(pair.Key, out var parts) || !Same(pair.Value, parts)))
        throw new InvalidOperationException("Canonical module fingerprints changed.");
}
var initial = Invoke("initial", modules.Count);
Equal(initial, Invoke("unchanged-process", 0));
Equal(initial, Invoke("fresh-process", modules.Count, fresh: true));
Compile(original.Replace("first", "second", StringComparison.Ordinal));
var changed = Invoke("semantic-change", 1);
if (Same(initial["FingerprintFixture"], changed["FingerprintFixture"]))
    throw new InvalidOperationException("A semantic string change was omitted from the fingerprint.");
Equal(changed, Invoke("changed-fresh", modules.Count, fresh: true));
modules.Remove("FingerprintFixture");
modules.Add("RenamedFixture", compiled);
var renamed = Invoke("renamed-module", 1);
Equal(renamed, Invoke("renamed-fresh", modules.Count, fresh: true));
if (!measure)
{
    modules = new(StringComparer.Ordinal) { ["RenamedFixture"] = compiled };
    var fixture = new Dictionary<string, SortedDictionary<string, string>>
        { ["RenamedFixture"] = renamed["RenamedFixture"] };
    var corrupted = 0;
    foreach (var entry in Directory.EnumerateDirectories(SuccessCacheRoot))
    {
        var payload = Path.Combine(entry, "files", "fingerprints.json");
        if (!File.Exists(payload)) continue;
        var parts = JsonSerializer.Deserialize<SortedDictionary<string, string>>(File.ReadAllText(payload))!;
        if (!Same(parts, fixture["RenamedFixture"])) continue;
        parts[parts.Keys.First()] = new string('0', 64);
        File.WriteAllText(payload, JsonSerializer.Serialize(parts));
        var receiptPath = Path.Combine(entry, "receipt.json");
        var receipt = JsonSerializer.Deserialize<SortedDictionary<string, string>>(File.ReadAllText(receiptPath))!;
        receipt["fingerprints.json"] = Sha(payload);
        File.WriteAllText(receiptPath, JsonSerializer.Serialize(receipt));
        corrupted++;
    }
    if (corrupted == 0) throw new InvalidOperationException("No fingerprint receipt found to corrupt.");
    Equal(fixture, Invoke("self-rehashed-corruption", 1));
    foreach (var suffix in new[] { "", ".server", ".private" })
    {
        var part = compiled + suffix;
        if (!File.Exists(part)) throw new InvalidOperationException("Missing multipart fixture: " + part);
        var bytes = File.ReadAllBytes(part);
        File.WriteAllBytes(part, [.. bytes, (byte)'\n']);
        var appended = Invoke("changed-part" + suffix, 1);
        Equal(appended, Invoke("changed-part-fresh" + suffix, 1, fresh: true));
        File.WriteAllBytes(part, bytes);
        Equal(fixture, Invoke("restored-part" + suffix, 0));
    }
    foreach (var suffix in new[] { ".private", ".server" })
    {
        File.Move(compiled + suffix, compiled + suffix + ".saved");
        var fewer = Invoke("removed-part" + suffix, 1);
        Equal(fewer, Invoke("removed-part-fresh" + suffix, 1, fresh: true));
    }
    foreach (var suffix in new[] { ".server", ".private" })
    {
        File.Move(compiled + suffix + ".saved", compiled + suffix);
        var added = Invoke("added-part" + suffix, 0);
        Equal(added, Invoke("added-part-fresh" + suffix, 1, fresh: true));
    }
    var originalAuditor = auditor;
    auditor = Path.Combine(directory, Path.GetFileName(auditor));
    File.Copy(originalAuditor, auditor);
    Equal(fixture, Invoke("relocated-auditor", 0));
    using (var file = File.Open(auditor, FileMode.Append)) file.WriteByte(0);
    Equal(fixture, Invoke("changed-auditor", 1));
    auditor = originalAuditor;
    toolchain = Path.Combine(directory, "Toolchain");
    Directory.CreateDirectory(Path.Combine(toolchain, "bin"));
    using (var setup = new Program())
        File.Copy(setup.LeanExecutable, Path.Combine(toolchain, "bin", Path.GetFileName(setup.LeanExecutable)));
    var runtime = Path.Combine(toolchain, "bin", "fingerprint-runtime.dll");
    File.WriteAllText(runtime, "first native runtime identity");
    Equal(fixture, Invoke("different-toolchain", 1));
    Equal(fixture, Invoke("unchanged-toolchain", 0));
    File.WriteAllText(runtime, "changed native runtime identity");
    Equal(fixture, Invoke("changed-runtime", 1));
    toolchain = null;
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
    Equal(fixture, Invoke("disabled-cache", 1));
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
    var linted = original + "\npublic theorem linted (x : Nat) : x = x := by simp only [Nat.add_zero]\n" +
        "#print axioms linted\n";
    Compile(linted);
    var firstLinted = Invoke("linted", 1);
    var relocated = Path.Combine(directory, "Relocated");
    Directory.CreateDirectory(relocated);
    var relocatedSource = Path.Combine(relocated, Path.GetFileName(source));
    File.WriteAllText(relocatedSource, linted);
    Run(["lean", "--root=" + relocated, "-o", Path.ChangeExtension(relocatedSource, ".olean"), relocatedSource]);
    modules["RenamedFixture"] = Path.ChangeExtension(relocatedSource, ".olean");
    Equal(firstLinted, Invoke("relocated-linter-diagnostics", 1));
    Equal(firstLinted, Invoke("relocated-linter-fresh", 1, fresh: true));

    var dependent = Path.Combine(directory, "FingerprintDependent.lean");
    File.WriteAllText(dependent,
        "module\npublic import FingerprintFixture\npublic def dependentValue : String := fingerprintValue\n");
    Run(["lean", "--root=" + directory, "-o", Path.ChangeExtension(dependent, ".olean"), dependent],
        leanPath: directory);
    modules = new(StringComparer.Ordinal)
    {
        ["FingerprintFixture"] = compiled,
        ["FingerprintDependent"] = Path.ChangeExtension(dependent, ".olean")
    };
    var supportParts = Invoke("bound-support", 2);
    using var binding = new Program
        { auditExecutable = auditor, auditExecutableSha = Sha(auditor), libraryKey = "fingerprint-binding-fixture" };
    var sources = new SortedDictionary<string, string>(StringComparer.Ordinal)
        { ["consumer:" + source] = Sha(source), ["consumer:" + dependent] = Sha(dependent) };
    var manifest = new ConsumerSupportManifest(3, binding.VerificationPolicy, binding.libraryKey,
        binding.ConsumerToolchainIdentity(), PortableConsumerSources(directory, sources),
        new(supportParts, StringComparer.Ordinal),
        new(binding.ConsumerModuleImports(directory, modules), StringComparer.Ordinal), "",
        new(StringComparer.Ordinal));
    var manifestPath = Path.Combine(directory, "support.json");
    File.WriteAllText(manifestPath, JsonSerializer.Serialize(manifest));
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", manifestPath);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", Sha(manifestPath));
    var trusted = binding.TrustedConsumerSupport(directory, sources);
    if (trusted.Length != 1 || !binding.ImportedConsumerSupport(directory, trusted, modules).SetEquals(modules.Keys))
        throw new InvalidOperationException("Matching source/import-bound support was not reusable.");
    Compile(original.Replace("first", "dependency-changed", StringComparison.Ordinal));
    if (binding.ImportedConsumerSupport(directory, trusted, modules).Count != 0)
        throw new InvalidOperationException("A changed dependency did not invalidate its importer.");
    sources["consumer:" + source] = Sha(source);
    if (binding.TrustedConsumerSupport(directory, sources).Length != 0)
        throw new InvalidOperationException("Changed source inputs retained portable support trust.");
    File.AppendAllText(manifestPath, "\n");
    try
    {
        binding.TrustedConsumerSupport(directory, sources);
        throw new Exception("A changed portable manifest retained its trusted digest.");
    }
    catch (InvalidDataException error) when (error.Message.Contains("digest mismatch", StringComparison.Ordinal)) { }
    if (binding.ReplayConsumerModules(directory, modules.Keys, directory).Count != 0)
        throw new InvalidOperationException("Fingerprint fixtures failed independent kernel replay.");
    Console.WriteLine("PASS source/import closure binding, trusted manifest integrity and kernel replay");
}
File.WriteAllText(Path.Combine(directory, "timings.json"), JsonSerializer.Serialize(measurements,
    new JsonSerializerOptions { WriteIndented = true }));
Console.WriteLine("Fingerprint measurements: " + directory);

sealed record FingerprintJob(string Auditor, Dictionary<string, string> Modules, bool Fresh, string? Toolchain = null);
