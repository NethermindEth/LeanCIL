#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ConsumerTraceDirectory.cs
#:include ConsumerBatchOutcomes.cs

using System.Text.Json;

Run(["dotnet", "run", "--file", At("Tests/ConsumerSourceResolution.cs")]);
Run(["dotnet", "run", "--file", At("Tests/ConsumerSupportUnion.cs")]);
Run(["dotnet", "run", "--file", At("Tests/ConsumerCertificateReuse.cs")]);
Run(["dotnet", "run", "--file", At("Tests/ConsumerComponents.cs")]);
Run(["dotnet", "run", "--file", At("Tests/ConsumerFingerprintReuse.cs")]);
Run(["dotnet", "run", "--file", At("Tests/CertifiedFingerprints.cs")]);

var cli = new[] { "dotnet", args.Length == 0 ? ExtractorPath : Path.GetFullPath(args[0]) };
var root = Path.GetFullPath(At("artifacts/ConsumerPackage"));
var output = At("artifacts/ConsumerExtraction");
// Tamper only this test's private receipts. A valid base certificate may be
// copied from the caller's cache; the verifier still authenticates it normally.
var existingCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
    Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries");
var isolatedCache = At("artifacts/ConsumerCache-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(isolatedCache);
using (var setup = new Program())
{
    var (key, _) = setup.LibraryIdentity(CommonInputs());
    var candidate = Path.Combine(existingCache, key);
    if (Directory.Exists(candidate)) CopyTree(candidate, Path.Combine(isolatedCache, key));
}
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", isolatedCache);
var testTrace = ConsumerTraceDirectory.Create(At("artifacts"), "ConsumerTrace");
Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", testTrace);
Directory.CreateDirectory(Path.Combine(root, "Client"));
var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(root, "lakefile.toml"),
    $"name = \"consumer\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(root, "lean-toolchain"), true);
var independent = Path.Combine(root, "Client", "Independent.lean");
File.WriteAllText(independent, "namespace Client\ntheorem independent (x : Nat) : x = x := rfl\nend Client\n");
const string shared = """
import Extracted
import CIL.Semantics
import Client.Independent
namespace Client
theorem execution (x y : CIL.W64) (memory : CIL.Memory) :
    CIL.invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
      some (memory, [.i64 (x + y)]) := by rfl
end Client
""";
var sharedPath = Path.Combine(root, "Client", "Shared.lean");
File.WriteAllText(sharedPath, shared);
var proof = Path.Combine(root, "Proof.lean");
File.WriteAllText(proof, """
import Client.Shared
namespace ExampleProof
theorem correctness (x y : CIL.W64) (memory : CIL.Memory) :
    CIL.invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
      some (memory, [.i64 (x + y)]) := Client.execution x y memory
end ExampleProof
""");
Run(["lake", "update"], root);
var staleCache = Path.Combine(root, ".lake", "build", "lib", "lean", "Client");
Directory.CreateDirectory(staleCache);
File.WriteAllText(Path.Combine(staleCache, "Shared.olean"), "Not a valid compiled module; consumer caches must not be used.");
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "InitializedTypes::Add(ulong,ulong)", output,
    "--assume-initialized", "Examples.InitializedTypes"]);

void Verify(params string[] options)
{
    var text = Run([.. cli, "verify", output, .. options]);
    if (!text.Contains("Verified: ExampleProof.correctness")) throw new InvalidOperationException(text);
}
string Reject(string marker, params string[] options)
{
    var result = Execute([.. cli, "verify", output, .. options]);
    if (result.Code != 1 || !result.Output.Contains(marker) || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Expected consumer proof rejection: " + result.Output);
    return result.Output;
}
Verify("--proof", proof, "--proof-root", root);
var first = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
var inputs = first.GetProperty("inputs");
if (first.GetProperty("schema").GetInt32() != 4 ||
    !first.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid", StringComparison.Ordinal) ||
    !first.GetProperty("libraryBuild").GetString()!.StartsWith("consumer-", StringComparison.Ordinal))
    throw new InvalidOperationException("Consumer verification omitted certified base or exact extraction certificate audit.");
if (first.GetProperty("initializedTypes")[0].GetString() != "Examples.InitializedTypes")
    throw new InvalidOperationException("Consumer report dropped initialization preconditions.");
if (!inputs.TryGetProperty("consumer:" + sharedPath, out _) ||
    !inputs.TryGetProperty("consumer:" + Path.Combine(root, "lake-manifest.json"), out _) ||
    inputs.GetProperty("revision:leancil").GetString() != revision)
    throw new InvalidOperationException("Missing consumer source or dependency identity.");
Console.WriteLine("PASS external consumer package and transitive dependency importing Extracted");

Verify();
var cached = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (cached.GetProperty("libraryBuild").GetString() != "consumer-proof-cache")
    throw new InvalidOperationException("Unchanged consumer proof was not reused.");
Console.WriteLine("PASS unchanged consumer proof reuses an authenticated successful result");

// A distinct extraction identity must recheck the extraction-dependent proof,
// while the independently certified consumer helper can retain its artifact.
var trace = testTrace;
var beforeReuseTrace = Directory.GetFiles(trace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
var previousTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
string[][] NewReplayCommands(HashSet<string> previous) => Directory.EnumerateFiles(testTrace, "*.jsonl")
    .Where(path => !previous.Contains(path)).SelectMany(File.ReadLines)
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
    .Where(item => item.GetProperty("stage").GetString() is "Kernel replay of consumer proof and dependencies"
        or "Joint kernel replay of consumer proof and dependencies")
    .Select(item => File.ReadLines(Path.Combine(testTrace, item.GetProperty("transcript").GetString()!))
        .Where(line => line.StartsWith('{')).Select(line => JsonSerializer.Deserialize<JsonElement>(line)
            .GetProperty("module").GetString()!).ToArray()).ToArray();
string NewStageOutput(HashSet<string> previous, string stage) => string.Join('\n', Directory.EnumerateFiles(testTrace, "*.jsonl")
    .Where(path => !previous.Contains(path)).SelectMany(File.ReadLines)
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
    .Where(item => item.GetProperty("stage").GetString() == stage)
    .Select(item => File.ReadAllText(Path.Combine(testTrace, item.GetProperty("transcript").GetString()!))));
static bool BuiltModule(string output, string module) =>
    System.Text.RegularExpressions.Regex.IsMatch(output, @"\bBuilt " + System.Text.RegularExpressions.Regex.Escape(module) + @"(\s|$)");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "Arithmetic::Add(ulong,ulong)", output]);
    Verify();
    var replay = NewReplayCommands(beforeReuseTrace);
    if (replay.Length == 0 || replay.Any(command => command.Contains("Client.Independent")) ||
        !replay.Any(command => command.Contains("Client.Shared") && command.Contains("Extracted")))
        throw new InvalidOperationException("Consumer support replay did not distinguish extraction-dependent imports.");
}
finally { Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousTrace); }
Console.WriteLine("PASS extraction-independent helper reused across gates; dependent module replayed");

// Lake traces a module-system file's IR signature; restored support missing it is
// silently recompiled, so the cache saves no build time for such modules.
var moduleSupport = Path.Combine(root, "Client", "ModuleSupport.lean");
var independentBeforeModule = File.ReadAllText(independent);
try
{
    File.WriteAllText(moduleSupport, "module\nnamespace ModuleSupport\npublic theorem refl (x : Nat) : x = x := rfl\nend ModuleSupport\n");
    File.WriteAllText(independent, "import Client.ModuleSupport\n" + independentBeforeModule);
    Verify();
    // Invalidate the proof receipt so the next run restores support instead of the whole result.
    foreach (var receipt in Directory.EnumerateFiles(SuccessCacheRoot, "report.json", SearchOption.AllDirectories))
    {
        var saved = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(receipt));
        if (saved.GetProperty("inputs").TryGetProperty("consumer:" + proof, out _)) File.AppendAllText(receipt, "\n ");
    }
    var previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    var build = NewStageOutput(previous, "Building fresh consumer proof and dependencies");
    if (build.Length == 0 || BuiltModule(build, "Client.ModuleSupport") || BuiltModule(build, "Client.Independent"))
        throw new InvalidOperationException("Cached module-system support was rebuilt.");
}
finally
{
    File.WriteAllText(independent, independentBeforeModule);
    File.Delete(moduleSupport);
}
Console.WriteLine("PASS cached module-system support is restored without a rebuild");

// Extracted.lean names no assembly bytes, so an assembly change outside the extracted program
// restores extraction-dependent modules instead of rebuilding them. They are still replayed
// against the fresh Extracted, and the certificate binds the new assembly.
string[] NewBuildTranscripts(HashSet<string> previous) => Directory.EnumerateFiles(testTrace, "*.jsonl")
    .Where(path => !previous.Contains(path)).SelectMany(File.ReadLines)
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
    .Where(item => item.GetProperty("stage").GetString() == "Building fresh consumer proof and dependencies")
    .Select(item => File.ReadAllText(Path.Combine(testTrace, item.GetProperty("transcript").GetString()!))).ToArray();
var examples = At("Examples/Assembly/bin/Examples.dll");
var patchedDirectory = At("artifacts/ConsumerPatched-" + Guid.NewGuid().ToString("N"));
try
{
    Directory.CreateDirectory(patchedDirectory);
    var patched = Path.Combine(patchedDirectory, "Examples.dll");
    var bytes = File.ReadAllBytes(examples);
    Guid mvid;
    using (var pe = new System.Reflection.PortableExecutable.PEReader(new MemoryStream(bytes)))
    {
        var metadata = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
        mvid = metadata.GetGuid(metadata.GetModuleDefinition().Mvid);
    }
    var mvidBytes = mvid.ToByteArray();
    var offsets = Enumerable.Range(0, bytes.Length - mvidBytes.Length + 1)
        .Where(offset => bytes.AsSpan(offset, mvidBytes.Length).SequenceEqual(mvidBytes)).ToArray();
    if (offsets.Length != 1) throw new InvalidOperationException("Expected one module version identifier in the example assembly.");
    bytes[offsets[0]] ^= 0xff;
    File.WriteAllBytes(patched, bytes);
    if (Sha(patched) == Sha(examples)) throw new InvalidOperationException("Patched assembly is unchanged.");
    var generated = Sha(Path.Combine(output, "Extracted.lean"));
    Run([.. cli, "extract", patched, "Arithmetic::Add(ulong,ulong)", output]);
    if (Sha(Path.Combine(output, "Extracted.lean")) != generated)
        throw new InvalidOperationException("Extracted.lean depends on assembly bytes outside the extracted program.");
    var previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    var builds = NewBuildTranscripts(previous);
    var replay = NewReplayCommands(previous);
    var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (builds.Length != 1 || builds[0].Contains("Built Client.Shared") ||
        !replay.Any(command => command.Contains("Client.Shared") && command.Contains("Extracted")) ||
        report.GetProperty("assemblySha256").GetString() != Sha(patched))
        throw new InvalidOperationException("Identical extraction from a changed assembly did not reuse and replay its dependent module.");
    Console.WriteLine("PASS identical extraction restores dependent modules, replays them and certifies the new assembly");

    // A different extracted program must rebuild the modules that import it.
    Run([.. cli, "extract", examples, "SelectorExamples.Two.Collision::Add(ulong,ulong)", output]);
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    builds = NewBuildTranscripts(previous);
    if (builds.Length != 1 || !builds[0].Contains("Built Client.Shared"))
        throw new InvalidOperationException("A changed extraction reused a module built against another program.");
    Console.WriteLine("PASS changed extraction rebuilds dependent modules");
}
finally
{
    Run([.. cli, "extract", examples, "Arithmetic::Add(ulong,ulong)", output]);
    Directory.Delete(patchedDirectory, true);
}

// Support reuse is keyed by what Lean and Lake read, not by unrelated process
// state or by consumer files outside the support modules' sources.
string[] SupportGenerations() => Directory.EnumerateDirectories(SuccessCacheRoot)
    .Where(path => File.Exists(Path.Combine(path, "files", "leancil-support.json"))).ToArray();
var unrelated = Path.Combine(root, "Unrelated", "Refutation.lean");
var relevantVariable = "LAKE_LEANCIL_TEST_" + Guid.NewGuid().ToString("N");
var savedHostPath = Environment.GetEnvironmentVariable("DOTNET_HOST_PATH");
try
{
    Directory.CreateDirectory(Path.GetDirectoryName(unrelated)!);
    File.WriteAllText(unrelated, "theorem unrelatedRefutation : True := True.intro\n");
    Environment.SetEnvironmentVariable("DOTNET_HOST_PATH", "irrelevant-" + Guid.NewGuid().ToString("N"));
    var generations = SupportGenerations().Length;
    var previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    var replay = NewReplayCommands(previous);
    if (replay.Length != 1 || replay[0].Contains("Client.Independent") || !replay[0].Contains("Client.Shared"))
        throw new InvalidOperationException("Irrelevant environment or unrelated proof file invalidated certified support.");
    // The same support closure republished from a new session must not add a copy.
    var records = SupportGenerations().Select(path => Sha(Path.Combine(path, "files", "leancil-support.json"))).ToArray();
    if (records.Length != generations || records.Distinct().Count() != records.Length ||
        Directory.EnumerateDirectories(SuccessCacheRoot).Any(path => Path.GetFileName(path).Contains('.')))
        throw new InvalidOperationException("Identical support generation was published again.");
    Console.WriteLine("PASS irrelevant environment and unrelated proof files reuse one certified support generation");

    Environment.SetEnvironmentVariable(relevantVariable, "changed");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    if (!NewReplayCommands(previous).Any(command => command.Contains("Client.Independent")))
        throw new InvalidOperationException("A Lake environment variable change reused certified support.");
    Environment.SetEnvironmentVariable(relevantVariable, null);
    File.AppendAllText(independent, "\n-- support source edit\n");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    if (!NewReplayCommands(previous).Any(command => command.Contains("Client.Independent")))
        throw new InvalidOperationException("An edited support module reused its certified artifact.");
    Console.WriteLine("PASS relevant environment and support source edits invalidate certified support");
}
finally
{
    Environment.SetEnvironmentVariable("DOTNET_HOST_PATH", savedHostPath);
    Environment.SetEnvironmentVariable(relevantVariable, null);
    File.WriteAllText(independent, "namespace Client\ntheorem independent (x : Nat) : x = x := rfl\nend Client\n");
    Directory.Delete(Path.GetDirectoryName(unrelated)!, true);
}

// Portable manifests certify freshly rebuilt bytes, including the complete
// import closure. Neither a receipt key nor the producer's environment travels.
var portableVariables = new[] { "LEANCIL_DISABLE_SUCCESS_CACHE", "LEANCIL_EXPORT_CONSUMER_SUPPORT",
    "LEANCIL_CONSUMER_SUPPORT", "LEANCIL_CONSUMER_SUPPORT_SHA256", "LEANCIL_PROFILE_CONSUMER_REPLAY",
    "LEANCIL_TEST_CONFIGURATION", "LEANCIL_SUITE", "LEANCIL_RESTORE_CONSUMER_SUPPORT", "LEANCIL_CACHE_ENVIRONMENT" };
var savedPortableEnvironment = portableVariables.ToDictionary(name => name, Environment.GetEnvironmentVariable);
var originalIndependent = File.ReadAllText(independent);
var configuration = Path.Combine(root, "Client", "Configuration.lean");
var producerOnly = Path.Combine(root, "Client", "ProducerOnly.lean");
var producerProof = Path.Combine(root, "ProducerProof.lean");
var sourcePath = Path.Combine(root, "Client", "SourcePath.lean");
var pathDependent = Path.Combine(root, "Client", "PathDependent.lean");
var multipart = Path.Combine(root, "Client", "Multipart.lean");
var portableDirectory = At("artifacts/PortableConsumer-" + Guid.NewGuid().ToString("N"));
var relocated = At("artifacts/RelocatedConsumer-" + Guid.NewGuid().ToString("N"));
try
{
    File.WriteAllText(configuration, """
import Lean
open Lean Elab Command in
run_cmd do
  let enabled := (← IO.getEnv "LEANCIL_TEST_CONFIGURATION").isSome
  let value ← if enabled then `(true) else `(false)
  elabCommand (← `(def environmentFlag : Bool := $value))
""");
    // Persisted lint diagnostics contain the fresh session's absolute filename.
    const string linted = "theorem linted (x : Nat) : x = x := by simp only [Nat.add_zero]\n";
    File.WriteAllText(multipart, """
module
public import Lean
open Lean Elab Command in
run_cmd do
  let enabled := (← IO.getEnv "LEANCIL_TEST_CONFIGURATION").isSome
  let value ← if enabled then `(true) else `(false)
  elabCommand (← `(private def privateFlag : Bool := $value))
namespace Multipart
""" + "\npublic " + linted + "end Multipart\n");
    File.WriteAllText(independent, "import Client.Configuration\nimport Client.Multipart\n" + originalIndependent + linted);
    // The same filename in a declaration is semantic and must not be stripped.
    File.WriteAllText(sourcePath, """
import Lean
open Lean Elab Command in
run_cmd do
  let value := Syntax.mkStrLit (← getFileName)
  elabCommand (← `(def sourcePath : String := $value))
""");
    File.WriteAllText(pathDependent, "import Client.SourcePath\ntheorem pathRefl : sourcePath = sourcePath := rfl\n");
    File.WriteAllText(sharedPath, "import Client.PathDependent\n" + shared);
    File.WriteAllText(producerOnly, "theorem producerOnly : True := True.intro\n");
    File.WriteAllText(producerProof, "import Client.ProducerOnly\n" + File.ReadAllText(proof));
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
    Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", portableDirectory);
    Environment.SetEnvironmentVariable("LEANCIL_TEST_CONFIGURATION", null);
    Verify("--proof", producerProof, "--proof-root", root);
    var manifest = Directory.GetFiles(portableDirectory, "*.json").Single();
    var manifestBytes = File.ReadAllBytes(manifest);
    Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", null);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", manifest);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", Sha(manifest));
    Environment.SetEnvironmentVariable("LEANCIL_SUITE", "different-receiver-job");
    Directory.CreateDirectory(relocated);
    foreach (var file in Directory.GetFiles(root))
        File.Copy(file, Path.Combine(relocated, Path.GetFileName(file)));
    CopyTree(Path.Combine(root, "Client"), Path.Combine(relocated, "Client"));
    // Resolve fresh git dependencies as a new checkout would.
    Run(["lake", "update"], relocated);
    var previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify("--proof", Path.Combine(relocated, "Proof.lean"), "--proof-root", relocated);
    var commands = NewReplayCommands(previous);
    if (commands.Length == 0 || commands.Any(command => command.Contains("Client.Independent") || command.Contains("Client.Configuration") || command.Contains("Client.Multipart")) ||
        !commands.Any(command => command.Contains("Client.Shared") && command.Contains("Extracted") &&
            command.Contains("Client.SourcePath") && command.Contains("Client.PathDependent")))
        throw new InvalidOperationException("Portable support was not reused after relocation and environment change.");
    Console.WriteLine("PASS relocated lint diagnostics reuse; semantic source paths invalidate dependents; multipart modules reuse");
    var portableReport = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (portableReport.GetProperty("consumerSupportSha256").GetString() != Sha(manifest))
        throw new InvalidOperationException("Portable support provenance missing from certificate.");

    // Opt-in restore lets a receiver skip rebuilding support, not only replaying it: the
    // producer's compiled bytes stand in for a fresh build, as local receipts already do.
    var files = Path.ChangeExtension(manifest, ".files");
    var restoredOlean = Directory.EnumerateFiles(files, "Independent.olean", SearchOption.AllDirectories).Single();
    Environment.SetEnvironmentVariable("LEANCIL_RESTORE_CONSUMER_SUPPORT", "true");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify("--proof", Path.Combine(relocated, "Proof.lean"), "--proof-root", relocated);
    if (BuiltModule(NewStageOutput(previous, "Building fresh consumer proof and dependencies"), "Client.Independent") ||
        NewReplayCommands(previous).Any(command => command.Contains("Client.Independent")))
        throw new InvalidOperationException("Restored portable support was rebuilt or replayed.");
    Console.WriteLine("PASS opt-in portable restore skips the support build and its replay");

    // Restored bytes are trusted only through the manifest digest, never as downloaded.
    var restoredBytes = File.ReadAllBytes(restoredOlean);
    File.AppendAllText(restoredOlean, "tampered portable artifact");
    Reject("support file digest mismatch");
    File.WriteAllBytes(restoredOlean, restoredBytes);
    Console.WriteLine("PASS tampered portable support file is rejected");

    // Without the shipped files a receiver falls back to rebuilding, and still skips replay.
    Directory.Move(files, files + ".absent");
    try
    {
        previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
        Verify();
        if (!BuiltModule(NewStageOutput(previous, "Building fresh consumer proof and dependencies"), "Client.Independent") ||
            NewReplayCommands(previous).Any(command => command.Contains("Client.Independent")))
            throw new InvalidOperationException("Missing portable files did not fall back to a fresh build with fingerprint reuse.");
    }
    finally { Directory.Move(files + ".absent", files); }
    Console.WriteLine("PASS missing portable files fall back to a fresh build");

    // Lake traces do not see variables read by elaborators. Restore binds the declared ones:
    // undeclared, a changed value reuses the producer's bytes; declared, it forces a rebuild.
    Environment.SetEnvironmentVariable("LEANCIL_TEST_CONFIGURATION", "changed");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    if (BuiltModule(NewStageOutput(previous, "Building fresh consumer proof and dependencies"), "Client.Configuration"))
        throw new InvalidOperationException("An undeclared elaborator variable invalidated restored support.");
    Environment.SetEnvironmentVariable("LEANCIL_RESTORE_CONSUMER_SUPPORT", null);
    Environment.SetEnvironmentVariable("LEANCIL_TEST_CONFIGURATION", null);
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_ENVIRONMENT", "LEANCIL_TEST_CONFIGURATION");
    var declaredDirectory = portableDirectory + "-declared";
    Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", declaredDirectory);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", null);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", null);
    Verify("--proof", producerProof, "--proof-root", root);
    var declared = Directory.GetFiles(declaredDirectory, "*.json").Single();
    Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", null);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", declared);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", Sha(declared));
    Environment.SetEnvironmentVariable("LEANCIL_RESTORE_CONSUMER_SUPPORT", "true");
    Environment.SetEnvironmentVariable("LEANCIL_TEST_CONFIGURATION", "changed");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify("--proof", Path.Combine(relocated, "Proof.lean"), "--proof-root", relocated);
    if (!BuiltModule(NewStageOutput(previous, "Building fresh consumer proof and dependencies"), "Client.Configuration") ||
        !NewReplayCommands(previous).Any(command => command.Contains("Client.Configuration")))
        throw new InvalidOperationException("A declared elaborator variable change restored stale support.");
    Environment.SetEnvironmentVariable("LEANCIL_RESTORE_CONSUMER_SUPPORT", null);
    Environment.SetEnvironmentVariable("LEANCIL_TEST_CONFIGURATION", null);
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_ENVIRONMENT", null);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", manifest);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", Sha(manifest));
    Console.WriteLine("PASS restore binds declared elaborator variables and the toolchain");

    Environment.SetEnvironmentVariable("LEANCIL_TEST_CONFIGURATION", "changed");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    if (!NewReplayCommands(previous).Any(command => command.Contains("Client.Independent") && command.Contains("Client.Configuration") &&
        command.Contains("Client.Multipart")))
        throw new InvalidOperationException("Changed compiled dependency did not invalidate portable support closure.");
    Console.WriteLine("PASS unchanged sources with environment-dependent compiled dependency invalidate portable reuse");
    Environment.SetEnvironmentVariable("LEANCIL_TEST_CONFIGURATION", null);

    File.AppendAllText(Path.Combine(relocated, "Client", "Shared.lean"), "\n-- changed source snapshot\n");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    if (!NewReplayCommands(previous).Any(command => command.Contains("Client.Independent")))
        throw new InvalidOperationException("Changed source snapshot did not invalidate portable support.");
    File.AppendAllText(manifest, " ");
    Reject("manifest digest mismatch");
    File.WriteAllBytes(manifest, manifestBytes);
    Console.WriteLine("PASS changed source and tampered portable manifest cannot bypass kernel replay");

    Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", "true");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify("--proof", proof, "--proof-root", root);
    var profileRecords = Directory.EnumerateFiles(testTrace, "*.jsonl").Where(path => !previous.Contains(path)).SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
        .Where(item => item.GetProperty("stage").GetString() == "Profiled kernel replay of consumer modules").ToArray();
    if (profileRecords.Length != 1 || !File.ReadAllText(Path.Combine(testTrace,
        profileRecords[0].GetProperty("transcript").GetString()!)).Contains("\"module\":\"Client.Shared\""))
        throw new InvalidOperationException("Missing per-module kernel replay timing.");
    var replayThreads = Environment.GetEnvironmentVariable("LEAN_NUM_THREADS");
    if (!profileRecords[0].GetProperty("command").EnumerateArray().Any(argument =>
        argument.GetString() == "-j" + (string.IsNullOrWhiteSpace(replayThreads) ? "2" : replayThreads)))
        throw new InvalidOperationException("Replay did not forward the thread limit to the Lean frontend.");
    Console.WriteLine("PASS per-module profiling uses the toolchain checker and produces module timings");
}
finally
{
    foreach (var (name, value) in savedPortableEnvironment) Environment.SetEnvironmentVariable(name, value);
    File.WriteAllText(independent, originalIndependent);
    File.Delete(configuration);
    File.Delete(producerOnly);
    File.Delete(producerProof);
    File.Delete(sourcePath);
    File.Delete(pathDependent);
    File.Delete(multipart);
    File.WriteAllText(sharedPath, shared);
}
Verify("--proof", proof, "--proof-root", root);

// Neither a self-consistent source match nor modified cached bytes can bypass
// the producer receipt. Invalidate the proof receipt too, so this exercises the
// support artifact fallback rather than the unchanged-result fast path.
foreach (var receipt in Directory.EnumerateFiles(SuccessCacheRoot, "report.json", SearchOption.AllDirectories))
{
    var saved = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(receipt));
    if (saved.GetProperty("inputs").TryGetProperty("consumer:" + proof, out _)) File.AppendAllText(receipt, "\n ");
}
var independentArtifacts = Directory.EnumerateFiles(SuccessCacheRoot, "Independent.olean", SearchOption.AllDirectories).ToArray();
if (independentArtifacts.Length == 0) throw new InvalidOperationException("No certified consumer support artifact was published.");
foreach (var artifact in independentArtifacts) File.AppendAllText(artifact, "tampered artifact");
var tamperTrace = testTrace;
var beforeTamperTrace = Directory.GetFiles(tamperTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
try
{
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", tamperTrace);
    Verify();
    var commands = NewReplayCommands(beforeTamperTrace);
    if (!commands.Any(command => command.Contains("Client.Independent")))
        throw new InvalidOperationException("Tampered consumer artifacts were not rebuilt and replayed.");
}
finally { Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousTrace); }
Console.WriteLine("PASS tampered consumer support and proof receipts fall back to fresh verification");

// A changed imported proof must fail, regardless of any existing consumer caches.
File.WriteAllText(sharedPath, shared.Replace("x + y", "x - y"));
var importedFailure = Reject("error:");
CheckConsumerLeanSummary(importedFailure, "Client/Shared.lean:", "(building Client.Shared)", "x - y");
Console.WriteLine("PASS proof-checking failure leads with the located Lean errors of the failing module");
File.WriteAllText(sharedPath, shared + "\n-- Imported-source identity changed.\n");
Verify();
var restored = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (inputs.GetProperty("consumer:" + sharedPath).GetString() ==
    restored.GetProperty("inputs").GetProperty("consumer:" + sharedPath).GetString())
    throw new InvalidOperationException("Imported source edit did not change report identity.");
Console.WriteLine("PASS incorrect imported lemma rejected, settings reused and source hashes updated");

// A custom Lake output directory must not hide unused declarations from replay.
var lakefile = Path.Combine(root, "lakefile.toml");
var lakeConfiguration = File.ReadAllText(lakefile);
var poison = Path.Combine(root, "Client", "Poison.lean");
Directory.CreateDirectory(Path.GetDirectoryName(poison)!);
try
{
    File.WriteAllText(lakefile, lakeConfiguration
        .Replace("name = \"consumer\"\n", "name = \"consumer\"\nbuildDir = \".lake/custom-build\"\n"));
    File.WriteAllText(poison, "namespace Client.Poison\ntheorem valid : True := True.intro\nend Client.Poison\n");
    File.WriteAllText(sharedPath, "import Client.Poison\n" + shared);
    Verify();
    Console.WriteLine("PASS custom Lake build directory with additional consumer module verified");
    File.WriteAllText(poison, """
        import Lean
        set_option debug.skipKernelTC true
        run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
          name := `Client.Poison.forged
          levelParams := []
          type := Lean.mkConst ``False
          value := Lean.mkConst ``True.intro
        })
        """);
    File.WriteAllText(sharedPath, "import Client.Poison\n" + shared);
    // The selected theorem does not use the forged declaration, so axiom audit
    // alone cannot detect it. Require the kernel replay diagnostic specifically.
    Reject("while replaying declaration");
}
finally
{
    File.WriteAllText(lakefile, lakeConfiguration);
    File.WriteAllText(sharedPath, shared);
    File.Delete(poison);
}
Console.WriteLine("PASS unused forged consumer helper in custom Lake build directory rejected by kernel replay");

File.WriteAllText(Path.Combine(root, "Extracted.lean"), "-- stale extraction");
Reject("reserved");
File.Delete(Path.Combine(root, "Extracted.lean"));
var framework = Path.Combine(root, ".lake/packages/leancil/CIL/Types.lean");
var frameworkSource = File.ReadAllText(framework);
try
{
    File.AppendAllText(framework, "\n-- changed framework\n");
    Reject("differ from the verifier");
}
finally { File.WriteAllText(framework, frameworkSource); }
Console.WriteLine("PASS stale generated modules and mismatched framework sources rejected");

// One batch session: requests sharing an extraction share a workspace and replay,
// yet each keeps its own pass/fail, certificate and expected rejection.
var batchA = At("artifacts/ConsumerBatchA");
var batchB = At("artifacts/ConsumerBatchB");
var batchC = At("artifacts/ConsumerBatchC");
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "InitializedTypes::Add(ulong,ulong)", batchA,
    "--assume-initialized", "Examples.InitializedTypes"]);
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "Arithmetic::Add(ulong,ulong)", batchB]);
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "Arithmetic::WrongAdd(ulong,ulong)", batchC]);
var alternate = Path.Combine(root, "ProofAlternate.lean");
var batchManifest = At("artifacts/ConsumerBatch.json");
var batchResults = At("artifacts/ConsumerBatchResults.json");
var batchVariable = "LAKE_LEANCIL_TEST_" + Guid.NewGuid().ToString("N");
object BatchRequest(string extraction, string proofPath, string theorem, string? expect = null) => expect is null
    ? new { output = extraction, proof = proofPath, theorem }
    : new { output = extraction, proof = proofPath, theorem, expect };
(int Code, string Output) Batch(params object[] requests)
{
    File.WriteAllText(batchManifest, JsonSerializer.Serialize(new { schema = 1, proofRoot = root, requests }));
    var result = Execute([.. cli, "verify-batch", batchManifest, "--results", batchResults]);
    return (result.Code, result.Output);
}
try
{
    File.WriteAllText(alternate, File.ReadAllText(proof).Replace("namespace ExampleProof", "namespace AlternateProof")
        .Replace("end ExampleProof", "end AlternateProof"));
    CheckConsumerBatchOutcomes(cli, root, proof, batchA, batchB, batchC, alternate);
    // A relevant Lake variable forces fresh support: the first workspace certifies
    // it and the second reuses those exact artifacts within the same session.
    Environment.SetEnvironmentVariable(batchVariable, "batch");
    var previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    var (code, text) = Batch(BatchRequest(batchA, proof, "ExampleProof.correctness"),
        BatchRequest(batchB, alternate, "AlternateProof.correctness"));
    var replays = NewReplayCommands(previous);
    if (code != 0 || replays.Length != 2 || replays.Count(command => command.Contains("Client.Independent")) != 1)
        throw new InvalidOperationException("Batch workspaces did not share certified support: " + text);
    (code, text) = Batch(BatchRequest(batchA, proof, "ExampleProof.correctness"),
        BatchRequest(batchB, alternate, "AlternateProof.correctness"));
    if (code != 0 || JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(batchResults))!
        .Any(item => item.GetProperty("libraryBuild").GetString() != "consumer-proof-cache"))
        throw new InvalidOperationException("Unchanged batch requests did not reuse authenticated results: " + text);
    Console.WriteLine("PASS batch workspaces share certified support and reuse unchanged results");

    // A long batch must report finished requests while later workspaces still run, or it looks hung.
    // The second workspace's proof build ends seconds after the first request's line unless lines wait for the end.
    Environment.SetEnvironmentVariable(batchVariable, "progress");
    var progressTrace = ConsumerTraceDirectory.Create(At("artifacts"), "ConsumerProgressTrace");
    var savedTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
    int CompletedBuilds() => Directory.EnumerateFiles(progressTrace, "*.jsonl").Sum(path =>
    {
        using var stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite | FileShare.Delete);
        using var reader = new StreamReader(stream);
        return reader.ReadToEnd().Split('\n').Count(line => line.Contains("\"stage\":\"Building fresh consumer proof and dependencies\""));
    });
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", progressTrace);
        File.WriteAllText(batchManifest, JsonSerializer.Serialize(new { schema = 1, proofRoot = root, requests = new[] {
            BatchRequest(batchA, proof, "ExampleProof.correctness"), BatchRequest(batchB, alternate, "AlternateProof.correctness") } }));
        var start = new System.Diagnostics.ProcessStartInfo(cli[0])
            { RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
        foreach (var argument in cli.Skip(1).Concat(["verify-batch", batchManifest, "--results", batchResults])) start.ArgumentList.Add(argument);
        using var process = System.Diagnostics.Process.Start(start)!;
        var errors = process.StandardError.ReadToEndAsync();
        var lines = new List<string>();
        var buildsAtFirstResult = -1;
        while (process.StandardOutput.ReadLine() is { } line)
        {
            if (buildsAtFirstResult < 0 && line.StartsWith("PASS ", StringComparison.Ordinal)) buildsAtFirstResult = CompletedBuilds();
            lines.Add(line);
        }
        process.WaitForExit();
        var all = string.Join("\n", lines) + "\n" + errors.GetAwaiter().GetResult();
        if (process.ExitCode != 0 || buildsAtFirstResult != 1 || CompletedBuilds() != 2 ||
            !lines.First(line => line.StartsWith("PASS ", StringComparison.Ordinal)).Contains("ExampleProof.correctness") ||
            lines.Count(line => line.StartsWith("PASS verified", StringComparison.Ordinal)) != 2 ||
            lines[^1] != "Batch: 2 passed, 0 failed of 2 requests.")
            throw new InvalidOperationException($"Batch results were not reported as workspaces finished (builds at first result: {buildsAtFirstResult}):\n{all}");
        var results = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(batchResults))!;
        if (results.Length != 2 || results[0].GetProperty("theorem").GetString() != "ExampleProof.correctness" ||
            results[1].GetProperty("theorem").GetString() != "AlternateProof.correctness")
            throw new InvalidOperationException("Batch results file no longer follows request order.");
    }
    finally
    {
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", savedTrace);
    }
    Console.WriteLine("PASS batch reports each request when its workspace finishes; summary and results keep request order");
}
finally
{
    Environment.SetEnvironmentVariable(batchVariable, null);
    File.Delete(alternate);
}

// A batch session exports one manifest covering every workspace, so a producer need not split
// a request out of its batch; receivers combine several manifests, each under its own digest.
var savedUnionEnvironment = portableVariables.ToDictionary(name => name, Environment.GetEnvironmentVariable);
var portableX = Path.Combine(root, "Client", "PortableX.lean");
var portableY = Path.Combine(root, "Client", "PortableY.lean");
var proofX = Path.Combine(root, "ProofX.lean");
var proofY = Path.Combine(root, "ProofY.lean");
var proofXY = Path.Combine(root, "ProofXY.lean");
var unionDirectory = At("artifacts/PortableUnion-" + Guid.NewGuid().ToString("N"));
try
{
    File.WriteAllText(portableX, "theorem portableX : True := True.intro\n");
    File.WriteAllText(portableY, "theorem portableY : True := True.intro\n");
    File.WriteAllText(proofX, "import Client.PortableX\n" + File.ReadAllText(proof));
    File.WriteAllText(proofY, "import Client.PortableY\n" + File.ReadAllText(proof));
    File.WriteAllText(proofXY, "import Client.PortableX\nimport Client.PortableY\n" + File.ReadAllText(proof));
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", null);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", null);
    Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", Path.Combine(unionDirectory, "batch"));
    var (code, text) = Batch(BatchRequest(batchA, proofX, "ExampleProof.correctness"),
        BatchRequest(batchB, proofY, "ExampleProof.correctness"));
    var exported = Directory.GetFiles(Path.Combine(unionDirectory, "batch"), "*.json");
    if (code != 0 || exported.Length != 1)
        throw new InvalidOperationException("A batch session must export exactly one manifest: " + text);
    var union = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(exported[0]));
    if (union.GetProperty("Schema").GetInt32() != 3 ||
        !new[] { "Client.PortableX", "Client.PortableY" }.All(module =>
            union.GetProperty("Modules").TryGetProperty(module, out _) && union.GetProperty("Files").TryGetProperty(module, out _)))
        throw new InvalidOperationException("Batch export omitted a workspace's support closure.");
    Console.WriteLine("PASS batch export unions the support of every workspace into one manifest");

    string Export(string name, string proofPath)
    {
        Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", Path.Combine(unionDirectory, name));
        Verify("--proof", proofPath, "--proof-root", root);
        Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", null);
        return Directory.GetFiles(Path.Combine(unionDirectory, name), "*.json").Single();
    }
    var manifestX = Export("x", proofX);
    var manifestY = Export("y", proofY);
    string[][] Receive(string paths, string digests)
    {
        Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", paths);
        Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", digests);
        var previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
        Verify("--proof", proofXY, "--proof-root", root);
        return NewReplayCommands(previous);
    }
    var both = Receive(manifestX + Path.PathSeparator + manifestY, Sha(manifestX) + "," + Sha(manifestY));
    var onlyX = Receive(manifestX, Sha(manifestX));
    if (both.Any(command => command.Contains("Client.PortableX") || command.Contains("Client.PortableY")) ||
        onlyX.Any(command => command.Contains("Client.PortableX")) || !onlyX.Any(command => command.Contains("Client.PortableY")))
        throw new InvalidOperationException("Combined portable manifests were not each honored.");
    // A digest count that does not pair with the paths has no trusted anchor for some manifest.
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", manifestX + Path.PathSeparator + manifestY);
    Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", Sha(manifestX));
    Reject("missing trusted digest", "--proof", proofXY, "--proof-root", root);
    Console.WriteLine("PASS several trusted manifests combine, and unpaired digests are rejected");
}
finally
{
    foreach (var (name, value) in savedUnionEnvironment) Environment.SetEnvironmentVariable(name, value);
    File.Delete(portableX);
    File.Delete(portableY);
    File.Delete(proofX);
    File.Delete(proofY);
    File.Delete(proofXY);
}
