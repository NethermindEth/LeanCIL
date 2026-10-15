#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

var cli = new[] { "dotnet", args.Length == 0 ? ExtractorPath : Path.GetFullPath(args[0]) };
var root = Path.GetFullPath(At("artifacts/ConsumerPackage"));
var output = At("artifacts/ConsumerExtraction");
// Tamper only this test's private receipts. A valid base certificate may be
// copied from the caller's cache; the verifier still authenticates it normally.
var existingCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
    Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries");
var isolatedCache = At("artifacts/ConsumerCache-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(isolatedCache);
if (Directory.Exists(existingCache))
{
    foreach (var candidate in Directory.EnumerateDirectories(existingCache))
        if (File.Exists(Path.Combine(candidate, "cache-manifest.json")) &&
            File.Exists(Path.Combine(candidate, "lakefile.toml")) && Sha(Path.Combine(candidate, "lakefile.toml")) == Sha(At("lakefile.toml")))
            CopyTree(candidate, Path.Combine(isolatedCache, Path.GetFileName(candidate)));
}
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", isolatedCache);
var testTrace = At("artifacts/ConsumerTrace-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(testTrace);
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
void Reject(string marker, params string[] options)
{
    var result = Execute([.. cli, "verify", output, .. options]);
    if (result.Code != 1 || !result.Output.Contains(marker) || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Expected consumer proof rejection: " + result.Output);
}
Verify("--proof", proof, "--proof-root", root);
var first = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
var inputs = first.GetProperty("inputs");
if (first.GetProperty("schema").GetInt32() != 3 ||
    !first.GetProperty("extractionAudit").GetString()!.Contains("ExtractionAudit.valid", StringComparison.Ordinal) ||
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
    .Where(item => item.GetProperty("stage").GetString() == "Kernel replay of consumer proof and dependencies")
    .Select(item => File.ReadLines(Path.Combine(testTrace, item.GetProperty("transcript").GetString()!))
        .Where(line => line.StartsWith('{')).Select(line => JsonSerializer.Deserialize<JsonElement>(line)
            .GetProperty("module").GetString()!).ToArray()).ToArray();
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

// Portable manifests certify freshly rebuilt bytes, including the complete
// import closure. Neither a receipt key nor the producer's environment travels.
var portableVariables = new[] { "LEANCIL_DISABLE_SUCCESS_CACHE", "LEANCIL_EXPORT_CONSUMER_SUPPORT",
    "LEANCIL_CONSUMER_SUPPORT", "LEANCIL_CONSUMER_SUPPORT_SHA256", "LEANCIL_PROFILE_CONSUMER_REPLAY",
    "LEANCIL_TEST_CONFIGURATION", "LEANCIL_SUITE" };
var savedPortableEnvironment = portableVariables.ToDictionary(name => name, Environment.GetEnvironmentVariable);
var originalIndependent = File.ReadAllText(independent);
var configuration = Path.Combine(root, "Client", "Configuration.lean");
var producerOnly = Path.Combine(root, "Client", "ProducerOnly.lean");
var producerProof = Path.Combine(root, "ProducerProof.lean");
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
    File.WriteAllText(independent, "import Client.Configuration\n" + originalIndependent);
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
    if (commands.Length == 0 || commands.Any(command => command.Contains("Client.Independent") || command.Contains("Client.Configuration")) ||
        !commands.Any(command => command.Contains("Client.Shared") && command.Contains("Extracted")))
        throw new InvalidOperationException("Portable support was not reused after relocation and environment change.");
    Console.WriteLine("PASS portable support across checkout roots and environments without local receipts");
    var portableReport = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (portableReport.GetProperty("consumerSupportSha256").GetString() != Sha(manifest))
        throw new InvalidOperationException("Portable support provenance missing from certificate.");

    Environment.SetEnvironmentVariable("LEANCIL_TEST_CONFIGURATION", "changed");
    previous = Directory.GetFiles(testTrace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    Verify();
    if (!NewReplayCommands(previous).Any(command => command.Contains("Client.Independent") && command.Contains("Client.Configuration")))
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
    Console.WriteLine("PASS per-module profiling uses the toolchain checker and produces module timings");
}
finally
{
    foreach (var (name, value) in savedPortableEnvironment) Environment.SetEnvironmentVariable(name, value);
    File.WriteAllText(independent, originalIndependent);
    File.Delete(configuration);
    File.Delete(producerOnly);
    File.Delete(producerProof);
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
Reject("error:");
File.WriteAllText(sharedPath, shared + "\n-- Imported-source identity changed.\n");
Verify();
var restored = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (inputs.GetProperty("consumer:" + sharedPath).GetString() ==
    restored.GetProperty("inputs").GetProperty("consumer:" + sharedPath).GetString())
    throw new InvalidOperationException("Imported source edit did not change report identity.");
Console.WriteLine("PASS incorrect imported lemma rejected, settings reused and source hashes updated");

File.WriteAllText(sharedPath, shared.Replace("theorem execution", "axiom execution").Replace(" := by rfl", ""));
Reject("Unapproved proof axioms");
File.WriteAllText(sharedPath, shared);
Console.WriteLine("PASS axiom hidden in imported consumer module rejected");

File.WriteAllText(sharedPath, "import Lean\n" + shared + "\n" + """
set_option debug.skipKernelTC true
run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
  name := `Client.forged
  levelParams := []
  type := Lean.mkConst ``False
  value := Lean.mkConst ``True.intro
})
""");
Reject("while replaying declaration");
File.WriteAllText(sharedPath, shared);
Console.WriteLine("PASS kernel replay rejects unchecked declarations in consumer imports");

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
