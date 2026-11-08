#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Collections.Concurrent;
using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;

string[] cli = ["dotnet", ExtractorPath];
var root = At("artifacts/ProofWorkspace-" + Guid.NewGuid().ToString("N"));
var consumer = Path.Combine(root, "Consumer");
var package = Path.Combine(root, "Package");
Directory.CreateDirectory(Path.Combine(package, "Client"));
// A four-limb struct with a static constructor and symbols stands in for any consumer library type.
const string method = "Workspace.Wide::get_IsZeroOrOne()";
const string initializedType = "Workspace.Wide";
const string shiftedBody = "((u0 >> 1) | u1 | u2 | u3) == 0";
const string unshiftedBody = "(u0 | u1 | u2 | u3) == 0";
// A second method in its own file, so editing it moves no sequence point of the first.
const string twiceMethod = "Workspace.Arith::Twice(ulong)";
const string twiceBody = "x + x;";
const string changedTwiceBody = "x + x + 1;";
Directory.CreateDirectory(consumer);
var project = Path.Combine(consumer, "Workspace.csproj");
File.WriteAllText(project, """
    <Project Sdk="Microsoft.NET.Sdk">
      <PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
    </Project>
    """);
var wide = Path.Combine(consumer, "Wide.cs");
File.WriteAllText(wide, """
    namespace Workspace;

    public readonly struct Wide(ulong u0, ulong u1, ulong u2, ulong u3)
    {
        public static readonly Wide Zero = default;
        public static readonly Wide One = new(1, 0, 0, 0);

        readonly ulong u0 = u0, u1 = u1, u2 = u2, u3 = u3;

        public bool IsZeroOrOne => ((u0 >> 1) | u1 | u2 | u3) == 0;
    }
    """);
var arith = Path.Combine(consumer, "Arith.cs");
File.WriteAllText(arith, """
    namespace Workspace;

    public static class Arith
    {
        public static ulong Twice(ulong x) => x + x;
    }
    """);
Console.WriteLine("Building the workspace consumer fixture");
Run(["dotnet", "build", project, "-c", "Release"]);
var assembly = Path.Combine(consumer, "bin", "Workspace.dll");
var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"consumer\"\n[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) +
    "\nrev = \"" + revision + "\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
var proof = Path.Combine(package, "Proof.lean");
// A proof written before its method was selected names no method; the editor does not resolve that import.
File.WriteAllText(proof, "import Extracted\n#check Extracted.program\n");
Run(["lake", "update"], package);
var framework = Path.Combine(package, ".lake", "packages", "leancil");
var editor = Path.Combine(framework, ".lake", "leancil");
var compiledModules = Path.Combine(framework, ".lake", "build", "lib", "lean");
string[] command = [.. cli, "workspace", assembly, method, "--profile", "scalar", "--proof", proof,
    "--theorem", "WorkspaceProof.selectedMethod", "--assume-initialized", initializedType];

// The module a proof imports for its method, as the workspace command prints it.
string KeyOf(string output) => Regex.Match(output, @"import Extracted\.([A-Za-z0-9_]+)") is { Success: true } match
    ? match.Groups[1].Value : throw new InvalidOperationException("The workspace named no module: " + output);
// Lake builds imports exactly as the language server's setup-file does for a file outside any library.
(int Code, string Output) CheckProof(string file)
{
    var result = Execute(["lake", "lean", file], package);
    return (result.Code, result.Output);
}
string CheckedProof()
{
    var result = CheckProof(proof);
    if (result.Code != 0) throw new InvalidOperationException("The proof does not check in place: " + result.Output);
    return result.Output;
}
int CodeLength(string key)
{
    var probe = Path.Combine(package, "CodeLength.lean");
    File.WriteAllText(probe, $"import Extracted.{key}\n#eval Extracted.method0.code.length\n");
    try
    {
        var printed = Run(["lake", "lean", probe], package);
        return int.Parse(Regex.Match(printed, @"^(\d+)\s*$", RegexOptions.Multiline).Groups[1].Value);
    }
    finally { File.Delete(probe); }
}
void Edit(string file, string from, string to)
{
    var text = File.ReadAllText(file);
    if (!text.Contains(from, StringComparison.Ordinal))
        throw new InvalidOperationException($"{file} does not contain {from}");
    File.WriteAllText(file, text.Replace(from, to, StringComparison.Ordinal));
}
void Rebuild(string from, string to)
{
    Edit(wide, from, to);
    Run(["dotnet", "build", project, "-c", "Release"]);
}
string[] EditorFiles() => [.. Directory.EnumerateFiles(editor, "*", SearchOption.AllDirectories)
    .Select(path => Path.GetRelativePath(editor, path).Replace('\\', '/')).Order(StringComparer.Ordinal)];

Console.WriteLine("Rejecting an editor environment Lean would truncate, before writing the editor library");
// A lowered limit stands in for Lean's Windows buffer on every OS; the editor's `lake serve` would lose LEAN_PATH.
var crowded = Execute(command,
    environment: new Dictionary<string, string> { [LeanEnvironmentLimitVariable] = "1000" });
var serveCheck = "`lake serve` in " + Path.GetFullPath(package);
if (crowded.Code == 0 || !crowded.Output.Contains(serveCheck, StringComparison.Ordinal) ||
    !crowded.Output.Contains("1,000-byte limit", StringComparison.Ordinal) || Directory.Exists(editor))
    throw new InvalidOperationException("An oversized editor environment was not rejected at setup:\n" +
        crowded.Output);
Console.WriteLine("Generating the editor extraction in the consumer package and checking the proof in place");
var created = Run(command);
var key = KeyOf(created);
var unkeyed = CheckProof(proof);
if (!created.Contains("Editor checking is not a certificate", StringComparison.Ordinal) ||
    !created.Contains("import ExtractedSymbols." + key, StringComparison.Ordinal) ||
    !created.Contains("replace it with import Extracted." + key, StringComparison.Ordinal) || unkeyed.Code == 0)
    throw new InvalidOperationException("A proof importing plain Extracted resolved or got no advice: " + created +
        "\n" + unkeyed.Output);
var helper = Path.Combine(package, "Client", "Support.lean");
File.WriteAllText(helper, $"""
import Extracted.{key}
import ExtractedSymbols.{key}
namespace Client
theorem methodCount : Extracted.program.length = 1 := rfl
theorem methodIdentity : Extracted.method0Signature =
    "System.Boolean Workspace.Wide::get_IsZeroOrOne()" := rfl
#print axioms methodCount
#print axioms methodIdentity
end Client
""");
File.WriteAllText(proof, """
import Client.Support
namespace WorkspaceProof
theorem selectedMethod : Extracted.program.length = 1 ∧ Extracted.method0Signature =
    "System.Boolean Workspace.Wide::get_IsZeroOrOne()" :=
  ⟨Client.methodCount, Client.methodIdentity⟩
#print axioms selectedMethod
end WorkspaceProof
""");
// Only the editor library's keyed modules and the selection record are written; none is a report or receipt.
string[] editorFiles = [$"Extracted/{key}.lean", $"ExtractedSymbols/{key}.lean", $"selections/{key}/selection.json"];
if (!EditorFiles().SequenceEqual(editorFiles) ||
    Directory.EnumerateFiles(package, "*", SearchOption.AllDirectories)
        .Any(path => Path.GetFileName(path) is "verified.json" or "verification.json" or "receipt.json"))
    throw new InvalidOperationException("An editor workspace must never publish a certificate: " +
        string.Join(", ", EditorFiles()));
if (Run(["git", "status", "--porcelain"], framework).Length != 0)
    throw new InvalidOperationException("The editor extraction changed the framework checkout's tracked files.");
var codeLength = CodeLength(key);
File.AppendAllText(proof, $"""

example : Extracted.method0.code.length = {codeLength} := by
  trace_state
  decide
""");
var goals = CheckedProof();
if (!goals.Contains($"⊢ Extracted.method0.code.length = {codeLength}", StringComparison.Ordinal))
    throw new InvalidOperationException("Editing the proof in place did not show its goal: " + goals);
Console.WriteLine("PASS the proof checks in place against its keyed extraction and shows its goals; plain Extracted " +
    "is not generated and the command names the import to use");

// A helper the package gains after the first run states a fact about the method body, not just its identity.
var body = Path.Combine(package, "Client", "Body.lean");
void WriteBody(int length) => File.WriteAllText(body, $"""
import Extracted.{key}
namespace Client
theorem codeLength : Extracted.method0.code.length = {length} := by decide
end Client
""");
WriteBody(codeLength);
Edit(proof, "import Client.Support\n", "import Client.Support\nimport Client.Body\n");
var compiled = Path.Combine(compiledModules, "Extracted", key + ".olean");
var compiledAt = File.GetLastWriteTimeUtc(compiled);
var editorAt = Directory.EnumerateFiles(editor, "*", SearchOption.AllDirectories)
    .ToDictionary(path => path, File.GetLastWriteTimeUtc);
Run(command);
// An unchanged method must leave the extraction and its build untouched, or every re-run rebuilds helpers.
if (File.GetLastWriteTimeUtc(compiled) != compiledAt ||
    editorAt.Any(entry => File.GetLastWriteTimeUtc(entry.Key) != entry.Value))
    throw new InvalidOperationException("Re-running for an unchanged method rewrote or rebuilt the extraction.");
CheckedProof();
Console.WriteLine("PASS a helper module added to the package is accepted; an unchanged re-run rebuilds nothing");

Console.WriteLine("Rebuilding the assembly with a different method body and refreshing in place");
var clock = Stopwatch.StartNew();
Rebuild(shiftedBody, unshiftedBody);
var rebuildTime = clock.Elapsed;
clock.Restart();
var refreshed = Execute(command);
var refreshTime = clock.Elapsed;
clock.Restart();
// Lake traces the helper through the keyed module, so its proof about the old body fails without any Lean edit.
var stale = CheckProof(proof);
var checkTime = clock.Elapsed;
if (refreshed.Code != 0 || stale.Code == 0 || !stale.Output.Contains("Client/Body.lean", StringComparison.Ordinal))
    throw new InvalidOperationException("A rebuilt assembly did not reach the proof's helper after a refresh: " +
        refreshed.Output + "\n" + stale.Output);
if (KeyOf(refreshed.Output) != key)
    throw new InvalidOperationException("A rebuild changed the module name of the same method.");
var changedLength = CodeLength(key);
if (changedLength == codeLength)
    throw new InvalidOperationException("The refreshed extraction kept the old method body.");
WriteBody(changedLength);
Edit(proof, $"= {codeLength} :=", $"= {changedLength} :=");
goals = CheckedProof();
if (!goals.Contains($"⊢ Extracted.method0.code.length = {changedLength}", StringComparison.Ordinal))
    throw new InvalidOperationException("The goals did not follow the rebuilt method: " + goals);
Console.WriteLine($"PASS a C# rebuild refreshes the extraction in place: build {rebuildTime.TotalSeconds:F1}s, " +
    $"workspace {refreshTime.TotalSeconds:F1}s, stale helper reported in {checkTime.TotalSeconds:F1}s");

Console.WriteLine("Verifying the same proof files through fresh hermetic verification");
var output = Path.Combine(root, "Verification");
string[] extract = [.. cli, "extract", assembly, method, output, "scalar", "--assume-initialized", initializedType];
string[] verify = [.. cli, "verify", output, "--proof", proof, "--proof-root", package,
    "--theorem", "WorkspaceProof.selectedMethod"];
Run(extract);
Run([.. verify, "--fresh"]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid", StringComparison.Ordinal) ||
    report.GetProperty("libraryBuild").GetString() == "consumer-proof-cache")
    throw new InvalidOperationException("Workspace proof did not pass ordinary fresh extraction audit and hermetic verification.");
// Verification never reads the editor's sources: a forged editor module changes nothing it certifies.
File.AppendAllText(Path.Combine(editor, "Extracted", key + ".lean"), "\ntheorem forged : False := sorry\n");
Run(verify);
var forgedReport = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (forgedReport.GetProperty("identitySha256").GetString() != report.GetProperty("identitySha256").GetString() ||
    forgedReport.GetProperty("inputs").EnumerateObject().Any(input =>
        input.Name.Replace('\\', '/').Contains("/.lake/leancil/", StringComparison.Ordinal)))
    throw new InvalidOperationException("Verification read the editor's Extracted module.");
File.AppendAllText(Path.Combine(output, "Extracted.lean"), "\n-- changed after extraction\n");
var tampered = Execute(verify);
if (tampered.Code == 0 || !tampered.Output.Contains("differs from regenerated CIL", StringComparison.Ordinal) ||
    File.Exists(Path.Combine(output, "verified.json")))
    throw new InvalidOperationException("Verification accepted a tampered extraction: " + tampered.Output);
Run(extract);
Run(command);
CheckedProof();
Console.WriteLine("PASS the same files verify fresh, ignore forged editor sources and reject a tampered extraction");

// After a rebuild verify extracts again from the recorded settings; the stale helper then fails as in the editor.
Rebuild(unshiftedBody, shiftedBody);
var reextracted = Execute(verify);
if (reextracted.Code == 0 || !reextracted.Output.Contains("Re-extracted", StringComparison.Ordinal) ||
    !reextracted.Output.Contains("Body.lean", StringComparison.Ordinal))
    throw new InvalidOperationException("verify did not re-extract the rebuilt assembly: " + reextracted.Output);
WriteBody(codeLength);
Edit(proof, $"= {changedLength} :=", $"= {codeLength} :=");
var current = Run(verify);
if (current.Contains("Re-extracted", StringComparison.Ordinal) ||
    !current.Contains("Verified:", StringComparison.Ordinal))
    throw new InvalidOperationException("verify re-extracted an artifact that matched the assembly: " + current);
var mismatched = Path.Combine(package, "Mismatched.lean");
File.WriteAllText(mismatched, "import Extracted.Wide_get_IsZeroOrOne_00000000\ntheorem other : True := trivial\n");
var foreign = Execute([.. cli, "verify", output, "--proof", mismatched, "--proof-root", package, "--theorem", "other"]);
File.Delete(mismatched);
if (foreign.Code == 0 || !foreign.Output.Contains("names another extraction", StringComparison.Ordinal) ||
    !foreign.Output.Contains("Extracted." + key, StringComparison.Ordinal))
    throw new InvalidOperationException("Verification accepted a key of another extraction: " + foreign.Output);
Run(command);
CheckedProof();
Console.WriteLine("PASS verify re-extracts a rebuilt assembly from its recorded settings and rejects a proof " +
    "importing another extraction's module");

var pdb = Path.ChangeExtension(assembly, ".pdb");
var savedPdb = File.ReadAllBytes(pdb);
try
{
    File.Delete(pdb);
    Run(command);
    var withoutSymbols = CheckProof(proof);
    if (File.Exists(Path.Combine(editor, "ExtractedSymbols", key + ".lean")) || withoutSymbols.Code == 0 ||
        !withoutSymbols.Output.Contains("ExtractedSymbols", StringComparison.Ordinal))
        throw new InvalidOperationException("A missing PDB left stale editor symbols: " + withoutSymbols.Output);
}
finally { File.WriteAllBytes(pdb, savedPdb); }
Run(command);
CheckedProof();
Console.WriteLine("PASS a missing PDB removes ExtractedSymbols instead of keeping names of an older build");

void Reject(string[] arguments, string marker)
{
    var result = Execute(arguments);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new InvalidOperationException("Expected the workspace command to reject with '" + marker + "': " +
            result.Output);
}

var shadow = Path.Combine(package, "Client", "ExtractedSymbols.lean");
File.WriteAllText(shadow, "def forged : Nat := 0\n");
try { Reject(command, "reserved for the selected extractions"); }
finally { File.Delete(shadow); }
var keyedShadow = Path.Combine(package, "Extracted", key + ".lean");
Directory.CreateDirectory(Path.GetDirectoryName(keyedShadow)!);
File.WriteAllText(keyedShadow, "def forged : Nat := 0\n");
try { Reject(command, "reserved for the selected extractions"); }
finally { Directory.Delete(Path.GetDirectoryName(keyedShadow)!, true); }
// Another profile of the same method is another extraction; it is added beside this one, not in its place.
var wideFiles = EditorFiles();
var wideAt = Directory.EnumerateFiles(editor, "*", SearchOption.AllDirectories)
    .ToDictionary(path => path, File.GetLastWriteTimeUtc);
string[] otherProfileCommand = [.. command];
otherProfileCommand[Array.IndexOf(otherProfileCommand, "scalar")] = "arm64-advsimd";
var otherProfile = Run(otherProfileCommand);
var otherKey = KeyOf(otherProfile);
if (otherKey == key || !otherProfile.Contains("1 other method extraction", StringComparison.Ordinal) ||
    !File.Exists(Path.Combine(editor, "Extracted", otherKey + ".lean")) ||
    wideAt.Any(entry => File.GetLastWriteTimeUtc(entry.Key) != entry.Value))
    throw new InvalidOperationException("A second selection replaced or touched the first: " + otherProfile);
CheckedProof();
// Dropping a selection takes its modules and Lake outputs and leaves the other method's files and build alone.
var otherCompiled = Path.Combine(compiledModules, "Extracted", otherKey + ".olean");
if (!File.Exists(otherCompiled)) throw new InvalidOperationException("The other selection was not built.");
var wideBuilt = Directory.EnumerateFiles(compiledModules, key + ".*", SearchOption.AllDirectories)
    .ToDictionary(path => path, File.GetLastWriteTimeUtc);
Reject([.. cli, "workspace", "--remove", method, "--proof-root", package], "names 2 selections");
Reject([.. cli, "workspace", "--remove", "Wide_get_IsZeroOrOne_00000000", "--proof-root", package],
    "No recorded selection matches");
var removed = Run([.. cli, "workspace", "--remove", method, "--profile", "arm64-advsimd", "--proof-root", package]);
var removedProbe = Path.Combine(package, "Removed.lean");
File.WriteAllText(removedProbe, $"import Extracted.{otherKey}\n");
var removedCheck = CheckProof(removedProbe);
File.Delete(removedProbe);
if (!removed.Contains("Removed editor extraction " + otherKey, StringComparison.Ordinal) ||
    !EditorFiles().SequenceEqual(wideFiles) || File.Exists(otherCompiled) || removedCheck.Code == 0 ||
    wideAt.Any(entry => File.GetLastWriteTimeUtc(entry.Key) != entry.Value) ||
    wideBuilt.Any(entry => File.GetLastWriteTimeUtc(entry.Key) != entry.Value))
    throw new InvalidOperationException("Removing the other selection left files behind or touched the first: " +
        removed + string.Join(", ", EditorFiles()) + removedCheck.Output);
CheckedProof();
var olderRevision = Run(["git", "rev-parse", "HEAD^"], framework).Trim();
try
{
    Run(["git", "update-ref", "HEAD", olderRevision], framework);
    Reject(command, "dependency revision differs");
}
finally { Run(["git", "update-ref", "HEAD", revision], framework); }
// Exercise the framework actually used by the tool without mutating the running checkout.
var toolCopy = Path.Combine(root, "Tool");
var toolSource = Path.GetDirectoryName(ExtractorPath)!;
foreach (var source in Directory.EnumerateFiles(toolSource, "*", SearchOption.AllDirectories))
{
    var destination = Path.Combine(toolCopy, Path.GetRelativePath(toolSource, source));
    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
    File.Copy(source, destination);
}
File.AppendAllText(Path.Combine(toolCopy, "verification", "CIL", "ProfileEquivalence.lean"), "\n-- other framework\n");
Reject(["dotnet", Path.Combine(toolCopy, Path.GetFileName(ExtractorPath)), .. command[2..]],
    "differ from the verifier's bundled framework");
Console.WriteLine("PASS reserved sources, other frameworks and moved dependency revisions are rejected; another " +
    "profile is a second extraction beside the first, and removing it leaves the first untouched");

// A scratch proof has no Lake package above it; the temp directory keeps the checkout's lakefile out of reach.
var standalone = Path.Combine(Path.GetTempPath(), "leancil-standalone-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(standalone);
// Opening must not depend on the author's git setup: with signing required and no signer, any commit fails.
var signingConfig = Path.Combine(standalone, "signing.gitconfig");
File.WriteAllText(signingConfig, "[commit]\n\tgpgsign = true\n[gpg]\n\tprogram = leancil-missing-signer\n");
var globalConfig = Environment.GetEnvironmentVariable("GIT_CONFIG_GLOBAL");
Environment.SetEnvironmentVariable("GIT_CONFIG_GLOBAL", signingConfig);
try
{
    var scratchProof = Path.Combine(standalone, "Scratch.lean");
    File.WriteAllText(scratchProof, "-- written once the module name is known\n");
    string[] open = [.. cli, "workspace", assembly, method, "--profile", "scalar", "--proof", scratchProof,
        "--assume-initialized", initializedType];
    var opened = Run(open);
    if (!opened.Contains("Created a Lake package beside the proof", StringComparison.Ordinal) ||
        !File.Exists(Path.Combine(standalone, "lakefile.toml")) || KeyOf(opened) != key)
        throw new InvalidOperationException("A standalone proof did not get a package beside it: " + opened);
    File.WriteAllText(scratchProof, $"""
        import Extracted.{key}
        import ExtractedSymbols.{key}
        theorem scratch : Extracted.program.length = 1 := rfl
        #print axioms scratch
        """);
    if (Directory.EnumerateDirectories(standalone, ".git", SearchOption.AllDirectories).Any())
        throw new InvalidOperationException("A standalone workspace created a git repository.");
    // Lake lists a source directory once per library, so test libraries would crowd LEAN_SRC_PATH toward
    // Lean's Windows environment limit; the copy declares only the framework and editor libraries.
    var bundled = Path.GetFullPath(Path.Combine(standalone, ".lake", "packages", "leancil"));
    var sourcePath = Run(["lake", "env"], standalone).Split('\n', StringSplitOptions.TrimEntries)
        .Single(line => line.StartsWith("LEAN_SRC_PATH=", StringComparison.Ordinal))["LEAN_SRC_PATH=".Length..];
    var frameworkEntries = sourcePath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
        .Count(entry => Path.GetFullPath(entry).StartsWith(bundled, StringComparison.OrdinalIgnoreCase));
    if (frameworkEntries != 2)
        throw new InvalidOperationException($"The bundled framework adds {frameworkEntries} source directories " +
            "to LEAN_SRC_PATH instead of one each for CIL and the editor library: " + sourcePath);
    Run(["lake", "lean", scratchProof], standalone);
    // The framework copy is required by path, which certification never accepts in place of a pinned revision.
    var unpinned = Execute([.. cli, "verify", output, "--proof", scratchProof, "--proof-root", standalone,
        "--theorem", "scratch"]);
    if (unpinned.Code == 0 || !unpinned.Output.Contains("must be git packages pinned", StringComparison.Ordinal))
        throw new InvalidOperationException("Verification accepted an unpinned framework dependency: " +
            unpinned.Output);
    // Single-file verification resolves the keyed import to the extraction it checks; a new output has no
    // saved package root.
    var singleOutput = Path.Combine(root, "Single");
    Run([.. cli, "extract", assembly, method, singleOutput, "scalar", "--assume-initialized", initializedType]);
    var single = Run([.. cli, "verify", singleOutput, "--proof", scratchProof, "--theorem", "scratch"]);
    if (!single.Contains("Verified: scratch", StringComparison.Ordinal))
        throw new InvalidOperationException("A keyed single-file proof did not verify: " + single);
    File.AppendAllText(scratchProof, "\ntheorem edited : Extracted.program.length = 1 := scratch\n");
    var reopened = Run(open);
    if (reopened.Contains("Created a Lake package", StringComparison.Ordinal))
        throw new InvalidOperationException("Re-running regenerated the standalone package: " + reopened);
    Run(["lake", "lean", scratchProof], standalone);
}
finally
{
    Environment.SetEnvironmentVariable("GIT_CONFIG_GLOBAL", globalConfig);
    Directory.Delete(standalone, true);
}
Console.WriteLine("PASS a standalone proof gets a package beside it without git commits or a pinned framework, " +
    "verifies as a single file and refreshes on re-run");

Console.WriteLine("Watching two proofs of two methods in one package");
var twiceProof = Path.Combine(package, "TwiceProof.lean");
File.WriteAllText(twiceProof, "-- written once the module name is known\n");
var twiceKey = KeyOf(Run([.. cli, "workspace", assembly, twiceMethod, "--profile", "scalar", "--proof", twiceProof,
    "--theorem", "TwiceProof.length"]));
void WriteTwiceProof(int length) => File.WriteAllText(twiceProof, $"""
import Extracted.{twiceKey}
namespace TwiceProof
theorem length : Extracted.method0.code.length = {length} := by decide
#print axioms length
end TwiceProof
""");
var twiceLength = CodeLength(twiceKey);
WriteTwiceProof(twiceLength);
// Both proofs are open at once: each checks in place against its own method's extraction.
CheckedProof();
if (CheckProof(twiceProof).Code != 0) throw new InvalidOperationException("The second proof does not check in place.");

string[] watch = [.. cli, "watch", package, "--project", project, "--format", "json"];
(JsonElement Cycle, TimeSpan Elapsed) WatchOnce(bool passes)
{
    var started = Stopwatch.StartNew();
    var result = Execute([.. watch, "--once"]);
    var line = result.Stdout.Split('\n').LastOrDefault(text => text.StartsWith('{'))
        ?? throw new InvalidOperationException("watch printed no cycle: " + result.Output);
    var cycle = JsonSerializer.Deserialize<JsonElement>(line);
    if ((result.Code == 0) != passes || cycle.GetProperty("passed").GetBoolean() != passes)
        throw new InvalidOperationException($"watch {(passes ? "failed" : "passed")} unexpectedly: " + result.Output);
    return (cycle, started.Elapsed);
}
JsonElement Outcome(JsonElement cycle, string file) => cycle.GetProperty("results").EnumerateArray()
    .Single(result => result.GetProperty("proof").GetString() == file);
void Expect(JsonElement cycle, string file, string status, bool rechecked)
{
    var outcome = Outcome(cycle, file);
    if (outcome.GetProperty("status").GetString() != status ||
        outcome.GetProperty("rechecked").GetBoolean() != rechecked)
        throw new InvalidOperationException($"Expected {file} {status} (rechecked {rechecked}): {cycle}");
}
string[] Refreshed(JsonElement cycle) =>
    [.. cycle.GetProperty("refreshed").EnumerateArray().Select(module => module.GetString()!)];
// Every file of the first method's extraction: editor modules, Lake outputs and verification records.
Dictionary<string, (string Hash, DateTime Time)> WideSnapshot() =>
    new[] { Path.Combine(editor, "selections", key) }
        .SelectMany(directory => Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories))
        .Concat(new[] { "Extracted", "ExtractedSymbols" }.SelectMany(module => new[] { editor, compiledModules }
            .Select(directory => Path.Combine(directory, module)).Where(Directory.Exists)
            .SelectMany(directory => Directory.EnumerateFiles(directory, key + ".*"))))
        .ToDictionary(path => path, path => (Sha(path), File.GetLastWriteTimeUtc(path)));

// watch refreshes the modules the editor loads, so it refuses the same truncated environment before any cycle.
var crowdedWatch = Execute([.. watch, "--once"],
    environment: new Dictionary<string, string> { [LeanEnvironmentLimitVariable] = "1000" });
if (crowdedWatch.Code == 0 || !crowdedWatch.Output.Contains(serveCheck, StringComparison.Ordinal) ||
    crowdedWatch.Stdout.Contains('{'))
    throw new InvalidOperationException("watch ran a cycle in an oversized environment:\n" + crowdedWatch.Output);

var (first, firstTime) = WatchOnce(passes: true);
Expect(first, "Proof.lean", "verified", rechecked: true);
Expect(first, "TwiceProof.lean", "verified", rechecked: true);
var (quiet, quietTime) = WatchOnce(passes: true);
Expect(quiet, "Proof.lean", "verified", rechecked: false);
Expect(quiet, "TwiceProof.lean", "verified", rechecked: false);
if (Refreshed(quiet).Length != 0) throw new InvalidOperationException("An unchanged build refreshed: " + quiet);
Console.WriteLine($"PASS watch verifies both proofs ({firstTime.TotalSeconds:F1}s), then reruns nothing when " +
    $"nothing changed ({quietTime.TotalSeconds:F1}s)");

var wideBefore = WideSnapshot();
if (!wideBefore.Keys.Any(path => Path.GetFileName(path) == "verified.json"))
    throw new InvalidOperationException("The first method's verification left no certificate.");
Edit(arith, twiceBody, changedTwiceBody);
var (edited, editedTime) = WatchOnce(passes: false);
// Exactly the edited method's extraction is refreshed and its proof rechecked; the other one is not touched.
if (!Refreshed(edited).Contains("Extracted." + twiceKey) ||
    Refreshed(edited).Any(module => module.EndsWith("." + key, StringComparison.Ordinal)))
    throw new InvalidOperationException("The edit did not refresh exactly the edited method: " + edited);
Expect(edited, "TwiceProof.lean", "failed", rechecked: true);
Expect(edited, "Proof.lean", "verified", rechecked: false);
var located = Outcome(edited, "TwiceProof.lean").GetProperty("report").GetProperty("failures")[0].GetProperty("source");
if (Path.GetFullPath(located.GetProperty("file").GetString()!) != Path.GetFullPath(twiceProof) ||
    located.GetProperty("line").GetInt32() != 3)
    throw new InvalidOperationException("The failure is not located at the proof's theorem: " + edited);
var wideAfter = WideSnapshot();
if (wideAfter.Count != wideBefore.Count || wideAfter.Any(entry =>
        !wideBefore.TryGetValue(entry.Key, out var before) || before != entry.Value))
    throw new InvalidOperationException("Editing the second method touched the first method's files.");
var changedTwice = CodeLength(twiceKey);
WriteTwiceProof(changedTwice);
var (fixedProof, fixTime) = WatchOnce(passes: true);
Expect(fixedProof, "TwiceProof.lean", "verified", rechecked: true);
Expect(fixedProof, "Proof.lean", "verified", rechecked: false);
Console.WriteLine($"PASS a C# edit refreshes and rechecks exactly its method, located at TwiceProof.lean:3 " +
    $"({editedTime.TotalSeconds:F1}s edit to feedback); the other method's files are byte-identical with " +
    $"unchanged times; the fixed proof verifies ({fixTime.TotalSeconds:F1}s)");

// A failed build must never leave an earlier build's result green: every proof is stale and loses its certificate.
Edit(arith, changedTwiceBody, "x + x +;");
var (broken, _) = WatchOnce(passes: false);
var errors = broken.GetProperty("build").EnumerateArray().ToArray();
if (errors.Length == 0 || errors.Any(error => Path.GetFileName(error.GetProperty("file").GetString()) != "Arith.cs") ||
    errors[0].GetProperty("line").GetInt32() != 5)
    throw new InvalidOperationException("The build failure is not located in the C# source: " + broken);
Expect(broken, "Proof.lean", "stale", rechecked: true);
Expect(broken, "TwiceProof.lean", "stale", rechecked: true);
if (Directory.EnumerateFiles(Path.Combine(editor, "selections"), "verified.json", SearchOption.AllDirectories).Any())
    throw new InvalidOperationException("A failed build left a certificate of an earlier build.");
Edit(arith, "x + x +;", changedTwiceBody);
var (restored, _) = WatchOnce(passes: true);
Expect(restored, "Proof.lean", "verified", rechecked: true);
Expect(restored, "TwiceProof.lean", "verified", rechecked: true);
Console.WriteLine("PASS a failed C# build is located at Arith.cs:5, makes every proof stale and deletes its " +
    "certificate; the next good build verifies both again");

// A proof whose method is renamed away reports it, and its editor module is removed so the editor fails too.
Edit(arith, "Twice(ulong x)", "Doubled(ulong x)");
var (renamed, _) = WatchOnce(passes: false);
Expect(renamed, "TwiceProof.lean", "missing", rechecked: true);
Expect(renamed, "Proof.lean", "verified", rechecked: false);
if (!Outcome(renamed, "TwiceProof.lean").GetProperty("message").GetString()!.Contains("no longer in the assembly",
        StringComparison.Ordinal) ||
    File.Exists(Path.Combine(editor, "Extracted", twiceKey + ".lean")) || CheckProof(twiceProof).Code == 0)
    throw new InvalidOperationException("A renamed method was not reported missing: " + renamed);
Console.WriteLine("PASS a renamed method is reported missing and its proof fails at its import in the editor");

// The loop: a running watch notices the C# edit, rebuilds and reports without any command.
var loop = new ProcessStartInfo(watch[0]) { RedirectStandardOutput = true, RedirectStandardError = true };
foreach (var argument in watch.Skip(1)) loop.ArgumentList.Add(argument);
using var watcher = Process.Start(loop)!;
var cycles = new BlockingCollection<string>();
watcher.OutputDataReceived += (_, line) => { if (line.Data?.StartsWith('{') == true) cycles.Add(line.Data); };
watcher.ErrorDataReceived += (_, _) => { };
watcher.BeginOutputReadLine();
watcher.BeginErrorReadLine();
try
{
    JsonElement Next()
    {
        if (!cycles.TryTake(out var line, TimeSpan.FromMinutes(10)))
            throw new InvalidOperationException("watch reported no cycle within ten minutes.");
        return JsonSerializer.Deserialize<JsonElement>(line);
    }
    Next();
    var edit = Stopwatch.StartNew();
    Edit(arith, "Doubled(ulong x)", "Twice(ulong x)");
    var noticed = Next();
    var feedback = edit.Elapsed;
    Expect(noticed, "TwiceProof.lean", "verified", rechecked: true);
    Expect(noticed, "Proof.lean", "verified", rechecked: false);
    Console.WriteLine($"PASS a running watch rebuilds, refreshes and verifies the restored method " +
        $"{feedback.TotalSeconds:F1}s after the C# edit");
}
finally
{
    if (!watcher.HasExited) watcher.Kill(entireProcessTree: true);
}
