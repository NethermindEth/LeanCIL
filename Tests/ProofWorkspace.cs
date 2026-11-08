#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

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
Directory.CreateDirectory(consumer);
File.WriteAllText(Path.Combine(consumer, "Workspace.csproj"), """
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
Console.WriteLine("Building the workspace consumer fixture");
Run(["dotnet", "build", Path.Combine(consumer, "Workspace.csproj"), "-c", "Release"]);
var assembly = Path.Combine(consumer, "bin", "Workspace.dll");
var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"consumer\"\n[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) +
    "\nrev = \"" + revision + "\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
var helper = Path.Combine(package, "Client", "Support.lean");
File.WriteAllText(helper, """
import Extracted
import ExtractedSymbols
namespace Client
theorem methodCount : Extracted.program.length = 1 := rfl
theorem methodIdentity : Extracted.method0Signature =
    "System.Boolean Workspace.Wide::get_IsZeroOrOne()" := rfl
#print axioms methodCount
#print axioms methodIdentity
end Client
""");
var proof = Path.Combine(package, "Proof.lean");
const string selectedMethod = """
import Client.Support
namespace WorkspaceProof
theorem selectedMethod : Extracted.program.length = 1 ∧ Extracted.method0Signature =
    "System.Boolean Workspace.Wide::get_IsZeroOrOne()" :=
  ⟨Client.methodCount, Client.methodIdentity⟩
#print axioms selectedMethod
end WorkspaceProof
""";
File.WriteAllText(proof, selectedMethod);
Run(["lake", "update"], package);
var framework = Path.Combine(package, ".lake", "packages", "leancil");
var editor = Path.Combine(framework, ".lake", "leancil");
string[] command = [.. cli, "workspace", assembly, method,
    "--profile", "scalar", "--proof", proof, "--assume-initialized", initializedType];

// Lake builds imports exactly as the language server's setup-file does for a file outside any library.
(int Code, string Output) CheckProof()
{
    var result = Execute(["lake", "lean", proof], package);
    return (result.Code, result.Output);
}
string CheckedProof()
{
    var result = CheckProof();
    if (result.Code != 0) throw new InvalidOperationException("The proof does not check in place: " + result.Output);
    return result.Output;
}
int CodeLength()
{
    var probe = Path.Combine(package, "CodeLength.lean");
    File.WriteAllText(probe, "import Extracted\n#eval Extracted.method0.code.length\n");
    try
    {
        var printed = Run(["lake", "lean", probe], package);
        return int.Parse(Regex.Match(printed, @"^(\d+)\s*$", RegexOptions.Multiline).Groups[1].Value);
    }
    finally { File.Delete(probe); }
}
void Rebuild(string from, string to)
{
    File.WriteAllText(wide, File.ReadAllText(wide).Replace(from, to, StringComparison.Ordinal));
    Run(["dotnet", "build", Path.Combine(consumer, "Workspace.csproj"), "-c", "Release"]);
}

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
string[] editorFiles = ["Extracted.lean", "ExtractedSymbols.lean", "selection.json"];
// Only the editor library's sources and Lake's own outputs are written; none of them is a report or receipt.
if (!created.Contains("Editor checking is not a certificate", StringComparison.Ordinal) ||
    !Directory.EnumerateFiles(editor).Select(Path.GetFileName).Order(StringComparer.Ordinal)
        .SequenceEqual(editorFiles) ||
    Directory.EnumerateFiles(package, "*", SearchOption.AllDirectories)
        .Any(path => Path.GetFileName(path) is "verified.json" or "verification.json" or "receipt.json"))
    throw new InvalidOperationException("An editor workspace must never publish a certificate.");
if (Run(["git", "status", "--porcelain"], framework).Length != 0)
    throw new InvalidOperationException("The editor extraction changed the framework checkout's tracked files.");
var codeLength = CodeLength();
File.AppendAllText(proof, $"""

example : Extracted.method0.code.length = {codeLength} := by
  trace_state
  decide
""");
var goals = CheckedProof();
if (!goals.Contains($"⊢ Extracted.method0.code.length = {codeLength}", StringComparison.Ordinal))
    throw new InvalidOperationException("Editing the proof in place did not show its goal: " + goals);
Console.WriteLine("PASS the proof checks in place against the generated Extracted and shows its goals");

// A helper the package gains after the first run states a fact about the method body, not just its identity.
var body = Path.Combine(package, "Client", "Body.lean");
void WriteBody(int length) => File.WriteAllText(body, $"""
import Extracted
namespace Client
theorem codeLength : Extracted.method0.code.length = {length} := by decide
end Client
""");
WriteBody(codeLength);
File.WriteAllText(proof, File.ReadAllText(proof).Replace("import Client.Support\n",
    "import Client.Support\nimport Client.Body\n", StringComparison.Ordinal));
var compiled = Path.Combine(framework, ".lake", "build", "lib", "lean", "Extracted.olean");
var compiledAt = File.GetLastWriteTimeUtc(compiled);
var editorAt = Directory.EnumerateFiles(editor).ToDictionary(path => path, File.GetLastWriteTimeUtc);
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
// Lake traces the helper through Extracted, so its proof about the old body fails without any Lean edit.
var stale = CheckProof();
var checkTime = clock.Elapsed;
if (refreshed.Code != 0 || stale.Code == 0 || !stale.Output.Contains("Client/Body.lean", StringComparison.Ordinal))
    throw new InvalidOperationException("A rebuilt assembly did not reach the proof's helper after a refresh: " +
        refreshed.Output + "\n" + stale.Output);
var changedLength = CodeLength();
if (changedLength == codeLength)
    throw new InvalidOperationException("The refreshed extraction kept the old method body.");
WriteBody(changedLength);
File.WriteAllText(proof, File.ReadAllText(proof).Replace($"= {codeLength} :=", $"= {changedLength} :=",
    StringComparison.Ordinal));
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
File.AppendAllText(Path.Combine(editor, "Extracted.lean"), "\ntheorem forged : False := sorry\n");
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

var pdb = Path.ChangeExtension(assembly, ".pdb");
var savedPdb = File.ReadAllBytes(pdb);
try
{
    File.Delete(pdb);
    Run(command);
    var withoutSymbols = CheckProof();
    if (File.Exists(Path.Combine(editor, "ExtractedSymbols.lean")) || withoutSymbols.Code == 0 ||
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
try { Reject(command, "reserved for the selected extraction"); }
finally { File.Delete(shadow); }
string[] otherProfileCommand = [.. command];
otherProfileCommand[Array.IndexOf(otherProfileCommand, "scalar")] = "arm64-advsimd";
var otherProfile = Run(otherProfileCommand);
if (!otherProfile.Contains("Replaced " + method + " (scalar)", StringComparison.Ordinal))
    throw new InvalidOperationException("Replacing the package's extraction was not reported: " + otherProfile);
Run(command);
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
Console.WriteLine("PASS reserved sources, other frameworks and moved dependency revisions are rejected; " +
    "a replaced selection is reported");

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
    File.WriteAllText(scratchProof, """
        import Extracted
        theorem scratch : Extracted.program.length = 1 := rfl
        #print axioms scratch
        """);
    string[] open = [.. cli, "workspace", assembly, method, "--profile", "scalar", "--proof", scratchProof,
        "--assume-initialized", initializedType];
    var opened = Run(open);
    if (!opened.Contains("Created a Lake package beside the proof", StringComparison.Ordinal) ||
        !File.Exists(Path.Combine(standalone, "lakefile.toml")))
        throw new InvalidOperationException("A standalone proof did not get a package beside it: " + opened);
    if (Directory.EnumerateDirectories(standalone, ".git", SearchOption.AllDirectories).Any())
        throw new InvalidOperationException("A standalone workspace created a git repository.");
    Run(["lake", "lean", scratchProof], standalone);
    // The framework copy is required by path, which certification never accepts in place of a pinned revision.
    var unpinned = Execute([.. cli, "verify", output, "--proof", scratchProof, "--proof-root", standalone,
        "--theorem", "scratch"]);
    if (unpinned.Code == 0 || !unpinned.Output.Contains("must be git packages pinned", StringComparison.Ordinal))
        throw new InvalidOperationException("Verification accepted an unpinned framework dependency: " +
            unpinned.Output);
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
    "is edited in place and refreshes on re-run");
