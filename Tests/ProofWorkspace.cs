#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

string[] cli = ["dotnet", ExtractorPath];
var root = At("artifacts/ProofWorkspace-" + Guid.NewGuid().ToString("N"));
var consumer = Path.Combine(root, "Consumer");
var package = Path.Combine(root, "Package");
var workspace = Path.Combine(root, "Workspace");
Directory.CreateDirectory(Path.Combine(package, "Client"));
const string consumerRevision = "00fcecf53e22b5c9090052779e14b3ba246fb117";
const string method = "Nethermind.Int256.UInt256::get_IsZeroOrOne()";
const string initializedType = "Nethermind.Int256.UInt256";
Run(["git", "init", consumer]);
Run(["git", "remote", "add", "origin", "https://github.com/NethermindEth/int256.git"], consumer);
Run(["git", "fetch", "--depth", "1", "origin", consumerRevision], consumer);
Run(["git", "checkout", "--detach", "FETCH_HEAD"], consumer);
Console.WriteLine("Building pinned Nethermind.Int256 consumer " + consumerRevision);
Run(["dotnet", "build", Path.Combine(consumer, "src", "Nethermind.Int256", "Nethermind.Int256.csproj"),
    "-c", "Release"]);
var assembly = Path.Combine(consumer, "src", "artifacts", "bin", "Nethermind.Int256", "release",
    "Nethermind.Int256.dll");
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
    "System.Boolean Nethermind.Int256.UInt256::get_IsZeroOrOne()" := rfl
#print axioms methodCount
#print axioms methodIdentity
end Client
""");
var proof = Path.Combine(package, "Proof.lean");
File.WriteAllText(proof, """
import Client.Support
namespace WorkspaceProof
theorem selectedMethod : Extracted.program.length = 1 ∧ Extracted.method0Signature =
    "System.Boolean Nethermind.Int256.UInt256::get_IsZeroOrOne()" :=
  ⟨Client.methodCount, Client.methodIdentity⟩
#print axioms selectedMethod
end WorkspaceProof
""");
Run(["lake", "update"], package);
Console.WriteLine("Checking the real UInt256 editor workspace and preserving proof edits");
string[] command = [.. cli, "workspace", assembly, method,
    "--profile", "scalar", "--proof", proof, "--assume-initialized", initializedType, "--output", workspace];
var created = Run(command);
var editorProof = Path.Combine(workspace, "LeanCILProofWorkspace.lean");
if (!created.Contains("Editor checking is not a certificate", StringComparison.Ordinal) || Sha(editorProof) != Sha(proof))
    throw new InvalidOperationException("Workspace did not preserve the selected proof or state its trust boundary.");
var manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(workspace, "leancil-workspace.json")));
if (!manifest.GetProperty("EditorOnly").GetBoolean() || Directory.EnumerateFiles(workspace, "verified.json", SearchOption.AllDirectories).Any())
    throw new InvalidOperationException("An editor workspace must never publish a certificate.");
Run(["lake", "build", "+LeanCILProofWorkspace:olean"], workspace);
File.AppendAllText(editorProof, "\ntheorem editorChange : True := True.intro\n#print axioms editorChange\n");
var changedProof = Sha(editorProof);
Run(command);
if (Sha(editorProof) != changedProof) throw new InvalidOperationException("Reopening a workspace overwrote proof edits.");
Run(["lake", "build", "+LeanCILProofWorkspace:olean"], workspace);
File.Copy(editorProof, proof, true);
Console.WriteLine("Verifying the unchanged editor proof through fresh hermetic verification");
var output = Path.Combine(root, "Verification");
Run([.. cli, "extract", assembly, method, output, "scalar", "--assume-initialized", initializedType]);
Run([.. cli, "verify", output, "--proof", proof, "--proof-root", package,
    "--theorem", "WorkspaceProof.selectedMethod", "--fresh"]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("ExtractionAudit.valid", StringComparison.Ordinal) ||
    report.GetProperty("libraryBuild").GetString() == "consumer-proof-cache")
    throw new InvalidOperationException("Workspace proof did not pass ordinary fresh extraction audit and hermetic verification.");
Console.WriteLine("PASS real pinned UInt256 workspace, transitive symbols import, editable proof and fresh certification");

void Reject(string[] arguments, string marker)
{
    var result = Execute(arguments);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal) || Sha(editorProof) != changedProof)
        throw new InvalidOperationException("Expected explicit stale workspace rejection without proof loss: " + result.Output);
}

File.WriteAllText(proof, File.ReadAllText(editorProof).Replace(
    "\ntheorem editorChange : True := True.intro\n#print axioms editorChange\n", "", StringComparison.Ordinal));
Run(command);
foreach (var (path, name) in new[]
{
    (assembly, "assembly"), (Path.ChangeExtension(assembly, ".pdb"), "PDB"),
    (helper, "consumer helper"), (Path.Combine(package, "lean-toolchain"), "toolchain"),
    (Path.Combine(package, ".lake", "packages", "leancil", "lakefile.toml"), "dependency source")
})
{
    var original = File.ReadAllBytes(path);
    try
    {
        File.WriteAllBytes(path, [.. original, 32]);
        Reject(command, "Stale editor workspace");
    }
    finally { File.WriteAllBytes(path, original); }
}
string[] wrongProfile = [.. command];
wrongProfile[Array.IndexOf(wrongProfile, "scalar")] = "arm64-armbase";
Reject(wrongProfile, "Stale editor workspace");
var pdb = Path.ChangeExtension(assembly, ".pdb");
var savedPdb = File.ReadAllBytes(pdb);
try
{
    File.Delete(pdb);
    Reject(command, "Stale editor workspace");
    var stripped = Path.Combine(root, "NoPdbWorkspace");
    string[] strippedCommand = [.. command];
    strippedCommand[^1] = stripped;
    Run(strippedCommand);
    if (Directory.EnumerateFiles(stripped, "ExtractedSymbols.lean", SearchOption.AllDirectories).Any())
        throw new InvalidOperationException("A missing PDB left stale editor symbols.");
    File.WriteAllBytes(pdb, savedPdb);
    Reject(strippedCommand, "Stale editor workspace");
}
finally { File.WriteAllBytes(pdb, savedPdb); }
Console.WriteLine("PASS assembly, profile, PDB presence/content, toolchain and transitive source changes reject stale workspaces");

// Exercise the framework actually used by the tool without mutating the running checkout.
var toolCopy = Path.Combine(root, "Tool");
var toolSource = Path.GetDirectoryName(ExtractorPath)!;
foreach (var source in Directory.EnumerateFiles(toolSource, "*", SearchOption.AllDirectories))
{
    var destination = Path.Combine(toolCopy, Path.GetRelativePath(toolSource, source));
    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
    File.Copy(source, destination);
}
string[] copiedCommand = ["dotnet", Path.Combine(toolCopy, Path.GetFileName(ExtractorPath)), .. command[2..]];
Run(copiedCommand);
var copiedFramework = Path.Combine(toolCopy, "verification", "CIL", "ProfileEquivalence.lean");
var frameworkBytes = File.ReadAllBytes(copiedFramework);
try
{
    var frameworkText = File.ReadAllText(copiedFramework);
    var otherLineEnding = frameworkText.Contains("\r\n", StringComparison.Ordinal) ? "\n" : "\r\n";
    File.WriteAllText(copiedFramework, frameworkText.ReplaceLineEndings(otherLineEnding));
    Reject(copiedCommand, "Stale editor workspace");
    File.Delete(copiedFramework);
    Reject(copiedCommand, "Stale editor workspace");
}
finally { File.WriteAllBytes(copiedFramework, frameworkBytes); }
Run(copiedCommand);
Console.WriteLine("PASS exact tool framework bytes and removed tool sources reject stale workspaces");

var sourceDependency = Path.Combine(package, ".lake", "packages", "leancil");
var olderRevision = Run(["git", "rev-parse", "HEAD^"], sourceDependency).Trim();
try
{
    Run(["git", "update-ref", "HEAD", olderRevision], sourceDependency);
    Reject(command, "dependency revision differs");
}
finally { Run(["git", "update-ref", "HEAD", revision], sourceDependency); }
Console.WriteLine("PASS a dependency checkout revision inconsistent with its manifest is rejected");

var framework = Path.Combine(workspace, ".lake", "packages", "leancil");
foreach (var path in new[] { Path.Combine(framework, "Extracted.lean"), Path.Combine(framework, "ExtractedSymbols.lean"),
    Path.Combine(framework, "CIL", "Semantics.lean"), Path.Combine(workspace, "lakefile.toml"), Path.Combine(workspace, "lean-toolchain") })
{
    var original = File.ReadAllText(path);
    try
    {
        File.AppendAllText(path, "\n ");
        Reject(command, "generated or support source changed");
    }
    finally { File.WriteAllText(path, original); }
}
var shadow = Path.Combine(workspace, "Extracted.lean");
try
{
    File.WriteAllText(shadow, "def forged : Nat := 0\n");
    Reject(command, "unrecorded source");
}
finally { File.Delete(shadow); }
Run(command);
Console.WriteLine("PASS modified generated modules, framework/configuration and added shadow sources are rejected; proof edits remain");
