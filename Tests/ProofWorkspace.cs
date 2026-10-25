#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

string[] cli = ["dotnet", ExtractorPath];
string root = At("artifacts/ProofWorkspace-" + Guid.NewGuid().ToString("N"));
string consumer = Path.Combine(root, "Consumer");
string package = Path.Combine(root, "Package");
string workspace = Path.Combine(root, "Workspace");
Directory.CreateDirectory(Path.Combine(package, "Client"));
const string consumerRevision = "00fcecf53e22b5c9090052779e14b3ba246fb117";
const string method = "Nethermind.Int256.UInt256::get_IsZeroOrOne()";
const string initializedType = "Nethermind.Int256.UInt256";
Run(["git", "init", consumer]);
Run(["git", "remote", "add", "origin", "https://github.com/NethermindEth/int256.git"], consumer);
Run(["git", "fetch", "--depth", "1", "origin", consumerRevision], consumer);
Run(["git", "checkout", "--detach", "FETCH_HEAD"], consumer);
Run(["dotnet", "build", Path.Combine(consumer, "src", "Nethermind.Int256", "Nethermind.Int256.csproj"),
    "-c", "Release"]);
string assembly = Path.Combine(consumer, "src", "artifacts", "bin", "Nethermind.Int256", "release",
    "Nethermind.Int256.dll");
string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"consumer\"\n[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) +
    "\nrev = \"" + revision + "\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
string helper = Path.Combine(package, "Client", "Support.lean");
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
string proof = Path.Combine(package, "Proof.lean");
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
string[] command = [.. cli, "workspace", assembly, method,
    "--profile", "scalar", "--proof", proof, "--assume-initialized", initializedType, "--output", workspace];
string created = Run(command);
string editorProof = Path.Combine(workspace, "LeanCILProofWorkspace.lean");
if (!created.Contains("Editor checking is not a certificate", StringComparison.Ordinal) || Sha(editorProof) != Sha(proof))
    throw new InvalidOperationException("Workspace did not preserve the selected proof or state its trust boundary.");
JsonElement manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(workspace, "leancil-workspace.json")));
if (!manifest.GetProperty("EditorOnly").GetBoolean() || Directory.EnumerateFiles(workspace, "verified.json", SearchOption.AllDirectories).Any())
    throw new InvalidOperationException("An editor workspace must never publish a certificate.");
Run(["lake", "build", "+LeanCILProofWorkspace:olean"], workspace);
File.AppendAllText(editorProof, "\ntheorem editorChange : True := True.intro\n#print axioms editorChange\n");
string changedProof = Sha(editorProof);
Run(command);
if (Sha(editorProof) != changedProof) throw new InvalidOperationException("Reopening a workspace overwrote proof edits.");
Run(["lake", "build", "+LeanCILProofWorkspace:olean"], workspace);
File.Copy(editorProof, proof, true);
string output = Path.Combine(root, "Verification");
Run([.. cli, "extract", assembly, method, output, "scalar", "--assume-initialized", initializedType]);
Run([.. cli, "verify", output, "--proof", proof, "--proof-root", package,
    "--theorem", "WorkspaceProof.selectedMethod", "--fresh"]);
JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("ExtractionAudit.valid", StringComparison.Ordinal) ||
    report.GetProperty("libraryBuild").GetString() == "consumer-proof-cache")
    throw new InvalidOperationException("Workspace proof did not pass ordinary fresh extraction audit and hermetic verification.");
Console.WriteLine("PASS real pinned UInt256 workspace, transitive symbols import, editable proof and fresh certification");

void Reject(string[] arguments, string marker)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute(arguments);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal) || Sha(editorProof) != changedProof)
        throw new InvalidOperationException("Expected explicit stale workspace rejection without proof loss: " + result.Output);
}

File.WriteAllText(proof, File.ReadAllText(editorProof).Replace(
    "\ntheorem editorChange : True := True.intro\n#print axioms editorChange\n", "", StringComparison.Ordinal));
Run(command);
foreach ((string path, string name) in new[]
{
    (assembly, "assembly"), (Path.ChangeExtension(assembly, ".pdb"), "PDB"),
    (helper, "consumer helper"), (Path.Combine(package, "lean-toolchain"), "toolchain"),
    (Path.Combine(package, ".lake", "packages", "leancil", "lakefile.toml"), "dependency source")
})
{
    byte[] original = File.ReadAllBytes(path);
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
string pdb = Path.ChangeExtension(assembly, ".pdb");
byte[] savedPdb = File.ReadAllBytes(pdb);
try
{
    File.Delete(pdb);
    Reject(command, "Stale editor workspace");
    string stripped = Path.Combine(root, "NoPdbWorkspace");
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

string sourceDependency = Path.Combine(package, ".lake", "packages", "leancil");
string olderRevision = Run(["git", "rev-parse", "HEAD^"], sourceDependency).Trim();
try
{
    Run(["git", "update-ref", "HEAD", olderRevision], sourceDependency);
    Reject(command, "dependency revision differs");
}
finally { Run(["git", "update-ref", "HEAD", revision], sourceDependency); }
Console.WriteLine("PASS a dependency checkout revision inconsistent with its manifest is rejected");

string framework = Path.Combine(workspace, ".lake", "packages", "leancil");
foreach (string path in new[] { Path.Combine(framework, "Extracted.lean"), Path.Combine(framework, "ExtractedSymbols.lean"),
    Path.Combine(framework, "CIL", "Semantics.lean"), Path.Combine(workspace, "lakefile.toml"), Path.Combine(workspace, "lean-toolchain") })
{
    string original = File.ReadAllText(path);
    try
    {
        File.AppendAllText(path, "\n ");
        Reject(command, "generated or support source changed");
    }
    finally { File.WriteAllText(path, original); }
}
string shadow = Path.Combine(workspace, "Extracted.lean");
try
{
    File.WriteAllText(shadow, "def forged : Nat := 0\n");
    Reject(command, "unrecorded source");
}
finally { File.Delete(shadow); }
Run(command);
Console.WriteLine("PASS modified generated modules, framework/configuration and added shadow sources are rejected; proof edits remain");
