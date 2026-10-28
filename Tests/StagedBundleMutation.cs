using System.Text.Json;
using System.Text.Json.Nodes;

partial class Program
{
    static void CheckStagedBundleMutation(string fixture)
    {
        var root = Path.Combine(fixture, "StagedBundleMutation-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        string[] cli = ["dotnet", ExtractorPath];
        var a = Path.Combine(fixture, "A", "bin", "ImportFixture.A.dll");
        var b = Path.Combine(fixture, "B", "bin", "ImportFixture.B.dll");
        var app = Path.Combine(fixture, "App", "bin", "ImportFixture.App.dll");
        var token = "later-staged-proof-" + Guid.NewGuid().ToString("N");
        var marker = Path.Combine(root, "mutated-path.txt");
        string Rebundle(string name, string proofName, string suffix)
        {
            var originalSidecar = Path.Combine(fixture, name, "bin", "ImportFixture." + name + ".leancil.contracts");
            var contract = JsonNode.Parse(File.ReadAllText(originalSidecar))!.AsObject();
            var original = Path.GetFullPath(contract["fullVerificationLocator"]!.GetValue<string>(),
                Path.GetDirectoryName(originalSidecar)!);
            var staging = Path.Combine(root, "rebundle-" + name);
            CopyTree(original, staging);
            var proof = Directory.EnumerateFiles(staging, proofName, SearchOption.AllDirectories).Single();
            File.AppendAllText(proof, suffix);
            var inventory = JsonNode.Parse(File.ReadAllText(Path.Combine(staging, "bundle.json")))!.AsObject();
            inventory["files"]![Path.GetRelativePath(staging, proof).Replace('\\', '/')] = Sha(proof);
            File.WriteAllText(Path.Combine(staging, "bundle.json"), inventory.ToJsonString());
            var bundle = Path.Combine(root, Sha(Path.Combine(staging, "bundle.json")));
            Directory.Move(staging, bundle);
            contract["fullVerificationLocator"] = bundle;
            var sidecar = Path.Combine(root, "ImportFixture." + name + ".leancil.contracts");
            File.WriteAllText(sidecar, contract.ToJsonString());
            return sidecar;
        }
        var aSidecar = Rebundle("A", "Conditional.lean", "\n-- " + token + "\n");
        var mutation = $$"""

            open Lean Elab Command in
            run_cmd do
              for entry in ← (System.FilePath.mk {{JsonSerializer.Serialize(Path.GetTempPath())}}).readDir do
                if entry.fileName.startsWith "leancil-full-" then
                  let target := entry.path / "staging" / "bundle-0" / "consumer" / "Conditional.lean"
                  if ← target.pathExists then
                    let source ← IO.FS.readFile target
                    if (source.splitOn {{JsonSerializer.Serialize(token)}}).length > 1 then
                      IO.FS.writeFile target (source ++ "\n-- changed by the earlier dependency build\n")
                      IO.FS.writeFile {{JsonSerializer.Serialize(marker)}} target.toString
            """;
        var bSidecar = Rebundle("B", "BProof.lean", mutation);
        string[] Import(string sidecar, string assembly, string name)
        {
            var contract = JsonNode.Parse(File.ReadAllText(sidecar))!;
            return ["--import", sidecar, "--import-implementation", name + "=" + assembly,
                "--import-sha256", name + "=" + Sha(assembly),
                "--import-interface-sha256", name + "=" + contract["interfaceDigest"]!.GetValue<string>()];
        }
        var artifact = Path.Combine(root, "App");
        Run([.. cli, "extract", app, "ImportFixture.Application::Entry(ulong)", artifact,
            .. Import(aSidecar, a, "ImportFixture.A"), .. Import(bSidecar, b, "ImportFixture.B")]);
        var proofRoot = Path.Combine(fixture, "AppProofPackage");
        var rejected = Execute([.. cli, "verify", artifact, "--proof", Path.Combine(proofRoot, "Conditional.lean"),
            "--proof-root", proofRoot, "--force-full-verify"]);
        if (!File.Exists(marker))
            throw new InvalidOperationException("The dependency did not mutate the later staged proof: " + rejected.Output);
        var target = File.ReadAllText(marker);
        var staging = Path.GetDirectoryName(Path.GetDirectoryName(target)!)!;
        if (rejected.Code != 1 || !rejected.Output.Contains(
                "Full-verification staged bundle changed before its build: " + staging, StringComparison.Ordinal) ||
            File.Exists(Path.Combine(artifact, "verified.json")))
            throw new InvalidOperationException(
                "A changed later staged bundle was not rejected before its build: " + rejected.Output);
        Console.WriteLine("PASS B's actual producer build changes staged A, which rejects before A's proof build");
    }
}
