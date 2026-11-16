using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
    /// <summary>Joint proof and image binding verification with explicit consumer digests.</summary>
    static void CheckDeepBinding(string root, string[] cli, string extraction, string app, string lib,
        string libName, string[] verify, bool controlsOnly = false, bool finalOnly = false)
    {
        var manifest = Path.Combine(root, "deep-inputs.sha256");
        File.WriteAllText(manifest, Sha(app) + "  " + Path.GetRelativePath(root, app) + "\n" +
            Sha(lib) + "  " + Path.GetRelativePath(root, lib) + "\n");
        if (!controlsOnly && !finalOnly)
        {
            var result = Execute([.. verify, "--deep-checks", manifest, "--format", "json"]);
            if (result.Code != 0) throw new InvalidOperationException(result.Output);
            var report = JsonSerializer.Deserialize<JsonElement>(result.Stdout);
            var binding = report.GetProperty("binding");
            if (binding.GetProperty("mode").GetString() != "deep" ||
                binding.GetProperty("facts").GetArrayLength() != 12 ||
                binding.GetProperty("images").GetArrayLength() != 2 ||
                binding.GetProperty("facts").EnumerateArray().Count(fact =>
                    fact.GetProperty("status").GetString() == "reconfirmed") != 2)
                throw new InvalidOperationException("Unexpected joint binding report: " + result.Stdout);
            Console.WriteLine("PASS joint CLI verification reports image digests and all twelve facts");
        }
        var inputs = DeepCheckInputs.Read(manifest);
        var identity = ExtractionIdentity.Read(extraction);
        var pins = inputs.MatchPins(identity.Root);
        var images = pins.Select(pin => new BindingImagePin(pin.Identity, pin.Image.Digest,
            pin.Image.Bytes.ToArray())).ToArray();
        var reference = images.Single(image => image.Identity.Split(',')[0] == libName);
        var application = images.Single(image => image != reference);
        var proof = verify[Array.IndexOf(verify, "--proof") + 1];
        var theorem = verify[Array.IndexOf(verify, "--theorem") + 1];
        var methods = identity.Root.GetProperty("methods").GetArrayLength();
        if (methods < 2) throw new InvalidOperationException("The binding fixture requires two method pages");

        var sources = Path.Combine(root, "binding-sources");
        CopyBindingSources(sources);
        var sourceKey = BindingSourcesKey(sources);
        File.AppendAllText(Path.Combine(sources, "StrictBinding", "Bind.lean"), "\n-- changed\n");
        if (sourceKey != BindingSourcesKey(Root) || sourceKey == BindingSourcesKey(sources))
            throw new InvalidOperationException("Binding source key does not identify its sources");
        using Program checking = new() { freshProofs = true };

        void Mutation(string name, string module, Func<string, string> edit, string diagnostic,
            BindingFact? rejectedFact = null, bool succeeds = false, string? rejectedStage = null)
        {
            if (controlsOnly && !succeeds) return;
            if (finalOnly && name is not ("false later body page" or "wrong pinned identity theorem")) return;
            DeepCheckRun run = new(inputs);
            var mutated = false;
            string stage = "proof selection";
            Exception? rejected = null;
            try
            {
                checking.Verify(app, identity.Root.GetProperty("assemblyIdentity").GetString()!,
                    identity.Root.GetProperty("entry").GetString()!, proof, extraction, theorem: theorem,
                    existingArtifacts: true, deepChecks: inputs, deepRun: run, stage: next =>
                    {
                        stage = next;
                        if (next != "deep-check sources") return;
                        var directory = Directory.EnumerateDirectories(extraction, "proof-*").Single();
                        var bodies = ModuleSource(directory, BodiesModule);
                        File.WriteAllText(bodies, PagedFactModuleSource(BindingFact.BodyBytes, methods, 1));
                        var path = ModuleSource(directory, module);
                        var source = File.ReadAllText(path);
                        var changed = edit(source);
                        if (!succeeds && changed == source)
                            throw new InvalidOperationException("Mutation changed nothing: " + name);
                        File.WriteAllText(path, changed);
                        mutated = true;
                    });
            }
            catch (Exception error) { rejected = error; }
            if (succeeds)
            {
                if (!mutated || rejected is not null || !File.Exists(Path.Combine(extraction, "verified.json")))
                    throw new InvalidOperationException("Valid method pages failed: " + rejected);
                Console.WriteLine("PASS valid method pages in joint verification");
                return;
            }
            if (!mutated || rejected is null || !rejected.Message.Contains(diagnostic, StringComparison.Ordinal))
                throw new InvalidOperationException(name + " was not rejected as expected: " + rejected);
            if (rejectedStage is not null && stage != rejectedStage)
                throw new InvalidOperationException(name + " failed during " + stage + ", expected " + rejectedStage);
            if (File.Exists(Path.Combine(extraction, "verified.json")))
                throw new InvalidOperationException(name + " retained a successful certificate");
            var failed = run.Attempt!.Failure(stage, rejected.Message);
            if (rejectedFact is { } fact && !failed.facts.Any(item =>
                item.id == JsonSerializer.SerializeToElement(fact).GetString() &&
                item.status == FailureReports.BindingFailureStatus.Failed))
                throw new InvalidOperationException(name + " lost its named audit rejection");
            Console.WriteLine("PASS " + name);
        }

        Mutation("valid method pages", BodiesModule, source => source, "", succeeds: true);
        Mutation("changed second page", BodiesModule, source => source.Replace(
            "Extracted.methodEvidence) 1 1)", "Extracted.methodEvidence) 1 0)", StringComparison.Ordinal),
            "Deep-check module build failed");
        Mutation("changed image digit", reference.Module, source => FirstChunkDigit().Replace(source,
            match => "  0x" + match.Groups[1].Value + (match.Groups[2].Value == "0" ? "1" : "0"), 1),
            "replay");
        Mutation("body theorem about other evidence", BodiesModule, source => ReplaceBodies(source,
            "theorem bodies : StrictBinding.BodiesBound images [] := by decide +kernel"),
            "Theorem statement mismatch", BindingFact.BodyBytes);
        const string statement = "StrictBinding.BodiesBound images Extracted.methodEvidence";
        Mutation("body theorem with extra axiom", BodiesModule, source => ReplaceBodies(source,
            $"axiom cheat : {statement}\ntheorem bodies : {statement} := cheat"),
            "axiom", BindingFact.BodyBytes);
        Mutation("digest of other bytes", application.Module,
            _ => ImageModuleSource(application with { Bytes = reference.Bytes }), "replay");
        Mutation("digest theorem about another constant", reference.Module, source => source
            .Replace("import StrictBinding.Sha256", "import StrictBinding.Sha256\nimport " + application.Module,
                StringComparison.Ordinal)
            .Replace("theorem digest : StrictBinding.DigestIs image ",
                "theorem digest : StrictBinding.DigestIs " + application.Module + ".image ", StringComparison.Ordinal),
            "Deep-check module build failed");
        Mutation("false later body page", BodiesModule, source => source
            .Replace("import BindingAudit.Images", "import Lean\nimport BindingAudit.Images", StringComparison.Ordinal)
            .Replace("theorem page1 :", "theorem page1_valid :", StringComparison.Ordinal)
            .Replace(BodiesDocstring, """
                set_option debug.skipKernelTC true in
                run_cmd Lean.Elab.Command.liftCoreM do
                  let valid <- Lean.getConstInfo `BindingAudit.Bodies.page1_valid
                  Lean.addDecl (.thmDecl {
                    name := `BindingAudit.Bodies.page1, levelParams := [], type := valid.type,
                    value := Lean.mkConst ``True.intro })

                """ + "\n" + BodiesDocstring, StringComparison.Ordinal), "BindingAudit.Bodies.page1",
            BindingFact.BodyBytes, rejectedStage: "replay diagnostics");
        Mutation("wrong pinned identity theorem", ImagesModule, source => source.Replace(
            "theorem images_eq : images =",
            "theorem images_eq : images = images := rfl\ntheorem images_unused : images =", StringComparison.Ordinal),
            "Theorem statement mismatch");
    }
    /// <summary>The docstring that opens the `bodies` theorem, the last declaration of the bodies module.</summary>
    const string BodiesDocstring = "/-- The method bodies of `Extracted.methodEvidence`";

    /// <summary>The module with its `bodies` theorem, which closes the module, replaced by other text.</summary>
    static string ReplaceBodies(string source, string replacement) =>
        source[..source.IndexOf(BodiesDocstring, StringComparison.Ordinal)] + replacement + "\n\nend BindingAudit\n";

    [GeneratedRegex(@"(?m)^  0x([0-9a-f]{40})([0-9a-f])")]
    private static partial Regex FirstChunkDigit();

}
