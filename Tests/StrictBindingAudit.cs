using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
    /// <summary>
    /// The strict binding audit of an extraction with one pinned reference: the command reconfirms every digest and
    /// the body locations and reports the other facts as not covered; wrong digests stop it early; it changes nothing
    /// the default flow reads; and modules that state something other than what the driver expects, or that were
    /// built from other bytes than the stated digest names, are never reported as reconfirmed.
    /// </summary>
    static void CheckBindingAudit(string root, string[] cli, string extraction, string app, string lib,
        string libName, string[] verify)
    {
        string appSha = Sha(app), libSha = Sha(lib);
        string output = Path.Combine(root, "binding-audit"), results = Path.Combine(root, "binding-report.json");
        string[] audit = [.. cli, "audit-binding", extraction];
        string verifiedBefore = Run(verify);
        string artifactsBefore = TreeDigest(extraction);

        // A wrong digest of either file is refused before any Lean module is built.
        MultiAssemblyFixture.Rejected("wrong stated digest", "the stated digest is",
            [.. audit, "--sha256", Flip(appSha), "--output", output]);
        MultiAssemblyFixture.Rejected("wrong stated reference digest", "the stated digest is",
            [.. audit, "--sha256", appSha, "--reference-sha256", libName + "=" + Flip(libSha), "--output", output]);
        MultiAssemblyFixture.Rejected("reference that was not pinned", "did not pin",
            [.. audit, "--sha256", appSha, "--reference-sha256", "Other=" + libSha, "--output", output]);
        MultiAssemblyFixture.Rejected("unknown required item", "Unknown item in --require",
            [.. audit, "--sha256", appSha, "--require", "nothing", "--output", output]);
        if (Directory.Exists(output))
            throw new InvalidOperationException("A refused audit wrote its output directory");

        // The command reconfirms what it covers, labels the digest sources and lists everything else as not covered.
        var run = Execute([.. audit, "--sha256", appSha, "--reference-sha256", libName + "=" + libSha,
            "--require", "body-locations", "--output", output, "--results", results]);
        if (run.Code != 0 || !run.Stdout.StartsWith("Valid: strict binding audit of ", StringComparison.Ordinal))
            throw new InvalidOperationException("The strict binding audit did not pass: " + run.Output);
        using var report = JsonDocument.Parse(File.ReadAllText(results));
        var items = report.RootElement.GetProperty("items").EnumerateArray()
            .ToDictionary(item => item.GetProperty("id").GetString()!,
                item => item.GetProperty("status").GetString()!);
        string[] covered = ["digests:" + libName, "digests:MultiFixture.App", "body-locations"];
        if (covered.Any(id => items.GetValueOrDefault(id) != "reconfirmed") ||
            items.Count != covered.Length + UncoveredBindingFacts.Length ||
            UncoveredBindingFacts.Any(fact => items.GetValueOrDefault(fact.Id) != "not covered"))
            throw new InvalidOperationException("Unexpected audit items: " +
                string.Join(", ", items.Select(pair => $"{pair.Key}={pair.Value}")));
        var sources = report.RootElement.GetProperty("images").EnumerateArray()
            .Select(image => image.GetProperty("source").GetString());
        if (sources.Any(source => source != "stated")) throw new InvalidOperationException("Both digests were stated");
        var sourcesKey = report.RootElement.GetProperty("strictBindingSourcesSha256").GetString();
        var toolchain = report.RootElement.GetProperty("leanToolchain").GetString();
        var leanVersion = report.RootElement.GetProperty("leanVersion").GetString()!;
        if (sourcesKey != BindingSourcesKey(Root) || toolchain != File.ReadAllText(At("lean-toolchain")).Trim() ||
            !leanVersion.StartsWith("Lean (version ", StringComparison.Ordinal))
            throw new InvalidOperationException("The report names the wrong sources or Lean: " + run.Stdout);
        Console.WriteLine("PASS strict binding audit reconfirmed both digests and the body locations");
        Console.WriteLine("PASS the report names the hash of the built StrictBinding sources and the Lean that ran");

        // The report in docs/CLI.md has the lines the command prints, and every not covered line is word for word.
        var printed = run.Stdout.ReplaceLineEndings("\n").Split('\n');
        foreach (var line in DocumentedBindingReport())
        {
            var stable = line.Contains(": not covered (", StringComparison.Ordinal) ? line
                : line.StartsWith("  Image ", StringComparison.Ordinal) ? "  Image "
                : line.StartsWith("  SHA-256 digest of ", StringComparison.Ordinal) ? "  SHA-256 digest of "
                : line[..(line.IndexOf(':') + 1)];
            if (!printed.Any(real => real.StartsWith(stable, StringComparison.Ordinal)))
                throw new InvalidOperationException("docs/CLI.md shows a line the command does not print: " + line);
        }
        Console.WriteLine("PASS the documented report has the lines the command prints");

        // An unstated reference digest is proved but not reconfirmed: the bodies in that image have the same status,
        // and requiring the bodies alone exits 1 where the stated run above exits 0.
        var matchedOutput = Path.Combine(root, "binding-matched");
        var matchedResults = Path.Combine(root, "binding-matched.json");
        var matchedRun = Execute([.. audit, "--sha256", appSha, "--require", "body-locations",
            "--output", matchedOutput, "--results", matchedResults]);
        using var matchedReport = JsonDocument.Parse(File.ReadAllText(matchedResults));
        var matchedItems = matchedReport.RootElement.GetProperty("items").EnumerateArray()
            .ToDictionary(item => item.GetProperty("id").GetString()!,
                item => item.GetProperty("status").GetString()!);
        if (matchedRun.Code != 1 || matchedItems["body-locations"] != Matched ||
            matchedItems["digests:" + libName] != Matched || matchedItems["digests:MultiFixture.App"] != Reconfirmed ||
            !matchedRun.Stderr.Contains("PE container and method body locations is required but " + Matched,
                StringComparison.Ordinal))
            throw new InvalidOperationException("A recorded digest satisfied --require: " + matchedRun.Output);
        Console.WriteLine("PASS an unstated reference digest matches and fails --require body-locations");

        // The extraction directory, its check and its verification are the same after an audit.
        if (TreeDigest(extraction) != artifactsBefore || Directory.Exists(extraction + ".binding-audit") ||
            Run(verify) != verifiedBefore)
            throw new InvalidOperationException("The binding audit changed the extraction or its verification");
        Console.WriteLine("PASS the binding audit left the extraction and its verification unchanged");

        // A digest the extraction recorded but the caller did not state is labelled as such.
        var recorded = BindingPlanOf(extraction, null, appSha, new(), output);
        if (!recorded.Images.Select(image => image.Source).SequenceEqual(["stated", "recorded, not stated"]))
            throw new InvalidOperationException("The recorded reference digest was not labelled");
        // A digest the extraction recorded matches its pinned digest and never satisfies `--require digests`.
        var matched = DigestVerdict(recorded.Images[1], null);
        BindingReport recordedReport = new(extraction, "", [], [matched, DigestVerdict(recorded.Images[0], null)], [],
            "", "", "");
        if (matched.Status != Matched || BindingProblems(recordedReport, []).Length != 0 ||
            BindingProblems(recordedReport, ["digests"]).Length != 1)
            throw new InvalidOperationException("A recorded digest was reconfirmed, or ignored by --require");
        Console.WriteLine("PASS a recorded digest matches the pinned digest and fails --require digests");
        // The statements are defined by the StrictBinding sources, whose hash the report carries.
        var copy = Path.Combine(root, "binding-sources");
        CopyBindingSources(copy);
        var keyBefore = BindingSourcesKey(copy);
        File.AppendAllText(Path.Combine(copy, "StrictBinding", "Bind.lean"), "\n-- changed\n");
        if (keyBefore == BindingSourcesKey(copy) || keyBefore != BindingSourcesKey(Root))
            throw new InvalidOperationException("The sources key does not follow the StrictBinding sources");
        Console.WriteLine("PASS the report names the hash of the StrictBinding sources");

        // Two references with one simple name are refused before any file is read: the clone's file does not exist.
        var clashing = Path.Combine(root, "binding-clash");
        Directory.CreateDirectory(clashing);
        var identityJson = File.ReadAllText(Path.Combine(extraction, "identity.json"));
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(identityJson)!;
        var references = manifest["references"]!.AsArray();
        var clone = references[0]!.DeepClone();
        clone["path"] = "../missing/" + libName + ".dll";
        references.Add(clone);
        File.WriteAllText(Path.Combine(clashing, "identity.json"), manifest.ToJsonString());
        var refused = false;
        try { BindingPlanOf(clashing, null, appSha, new(), output); }
        catch (ArgumentException error) when (error.Message.Contains("are named", StringComparison.Ordinal))
        {
            refused = true;
        }
        if (!refused) throw new InvalidOperationException("Clashing simple names were accepted");
        Console.WriteLine("PASS two pinned assemblies with one simple name are refused");

        // --require turns a fact the audit does not cover into a failure, and a failed fact is always one.
        BindingItem[] sample =
        [
            new("digests:A", "Digest", "reconfirmed"), new("body-locations", "Bodies", "failed", Reason: "audit"),
            new("layouts", "Layouts", "not covered", Reason: "none")
        ];
        BindingReport synthetic = new(extraction, "", [], sample, [], "", "", "");
        if (BindingProblems(synthetic, []).Length != 1 || BindingProblems(synthetic, ["layouts"]).Length != 2 ||
            BindingProblems(synthetic, ["all"]).Length != 2)
            throw new InvalidOperationException("--require did not select the items it names");
        Console.WriteLine("PASS --require selects not covered items");

        CheckTamperedBindingModules(root, extraction, appSha, libName, libSha);
    }

    /// <summary>
    /// Generated modules rewritten before the build must be reported as failed, with the stage that caught them:
    /// an image whose bytes are not the digest's, a theorem about other evidence, a proof that adds an axiom and
    /// images pinned under an identity their files do not spell.
    /// </summary>
    static void CheckTamperedBindingModules(string root, string extraction, string appSha, string libName,
        string libSha)
    {
        using Program binding = new();
        // Pages of one method give the bodies module two pages; an extraction has several from 251 methods.
        var plan = BindingPlanOf(extraction, null, appSha, new() { [libName] = libSha },
            Path.Combine(root, "binding-tampered")) with { PageSize = 1 };
        if (plan.Methods < 2) throw new InvalidOperationException("The fixture needs two methods to have two pages");
        var lib = plan.Images.Single(image => image.Name == libName);
        var app = plan.Images.Single(image => image != lib);
        binding.BindingSession();

        BindingReport Tampered(string module, Func<string, string> edit)
        {
            binding.WriteBindingModules(plan);
            var path = ModuleSource(plan.Output, module);
            var original = File.ReadAllText(path);
            var changed = edit(original);
            if (changed == original) throw new InvalidOperationException("The tampering changed nothing in " + module);
            File.WriteAllText(path, changed);
            return binding.CheckBindingModules(plan);
        }
        BindingItem Item(BindingReport report, string id) => report.Items.Single(item => item.Id == id);
        List<string> mismatches = [];
        void Expect(string name, BindingItem item, string status, string reason)
        {
            if (item.Status != status || !(item.Reason ?? "").Contains(reason, StringComparison.Ordinal))
                mismatches.Add($"{name}: expected {item.Title} {status} with '{reason}', got {item.Status} " +
                    $"({item.Reason})");
        }

        // Untampered, the pages compose into the whole and every fact is reconfirmed.
        binding.WriteBindingModules(plan);
        var control = binding.CheckBindingModules(plan);
        if (control.Items.Any(item => item.Id != "body-locations" && item.Status == Failed) ||
            Item(control, "body-locations").Status != Reconfirmed ||
            !File.ReadAllText(ModuleSource(plan.Output, BodiesModule)).Contains("page1", StringComparison.Ordinal))
            throw new InvalidOperationException(
                "The paged bodies module was not reconfirmed: " + BindingText(control, false));
        Console.WriteLine("PASS a bodies module of several pages composes and is reconfirmed");

        // The second page names the first page's claims, so it does not have the type its place in the chain needs:
        // the composition `bodies` does not elaborate, and the error is at the line where that declaration starts.
        var secondPage = Tampered(BodiesModule, source => source.Replace("Extracted.methodEvidence) 1 1)",
            "Extracted.methodEvidence) 1 0)", StringComparison.Ordinal));
        var compositionLine = LineOf(ModuleSource(plan.Output, BodiesModule), BodiesDocstring);
        Expect("a changed second page", Item(secondPage, "body-locations"), "failed", "build: ");
        Expect("a changed second page", Item(secondPage, "body-locations"), "failed",
            $"Bodies.lean:{compositionLine}:");
        Console.WriteLine("PASS a bodies module whose second page is not its own is not reconfirmed");

        // One changed hexadecimal digit in the DOS header, which no check reads: it compiles unchecked and the kernel
        // rejects it on replay, and the body check, which reads other bytes, is not reconfirmed for want of a digest.
        var flipped = Tampered(lib.Module, source => FirstChunkDigit().Replace(source,
            match => "  0x" + match.Groups[1].Value + (match.Groups[2].Value == "0" ? "1" : "0"), 1));
        Expect("flipped digit", Item(flipped, "digests:" + libName), "failed", "replay: ");
        Expect("flipped digit", Item(flipped, "digests:" + libName), "failed", lib.Module + ".hash");
        Expect("flipped digit", Item(flipped, "digests:" + app.Name), "reconfirmed", "");
        Expect("flipped digit", Item(flipped, "body-locations"), "failed", "a digest is not reconfirmed");
        if (BindingProblems(flipped, []).Length == 0)
            throw new InvalidOperationException("A failed digest left the audit valid");
        Console.WriteLine(BindingText(flipped, false));
        Console.WriteLine("PASS a changed byte fails the digest on replay and the bodies are not reconfirmed");

        const string statement = "StrictBinding.BodiesBound images Extracted.methodEvidence";
        var wrongType = Tampered(BodiesModule, source => ReplaceBodies(source,
            "theorem bodies : StrictBinding.BodiesBound images [] := by decide +kernel"));
        Expect("theorem of the wrong type", Item(wrongType, "body-locations"), "failed",
            "audit: Theorem statement mismatch: BindingAudit.bodies");
        Expect("theorem of the wrong type", Item(wrongType, "digests:" + libName), "reconfirmed", "");
        Console.WriteLine("PASS a bodies theorem about other evidence is not reconfirmed");

        var extraAxiom = Tampered(BodiesModule, source => ReplaceBodies(source,
            $"axiom cheat : {statement}\ntheorem bodies : {statement} := cheat"));
        Expect("extra axiom", Item(extraAxiom, "body-locations"), "failed", "audit: ");
        Expect("extra axiom", Item(extraAxiom, "body-locations"), "failed", "cheat");
        Console.WriteLine("PASS a bodies theorem that depends on an extra axiom is not reconfirmed");

        // A module that is right about other bytes: its image and digest numeral belong to the other file, so
        // the numeral the driver derives from the command line rejects the digest theorem, and the kernel
        // rejects the page lemmas, which compile unchecked, on replay.
        var otherBytes = Tampered(app.Module,
            _ => ImageModuleSource(app with { Bytes = lib.Bytes }));
        Expect("a module about other bytes", Item(otherBytes, "digests:" + app.Name), "failed",
            "audit: Theorem statement mismatch: " + app.Theorem);
        Expect("a module about other bytes", Item(otherBytes, "body-locations"), "failed", "replay: ");
        Expect("a module about other bytes", Item(otherBytes, "body-locations"), "failed",
            "declaration 'BindingAudit.page");

        // A digest theorem about another image constant, with the right numeral for its own file.
        var otherConstant = Tampered(lib.Module, source => source
            .Replace("import StrictBinding.Sha256", "import StrictBinding.Sha256\nimport " + app.Module,
                StringComparison.Ordinal)
            .Replace("theorem digest : StrictBinding.DigestIs image ",
                "theorem digest : StrictBinding.DigestIs " + app.Module + ".image ", StringComparison.Ordinal));
        Expect("a digest about another image constant", Item(otherConstant, "digests:" + libName), "failed",
            "build: ");
        Expect("a digest about another image constant", Item(otherConstant, "digests:" + libName), "failed",
            "proved that the proposition");
        Console.WriteLine("PASS a self-consistent module for other bytes is not reconfirmed");

        // The library's method is on the second page. One changed digit in its body leaves the first page true, and
        // the kernel rejects the second page on replay, though it compiled unchecked.
        var body = StrictBindingFacts.Bodies(lib.Bytes).Single(item => item.Token == FirstMethodToken).Bytes.ToArray();
        var laterPage = Tampered(lib.Module, source => FlipDigitOfBytes(source, lib.Bytes, body));
        Expect("a false second page", Item(laterPage, "body-locations"), "failed", "replay: ");
        Expect("a false second page", Item(laterPage, "body-locations"), "failed", "declaration 'BindingAudit.page1");
        if ((Item(laterPage, "body-locations").Reason ?? "").Contains("BindingAudit.page0", StringComparison.Ordinal))
            mismatches.Add("a false second page: the first page was rejected");
        Console.WriteLine("PASS a bodies module whose second page is false is not reconfirmed");

        // Images that do not state the identities the driver pinned: the bodies theorem still holds of them.
        var otherIdentity = Tampered(ImagesModule, source => source.Replace(
            "theorem images_eq : images =",
            "theorem images_eq : images = images := rfl\ntheorem images_unused : images =",
            StringComparison.Ordinal));
        Expect("images theorem of the wrong type", Item(otherIdentity, "body-locations"), "failed",
            "the identities of the pinned images are not confirmed");
        Console.WriteLine("PASS an images theorem of the wrong type leaves the bodies unreconfirmed");
        if (mismatches.Count > 0) throw new InvalidOperationException(string.Join("\n", mismatches));
    }

    /// <summary>The MethodDef token of the first method of an assembly.</summary>
    const int FirstMethodToken = 0x06000001;

    /// <summary>
    /// The image module with the last hexadecimal digit of the one occurrence of <paramref name="bytes"/> in the
    /// image changed, so the module's stated hashes and page claims no longer match what its rows hold.
    /// </summary>
    static string FlipDigitOfBytes(string source, byte[] image, byte[] bytes)
    {
        var offset = image.AsSpan().IndexOf(bytes);
        if (offset < 0 || offset != image.AsSpan().LastIndexOf(bytes))
            throw new InvalidOperationException("The body is not found once in the image");
        const int chunkBytes = 64, indentAndPrefix = 4;
        var last = offset + bytes.Length - 1;
        var row = ChunkLine().Matches(source)[last / chunkBytes];
        var digit = row.Index + indentAndPrefix + 2 * (last % chunkBytes) + 1;
        return source[..digit] + (source[digit] == '0' ? '1' : '0') + source[(digit + 1)..];
    }

    [GeneratedRegex(@"(?m)^  0x[0-9a-f]{128}")]
    private static partial Regex ChunkLine();

    /// <summary>The docstring that opens the `bodies` theorem, the last declaration of the bodies module.</summary>
    const string BodiesDocstring = "/-- The method bodies of `Extracted.methodEvidence`";

    /// <summary>The module with its `bodies` theorem, which closes the module, replaced by other text.</summary>
    static string ReplaceBodies(string source, string replacement) =>
        source[..source.IndexOf(BodiesDocstring, StringComparison.Ordinal)] + replacement + "\n\nend BindingAudit\n";

    /// <summary>The line, counted from 1, where <paramref name="text"/> first occurs in a file.</summary>
    static int LineOf(string path, string text)
    {
        var source = File.ReadAllText(path);
        return source[..source.IndexOf(text, StringComparison.Ordinal)].Count(character => character == '\n') + 1;
    }

    [GeneratedRegex(@"(?m)^  0x([0-9a-f]{40})([0-9a-f])")]
    private static partial Regex FirstChunkDigit();

    /// <summary>The lines of the sample report in docs/CLI.md.</summary>
    static string[] DocumentedBindingReport()
    {
        var text = File.ReadAllText(At("docs/CLI.md")).ReplaceLineEndings("\n");
        var start = text.IndexOf("```text\nValid: strict binding audit of", StringComparison.Ordinal);
        if (start < 0) throw new InvalidOperationException("docs/CLI.md has no sample audit report");
        start = text.IndexOf('\n', start) + 1;
        return text[start..text.IndexOf("\n```", start, StringComparison.Ordinal)].Split('\n');
    }

    /// <summary>A digest that differs from <paramref name="digest"/> in its last digit.</summary>
    static string Flip(string digest) => digest[..^1] + (digest[^1] == '0' ? "1" : "0");

    /// <summary>The names and contents of every file below a directory, as one digest.</summary>
    static string TreeDigest(string directory) => ContentKey(string.Join("\n", Directory
        .EnumerateFiles(directory, "*", SearchOption.AllDirectories).Order(StringComparer.Ordinal)
        .Select(path => Path.GetRelativePath(directory, path) + "=" + Sha(path))));
}
