using System.Diagnostics;
using System.Text.Json;

partial class Program
{
    static void CheckConsumerCertificateReuse(string[] args)
    {
        var measureOnly = args.Contains("--measure", StringComparer.Ordinal);
        var configurationReuse = args.Contains("--configuration-reuse", StringComparer.Ordinal);
        var integrityOnly = args.Contains("--integrity-only", StringComparer.Ordinal);
        var cli = new[] { "dotnet", args.FirstOrDefault(value =>
            value is not ("--measure" or "--configuration-reuse" or "--integrity-only")) ?? ExtractorPath };
        // Lake on Windows fails past MAX_PATH, and the copied cache nests a 64-digit key and
        // the compiled library beneath this directory, so keep its name short.
        var directory = At("artifacts/CertificateReuse-" + Guid.NewGuid().ToString("N")[..8]);
        var previousCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
            Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries");
        var isolatedCache = Path.Combine(directory, "Cache");
        Directory.CreateDirectory(isolatedCache);
        using (var setup = new Program())
        {
            var (key, _) = setup.LibraryIdentity(CommonInputs());
            var candidate = Path.Combine(previousCache, key);
            // Copy only this framework/toolchain entry; the CLI still authenticates it normally.
            if (Directory.Exists(candidate)) CopyTree(candidate, Path.Combine(isolatedCache, key));
        }
        Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", isolatedCache);
        var package = Path.Combine(directory, "Package");
        Directory.CreateDirectory(package);
        File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
        var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
        File.WriteAllText(Path.Combine(package, "lakefile.toml"),
            "name = \"certificate-reuse\"\n[[require]]\nname = \"leancil\"\ngit = " +
            JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) + "\n");
        Run(["lake", "update"], package);
        var output = Path.Combine(directory, "Extraction");
        var proof = Path.Combine(package, "Proof.lean");
        File.WriteAllText(proof, """
        import Extracted
        namespace ExampleProof
        /-- The extracted program satisfies its translation evidence. -/
        theorem correctness : CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
            Extracted.assemblies Extracted.platformDefinitions Extracted.methodEvidence Extracted.imports
            Extracted.program :=
          Extracted.translation_valid
        #print axioms correctness
        end ExampleProof
        """);
        var trace = ConsumerTraceDirectory.Create(directory, "Trace");
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
        var measurements = new List<object>();
        void Extract(string profile) => Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"),
            "Arithmetic::Add(ulong,ulong)", output, profile]);
        void Verify(string label, bool expectedBuild, params string[] options)
        {
            // Each invocation has a distinct proof source, so a whole-result receipt cannot satisfy it.
            File.AppendAllText(proof, "\n-- " + label + "\n");
            var previous = Directory.GetFiles(trace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
            var timer = Stopwatch.StartNew();
            Run([.. cli, "verify", output, "--proof", proof, "--proof-root", package, .. options]);
            timer.Stop();
            var stages = Directory.EnumerateFiles(trace, "*.jsonl").Where(path => !previous.Contains(path))
                .SelectMany(File.ReadLines).Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
            string Transcript(JsonElement stage) => File.ReadAllText(Path.Combine(trace,
                stage.GetProperty("transcript").GetString()!));
            var certificates = stages.Where(stage =>
                stage.GetProperty("stage").GetString() == "Checking consumer extraction certificate").ToArray();
            if (!measureOnly && certificates.Length != (expectedBuild ? 1 : 0))
                throw new InvalidOperationException("Redundant or missing certificate preparation: " + label);
            var certificateBuild = string.Join('\n', certificates.Select(Transcript));
            var built = System.Text.RegularExpressions.Regex.IsMatch(certificateBuild, @"\bBuilt Extracted(?:\s|$)");
            var auditBuilt = System.Text.RegularExpressions.Regex.IsMatch(certificateBuild,
                @"\bBuilt ExtractionAudit(?:\s|$)");
            var replay = stages.Where(stage => stage.GetProperty("stage").GetString() is
                "Kernel replay of consumer proof and dependencies" or "Joint kernel replay of consumer proof and dependencies")
                .ToArray();
            var replayed = replay.SelectMany(stage => Transcript(stage).Split('\n').Where(line => line.StartsWith('{')))
                .Select(line => JsonSerializer.Deserialize<JsonElement>(line).GetProperty("module").GetString()).ToArray();
            if ((!measureOnly && built != expectedBuild) || auditBuilt || !replayed.Contains("Extracted") ||
                replayed.Contains("ExtractionAudit") || !replayed.Contains("LeanCILProof"))
                throw new InvalidOperationException("Certificate build/replay mismatch: " + label);
            var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
            if (!report.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid") ||
                report.GetProperty("libraryBuild").GetString() == "consumer-proof-cache")
                throw new InvalidOperationException("Missing fresh certificate audit: " + label);
            var rechecks = stages.Where(stage => stage.GetProperty("stage").GetString() ==
                "Rechecking consumer inputs").ToArray();
            if (!measureOnly && rechecks.Length != 1)
                throw new InvalidOperationException("Ordinary consumer verification must recheck inputs once: " + label);
            measurements.Add(new { label, seconds = timer.Elapsed.TotalSeconds, built, auditBuilt,
                certificateProcesses = certificates.Length,
                certificateSeconds = certificates.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()),
                inputRechecks = rechecks.Length,
                inputRecheckSeconds = rechecks.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()),
                replaySeconds = replay.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()), replayed });
            Console.WriteLine((measureOnly ? "MEASURE" : "PASS") + " consumer certificate " + label);
        }
        Extract("scalar");
        if (integrityOnly)
        {
            CheckConsumerExtractionIntegrity(cli, directory, package, output, proof);
            return;
        }
        Verify("initial", expectedBuild: true);
        Verify("unchanged", expectedBuild: false);
        if (configurationReuse)
        {
            File.AppendAllText(Path.Combine(package, "lakefile.toml"), "\n# Different consumer configuration.\n");
            Verify("consumer-configuration", expectedBuild: false);
            Verify("fresh-consumer-configuration", true, "--fresh");
        }
        var corrupted = 0;
        Directory.CreateDirectory(SuccessCacheRoot);
        foreach (var generation in Directory.EnumerateDirectories(SuccessCacheRoot))
        {
            var files = Path.Combine(generation, "files");
            if (!File.Exists(Path.Combine(files, "leancil-support.json"))) continue;
            var artifacts = Directory.GetFiles(files, "Extracted.olean", SearchOption.AllDirectories);
            if (artifacts.Length == 0) continue;
            foreach (var artifact in artifacts) File.AppendAllText(artifact, "corrupted certificate");
            // Updating the untrusted hashes cannot renew the producer's HMAC.
            File.WriteAllBytes(Path.Combine(generation, "receipt.json"),
                JsonSerializer.SerializeToUtf8Bytes(CacheFiles(files)));
            corrupted++;
        }
        if (!measureOnly && corrupted == 0) throw new InvalidOperationException("No certified extraction artifact to corrupt.");
        Verify("self-rehashed-corruption", expectedBuild: true);
        Extract("x64-v3");
        Verify("changed-extraction", expectedBuild: true);
        File.AppendAllText(Path.Combine(output, "Extracted.lean"), "\n-- changed after certification\n");
        var tampered = Execute([.. cli, "verify", output, "--proof", proof, "--proof-root", package]);
        if (tampered.Code != 1 || !tampered.Output.Contains("differs from regenerated CIL", StringComparison.Ordinal) ||
            File.Exists(Path.Combine(output, "verified.json")))
            throw new InvalidOperationException("Cached certificate bypassed extraction regeneration: " + tampered.Output);
        Console.WriteLine("PASS cached certificate cannot bypass generated-source tampering rejection");
        Extract("scalar");
        if (configurationReuse)
            File.AppendAllText(Path.Combine(package, "lakefile.toml"),
                "\n# Restore generated-only preparation before mutation.\n");
        CheckConsumerExtractionIntegrity(cli, directory, package, output, proof);
        File.WriteAllText(Path.Combine(directory, "timings.json"), JsonSerializer.Serialize(measurements, Json));
        Console.WriteLine("Measurements: " + Path.Combine(directory, "timings.json"));
    }

    // The checker authenticates the bytes it read. Every verification mode must use that digest.
    static void CheckManifestDigest(string[] cli, string package, string output, string proof)
    {
        var path = Path.Combine(output, "identity.json");
        var bytes = File.ReadAllBytes(path);
        var expected = Sha256Digest.Of(bytes);
        var checkedManifest = Run([.. cli, "check", output, "--format", "json"]);
        if (JsonSerializer.Deserialize<JsonElement>(checkedManifest).GetProperty("identitySha256").GetString() !=
            expected.ToString())
            throw new InvalidDataException("Check reported a different manifest digest.");
        try
        {
            File.WriteAllBytes(path, [0xef, 0xbb, 0xbf, .. bytes]);
            if (Execute([.. cli, "check", output]).Code == 0)
                throw new InvalidDataException("Check accepted a different UTF-8 encoding of the manifest.");
        }
        finally { File.WriteAllBytes(path, bytes); }

        var reportPath = Path.Combine(output, "verified.json");
        var assembly = At("Examples/Assembly/bin/Examples.dll");
        const string mismatch = "Extraction identity changed during verification.";
        int checkCount = 0, mismatchAt = 0;
        Sha256Digest Receive(Sha256Digest actual)
        {
            if (actual != expected) throw new InvalidDataException("The fixture manifest changed.");
            return ++checkCount == mismatchAt ? Sha256Digest.Of([]) : actual;
        }
        foreach (var check in new[] { 1, 2 })
        {
            using var verifier = new Program();
            checkCount = 0;
            mismatchAt = check;
            try
            {
                verifier.Verify(assembly, "Examples", "Arithmetic::Add(ulong,ulong)", proof, output,
                    existingArtifacts: true, receiveDigest: Receive);
                throw new InvalidDataException("Standalone verification accepted a different digest.");
            }
            catch (InvalidDataException error) when (error.Message == mismatch) { }
            if (checkCount != check || File.Exists(reportPath))
                throw new InvalidDataException("Standalone digest mismatch left a certificate or ran further checks.");
        }

        ConsumerOutcome Batch(bool compile, int mismatchOn)
        {
            using var verifier = new Program();
            checkCount = 0;
            mismatchAt = mismatchOn;
            ConsumerRequest request = new(assembly, output, proof, "ExampleProof.correctness", null);
            return verifier.VerifyConsumerRequests(package, [request], null, batch: true,
                checkOnly: compile, receiveDigest: Receive).Single();
        }
        var refusedCompile = Batch(true, 1);
        if (refusedCompile.Error?.Message != mismatch || refusedCompile.Checked || checkCount != 1)
            throw new InvalidDataException("Compile check accepted an inconsistent digest.", refusedCompile.Error);
        var fresh = Batch(false, 0);
        var cached = Batch(false, 0);
        if (fresh.Report?.identitySha256 != expected.ToString() || cached.Report?.identitySha256 != expected.ToString() ||
            cached.Report.libraryBuild != "consumer-proof-cache" || checkCount != 2)
            throw new InvalidDataException("The checked digest was missing from the fresh or cached certificate.",
                fresh.Error ?? cached.Error);
        var refusedCache = Batch(false, 2);
        if (refusedCache.Error?.Message != mismatch || checkCount != 2 || File.Exists(reportPath))
            throw new InvalidDataException("A cached certificate survived a different digest.", refusedCache.Error);
        var compiled = Batch(true, 0);
        if (!compiled.Checked || compiled.Error is not null || File.Exists(reportPath))
            throw new InvalidDataException("Compile check failed on the original manifest.", compiled.Error);
        Console.WriteLine("PASS exact manifest bytes bind standalone, batch, cached and compile-only checks");
    }

    static void CheckConsumerExtractionIntegrity(string[] cli, string directory, string package,
        string output, string proof)
    {
        CheckManifestDigest(cli, package, output, proof);
        var cleanProof = Path.Combine(package, "CleanProof.lean");
        File.Copy(proof, cleanProof);
        var other = Path.Combine(directory, "OtherExtraction");
        Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"),
            "Arithmetic::Add(ulong,ulong)", other, "x64-v3"]);
        var batch = Path.Combine(directory, "requests.json");
        var results = Path.Combine(directory, "results.json");
        void Requests(bool replaceArtifact, bool expectRejection = false) =>
            File.WriteAllText(batch, JsonSerializer.Serialize(new
        {
            schema = 1, proofRoot = package,
            requests = new[]
            {
                expectRejection
                    ? new { output, proof, theorem = "ExampleProof.correctness", expect = "rejected",
                        refutes = (int?)1 }
                    : new { output, proof = replaceArtifact ? proof : cleanProof,
                        theorem = "ExampleProof.correctness", expect = "verified", refutes = (int?)null },
                new { output = other, proof = cleanProof, theorem = "ExampleProof.correctness", expect = "verified",
                    refutes = (int?)null }
            }
        }, Json));
        Requests(replaceArtifact: false);
        Run([.. cli, "verify-batch", batch, "--parallel", "2", "--results", results]);
        var warm = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(results))!;
        if (warm.Length != 2 || warm.Any(row => row.GetProperty("status").GetString() != "verified"))
            throw new InvalidOperationException("Clean extraction batch did not verify both requests.");
        File.Copy(results, Path.Combine(directory, "integrity-clean-results.json"));
        File.AppendAllText(proof, """

        open Lean Elab Command in
        run_cmd do
          let root := ((← getFileName) : System.FilePath).parent.get!
          let artifact := root / ".lake/packages/leancil_generated/.lake/build/lib/lean/Extracted.olean"
          let bytes ← IO.FS.readBinFile artifact
          IO.FS.rename artifact (artifact.addExtension "original")
          IO.FS.writeBinFile artifact (bytes.push 0)

        """);
        foreach (string[] options in new string[][] { [], ["--fresh"] })
        {
            var preparation = options.Length == 0 ? "restored" : "built";
            // An expected rejection runs after the request it refutes, and still fails on the changed artifact.
            Requests(replaceArtifact: true, expectRejection: options.Length != 0);
            File.WriteAllText(Path.Combine(output, "verified.json"), "stale report");
            var replaced = Execute([.. cli, "verify-batch", batch, "--parallel", "2",
                "--results", results, .. options]);
            File.WriteAllText(Path.Combine(directory, "integrity-" + preparation + ".log"), replaced.Output);
            File.Copy(results, Path.Combine(directory, "integrity-" + preparation + "-results.json"));
            var rows = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(results))!;
            var hashes = System.Text.RegularExpressions.Regex.Match(replaced.Output,
                @"Extracted\.olean: sha256 before=([0-9a-fA-F]{64}), after=([0-9a-fA-F]{64})");
            var independentOutcomes = rows.Length == 2 &&
                rows[0].GetProperty("stage").GetString() == "extraction integrity" &&
                rows[0].GetProperty("status").GetString() == "failed" &&
                rows[1].GetProperty("status").GetString() == "verified";
            var changedArtifactReported =
                replaced.Output.Contains("Extraction certificate artifacts changed during proof checking") &&
                replaced.Output.Contains("Preparation: " + preparation + "; package:", StringComparison.Ordinal) &&
                hashes.Success && hashes.Groups[1].Value != hashes.Groups[2].Value &&
                replaced.Output.Contains("artifact modified=", StringComparison.Ordinal) &&
                replaced.Output.Contains("trace sha256=", StringComparison.Ordinal);
            if (replaced.Code != 1 || !independentOutcomes || !changedArtifactReported ||
                replaced.Output.Contains("Lean could not prove", StringComparison.Ordinal) ||
                File.Exists(Path.Combine(output, "verified.json")) ||
                !File.Exists(Path.Combine(other, "verified.json")))
                throw new InvalidOperationException("Batch extraction integrity mismatch: " + replaced.Output);
            Console.WriteLine("PASS " + preparation + " batch extraction rewrite reports exact changed hashes, " +
                "fails the changed request and preserves the unrelated certificate");
        }
    }
}
