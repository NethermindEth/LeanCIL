using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;
using Nethermind.LeanCIL;

// Share the same fresh-build and theorem-audit implementation as the test scripts.
partial class Program
{
    sealed record VerificationSettings(int schema, string proof, string theorem, string? proofRoot = null);
    sealed record BatchRequest(string output, string proof, string theorem, string? expect = null);
    sealed record BatchManifest(int schema, string proofRoot, BatchRequest[] requests);
    sealed record BatchResult(string output, string proof, string theorem, string expect, string status, string stage,
        string? error, string[]? axioms, string? libraryBuild, FailureReports.Report? failure);

    const string BatchUsage = "Usage: leancil verify-batch requests.json [--fresh] [--rebuild-library] [--parallel count] [--results results.json]";

    internal static int VerifyBatch(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException(BatchUsage);
        var manifestPath = Path.GetFullPath(args[0]);
        var fresh = false;
        var rebuildLibrary = false;
        int? parallelism = null;
        string? resultsPath = null;
        for (var index = 1; index < args.Length; index++)
        {
            var option = args[index];
            if (option == "--rebuild-library" && !rebuildLibrary)
            {
                rebuildLibrary = true;
                continue;
            }
            if (option == "--fresh" && !fresh)
            {
                fresh = true;
                continue;
            }
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException($"Missing value for {option}.");
            switch (option)
            {
                case "--parallel" when parallelism is null:
                    parallelism = int.TryParse(args[index], out var degree) && degree > 0 ? degree
                        : throw new ArgumentException("--parallel requires a positive integer.");
                    break;
                case "--results" when resultsPath is null:
                    resultsPath = Path.GetFullPath(args[index]);
                    break;
                default:
                    throw new ArgumentException($"Unknown or duplicate option: {option}");
            }
        }

        var directory = Path.GetDirectoryName(manifestPath)!;
        var manifest = JsonSerializer.Deserialize<BatchManifest>(File.ReadAllText(manifestPath),
            new JsonSerializerOptions { UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow })
            ?? throw new InvalidDataException("Missing batch manifest.");
        if (manifest.schema != 1 || string.IsNullOrWhiteSpace(manifest.proofRoot) || manifest.requests is null || manifest.requests.Length == 0 ||
            manifest.requests.Any(request => request is null || string.IsNullOrWhiteSpace(request.output) ||
                string.IsNullOrWhiteSpace(request.proof) || string.IsNullOrWhiteSpace(request.theorem) ||
                request.expect is not (null or "verified" or "rejected")))
            throw new InvalidDataException("Invalid batch manifest: expected schema 1, proofRoot and requests with output, proof, theorem and optional expect (verified or rejected).");
        var proofRoot = Path.GetFullPath(manifest.proofRoot, directory);
        var count = manifest.requests.Length;
        var outcomes = new ConsumerOutcome?[count];
        var requests = new List<ConsumerRequest>();
        var indices = new List<int>();
        var outputs = manifest.requests.Select(request => Path.GetFullPath(request.output, directory)).ToArray();
        var proofs = manifest.requests.Select(request => Path.GetFullPath(request.proof, directory)).ToArray();
        var lastForOutput = Enumerable.Range(0, count).GroupBy(i => outputs[i], OperatingSystem.IsWindows()
            ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal).Select(group => group.Max()).ToHashSet();
        for (var i = 0; i < count; i++)
        {
            var request = manifest.requests[i];
            var stage = "proof selection";
            try
            {
                if (!Regex.IsMatch(request.theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
                    throw new ArgumentException("Invalid theorem name");
                if (!File.Exists(proofs[i]))
                    throw new FileNotFoundException($"Proof file not found: {CliPaths.Display(proofs[i])}", proofs[i]);
                var settingsPath = Path.Combine(outputs[i], "verification.json");
                // As in sequential runs, the last request for an output owns its settings.
                if (lastForOutput.Contains(i))
                {
                    Directory.CreateDirectory(outputs[i]);
                    File.Delete(Path.Combine(outputs[i], "verified.json"));
                    FailureReports.Delete(outputs[i]);
                    File.WriteAllText(settingsPath, JsonSerializer.Serialize(new VerificationSettings(1,
                        Path.GetRelativePath(outputs[i], proofs[i]).Replace('\\', '/'), request.theorem,
                        Path.GetRelativePath(outputs[i], proofRoot).Replace('\\', '/')), Json) + "\n");
                }
                stage = "extraction integrity";
                var identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(outputs[i], "identity.json")));
                var assembly = Path.GetFullPath(identity.GetProperty("assemblyPath").GetString()!, outputs[i]);
                requests.Add(new(assembly, outputs[i], proofs[i], request.theorem, lastForOutput.Contains(i) ? settingsPath : null,
                    request.expect == "rejected"));
                indices.Add(i);
            }
            catch (Exception error)
            {
                outcomes[i] = new ConsumerOutcome { Stage = stage, Error = error };
            }
        }

        // Print each request as soon as it is final, so a long batch shows progress; workspaces run in parallel.
        var printed = new bool[count];
        var gate = new object();
        bool Print(int i, ConsumerOutcome outcome)
        {
            var request = manifest.requests[i];
            var expect = request.expect ?? "verified";
            var passed = outcome.Error is null && (expect == "rejected" ? outcome.Rejected : outcome.Report is not null);
            lock (gate)
            {
                if (printed[i]) return passed;
                printed[i] = true;
                if (passed)
                    Console.WriteLine(expect == "rejected"
                        ? $"PASS rejected {CliPaths.Display(outputs[i])} {request.theorem} ({outcome.Stage})"
                        : $"PASS verified {CliPaths.Display(outputs[i])} {request.theorem}");
                else
                {
                    var error = outcome.Error ?? new InvalidOperationException("Verification produced no result.");
                    Console.WriteLine($"FAIL {CliPaths.Display(outputs[i])} {request.theorem} (stage: {outcome.Stage})");
                    CliDiagnostics.Write(new CliFailure(outcome.Stage, error), outcome.Stage, true);
                }
                Console.Out.Flush();
            }
            return passed;
        }

        using (var verification = new Program { freshProofs = fresh, freshLibrary = rebuildLibrary })
        {
            var verified = requests.Count == 0 ? [] : verification.VerifyConsumerRequests(proofRoot, requests, null, batch: true,
                parallelism ?? Math.Max(1, Environment.ProcessorCount / 8), (k, outcome) => Print(indices[k], outcome));
            for (var k = 0; k < verified.Length; k++) outcomes[indices[k]] = verified[k];
        }
        // A rejected last request leaves no certificate for its output, as in sequential runs.
        foreach (var i in lastForOutput.Where(i => !indices.Contains(i)))
            File.Delete(Path.Combine(outputs[i], "verified.json"));

        var results = new List<BatchResult>();
        var failed = 0;
        for (var i = 0; i < count; i++)
        {
            var request = manifest.requests[i];
            var outcome = outcomes[i]!;
            var expect = request.expect ?? "verified";
            var passed = Print(i, outcome);
            var status = passed ? expect : "failed";
            if (!passed) failed++;
            // A verified refutation is a certificate and a failed contract; any other pass leaves no failure.
            var failure = outcome.Error is { } error ? FailureReports.Failed(outcome.Stage, error, request.theorem, proofs[i], outputs[i], proofRoot)
                : outcome.Report is { } report ? FailureReports.Refuted(report.theoremAudit, request.theorem, proofs[i], outputs[i], proofRoot)
                : FailureReports.Classify(outcome.Stage, outcome.Detail ?? "Verification produced no result.", outcome.Hidden,
                    request.theorem, proofs[i], outputs[i], proofRoot);
            if (lastForOutput.Contains(i))
            {
                if (failure is null) FailureReports.Delete(outputs[i]);
                else FailureReports.Write(outputs[i], failure);
            }
            results.Add(new(outputs[i], proofs[i], request.theorem, expect, status, outcome.Stage,
                passed ? null : (outcome.Error?.Message ?? "Verification produced no result."),
                outcome.Report?.axioms, outcome.Report?.libraryBuild, failure));
        }
        if (resultsPath is not null)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(resultsPath)!);
            File.WriteAllText(resultsPath, JsonSerializer.Serialize(results, Json) + "\n");
        }
        Console.WriteLine($"Batch: {count - failed} passed, {failed} failed of {count} requests.");
        return failed == 0 ? 0 : 1;
    }

    internal static void VerifyArtifacts(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException("Usage: leancil verify output-directory [--proof proof.lean] [--theorem name] [--fresh] [--rebuild-library] [--proof-root package-directory] [--force-full-verify] [--full-artifact Lib=directory]");

        var output = Path.GetFullPath(args[0]);
        string? proof = null;
        string? theorem = null;
        var fresh = false;
        var rebuildLibrary = false;
        string? proofRoot = null;
        bool forceFull = false;
        Dictionary<string, string> fullArtifacts = new(StringComparer.Ordinal);

        for (var index = 1; index < args.Length; index++)
        {
            var option = args[index];
            if (option == "--force-full-verify" && !forceFull)
            {
                forceFull = true;
                continue;
            }
            if (option == "--rebuild-library" && !rebuildLibrary)
            {
                rebuildLibrary = true;
                continue;
            }
            if (option == "--fresh" && !fresh)
            {
                fresh = true;
                continue;
            }
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException($"Missing value for {option}.");

            switch (option)
            {
                case "--full-artifact":
                    string[] artifact = args[index].Split('=', 2);
                    if (artifact.Length != 2 || string.IsNullOrWhiteSpace(artifact[0]) || string.IsNullOrWhiteSpace(artifact[1]) ||
                        !fullArtifacts.TryAdd(artifact[0], Path.GetFullPath(artifact[1])))
                        throw new ArgumentException("--full-artifact requires unique Lib=directory values.");
                    break;
                case "--proof-root" when proofRoot is null:
                    proofRoot = Path.GetFullPath(args[index]);
                    break;
                case "--proof" when proof is null:
                    proof = Path.GetFullPath(args[index]);
                    break;
                case "--theorem" when theorem is null:
                    theorem = args[index];
                    break;
                default:
                    throw new ArgumentException($"Unknown or duplicate option: {option}");
            }
        }

        var reportPath = Path.Combine(output, "verified.json");
        var settingsPath = Path.Combine(output, "verification.json");
        var stage = "proof selection";
        try
        {
            if (File.Exists(settingsPath))
            {
                var saved = JsonSerializer.Deserialize<VerificationSettings>(File.ReadAllText(settingsPath),
                    new JsonSerializerOptions { UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow })
                    ?? throw new InvalidDataException("Missing verification settings.");
                if (saved.schema != 1 || string.IsNullOrWhiteSpace(saved.proof) || string.IsNullOrWhiteSpace(saved.theorem))
                    throw new InvalidDataException("Invalid verification.json: expected schema 1, proof and theorem.");
                proof ??= Path.GetFullPath(saved.proof, output);
                theorem ??= saved.theorem;
                if (saved.proofRoot is not null) proofRoot ??= Path.GetFullPath(saved.proofRoot, output);
            }
            else if (proof is null && File.Exists(reportPath))
            {
                // Migrate proof selection from reports created before settings were separate.
                var previous = JsonSerializer.Deserialize<Report>(File.ReadAllText(reportPath))
                    ?? throw new InvalidDataException("Missing verification report.");
                proof = previous.inputs.Keys.Single(key => key.StartsWith("proof:", StringComparison.Ordinal))[6..];
                theorem ??= previous.theorem;
            }

            File.Delete(reportPath);
            if (fullArtifacts.Count > 0 && !forceFull)
                throw new ArgumentException("--full-artifact requires --force-full-verify.");
            FailureReports.Delete(output);
            proof ??= Path.Combine(output, "Proof.lean");
            theorem ??= "ExampleProof.correctness";
            if (!Regex.IsMatch(theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
                throw new ArgumentException("Invalid theorem name");
            if (!File.Exists(proof))
                throw new FileNotFoundException($"Proof file not found: {CliPaths.Display(proof)}", proof);

            // Settings are reusable inputs and survive both successful and failed proofs.
            Directory.CreateDirectory(output);
            var settings = new VerificationSettings(1, Path.GetRelativePath(output, proof).Replace('\\', '/'), theorem,
                proofRoot is null ? null : Path.GetRelativePath(output, proofRoot).Replace('\\', '/'));
            File.WriteAllText(settingsPath, JsonSerializer.Serialize(settings, Json) + "\n");
            stage = "extraction integrity";
            var manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
            var assembly = Path.GetFullPath(manifest.GetProperty("assemblyPath").GetString()!, output);
            var identity = manifest.GetProperty("assemblyIdentity").GetString()!;
            var entry = manifest.GetProperty("entry").GetString()!;

            using Program verification = new()
            {
                freshProofs = fresh || forceFull,
                freshLibrary = rebuildLibrary,
                forceFullVerification = forceFull
            };
            if (forceFull) verification.fullImportAudit = (artifact, session, module, leanPath) =>
                verification.VerifyFullImports(artifact, session, module, theorem, leanPath, fullArtifacts);
            if (forceFull) verification.PreflightFullImports(output, fullArtifacts);
            var report = proofRoot is null
                ? verification.Verify(assembly, identity, entry, proof, output,
                    theorem: theorem, existingArtifacts: true, settings: settingsPath, stage: value => stage = value)
                : verification.VerifyConsumer(assembly, proof, output, theorem, proofRoot, settingsPath, value => stage = value);

            Console.WriteLine($"Verified: {report.theorem}");
            Console.WriteLine($"  Assembly: {identity}");
            Console.WriteLine($"  Entry: {entry}");
            if (manifest.TryGetProperty("initializedTypes", out var initializedTypes))
                foreach (var name in initializedTypes.EnumerateArray())
                    Console.WriteLine($"  Caller assumption: {name.GetString()} initialization completed successfully before invocation.");
            if (manifest.TryGetProperty("staticValues", out var staticValues))
                foreach (var name in staticValues.EnumerateArray())
                    Console.WriteLine($"  Caller assumption: {name.GetString()} keeps the value its static constructor stored.");
            foreach (string assumption in ContractImportAssumptions(manifest))
                Console.WriteLine(report.compositionTheorem is null
                    ? "  Conditional verification: assumes " + assumption + "; implementation contracts are not discharged by hashes or certification records."
                    : "  Original caller premise: " + assumption + "; discharged in " + report.compositionTheorem + ".");
            foreach (PublishedImport import in report.imports ?? [])
            {
                Console.WriteLine("  Imported contract accepted via " + import.acceptedVia + ": " + import.identity);
                Console.WriteLine("  Published certification (unauthenticated sidecar record, sidecar SHA-256 " + import.sidecarSha256 + "): " +
                    import.certificationTheorem + " : " + import.certificationStatement);
                Console.WriteLine("  Deployment obligation: " + import.deploymentObligation);
            }
            if (report.compositionTheorem is not null)
                Console.WriteLine("  Independently composed theorem: " + report.compositionTheorem);
            Console.WriteLine($"  Proof: {CliPaths.Display(proof)}");
            Console.WriteLine($"  Axioms: {(report.axioms.Length == 0 ? "none" : string.Join(", ", report.axioms))}");
            var refuted = FailureReports.Refuted(report.theoremAudit, theorem, proof, output, proofRoot);
            if (refuted is not null)
            {
                FailureReports.Write(output, refuted);
                Console.WriteLine($"  Refutes: the contract (theorem at {CliPaths.Display(proof)}:{refuted.line}:{refuted.column})");
                Console.WriteLine($"  Failure: {CliPaths.Display(Path.Combine(output, FailureReports.FileName))}");
            }
            Console.WriteLine($"  Settings: {CliPaths.Display(settingsPath)}");
            Console.WriteLine($"  Report: {CliPaths.Display(reportPath)}");
            Console.WriteLine("  Statement:");
            var statement = report.theoremAudit.Split("'" + report.theorem + "'", 2)[0].Trim();
            foreach (var line in statement.Split('\n'))
                Console.WriteLine("    " + line.TrimEnd());
        }
        catch (Exception error)
        {
            File.Delete(reportPath);
            FailureReports.Write(output, FailureReports.Failed(stage, error, theorem ?? "ExampleProof.correctness",
                proof ?? Path.Combine(output, "Proof.lean"), output, proofRoot));
            throw new CliFailure(stage, error);
        }
    }
}
