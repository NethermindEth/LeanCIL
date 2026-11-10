using System.Text.Json;
using System.Text.Json.Nodes;
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

    const string BatchUsage = "Usage: leancil verify-batch requests.json [--fresh] [--rebuild-library] " +
        "[--parallel count] [--results results.json] [--format text|json] [--trace]";

    const string VerifyUsage = "Usage: leancil verify output-directory [--proof proof.lean] [--theorem name] " +
        "[--fresh] [--rebuild-library] [--proof-root package-directory] [--force-full-verify] " +
        "[--full-artifact Lib=directory] [--format text|json] [--trace] [--goals]";

    /// <summary>
    /// The tool version, the LeanCIL revision and Lean toolchain its framework comes from, and the
    /// Lake requirement a consumer package pins to match it.
    /// </summary>
    internal static string VersionReport()
    {
        var version = InformationalVersion;
        var toolchain = File.ReadAllText(At("lean-toolchain")).Trim();
        var revision = SourceRevision;
        var report = new System.Text.StringBuilder()
            .AppendLine($"leancil {version?.Split('+')[0] ?? "unknown"}")
            .AppendLine($"LeanCIL revision: {revision ?? "unknown (built outside a git checkout)"}")
            .AppendLine($"Lean toolchain: {toolchain}");
        if (revision is not null)
            report.AppendLine("Consumer lakefile.toml requirement:")
                .AppendLine("[[require]]")
                .AppendLine("name = \"leancil\"")
                .AppendLine("git = \"https://github.com/NethermindEth/LeanCIL.git\"")
                .AppendLine($"rev = \"{revision}\"");
        return report.ToString();
    }

    /// <summary>LeanCIL's own example and test modules, which the tool does not ship.</summary>
    static HashSet<string> RepositoryModules() => [.. Regex.Matches(File.ReadAllText(At("lakefile.toml")),
            @"^\[\[lean_lib\]\]\r?\nname = ""([^""]+)""", RegexOptions.Multiline)
        .Select(match => match.Groups[1].Value).Where(name => name != "CIL"), "Examples.Support"];

    // Importing one fails later as a missing Lake source; name the module and its replacement instead.
    static void RejectRepositoryImports(string proof)
    {
        var repository = RepositoryModules();
        var imported = SourceImport().Matches(File.ReadAllText(proof)).Select(import => import.Groups[1].Value)
            .FirstOrDefault(repository.Contains);
        if (imported is not null)
            throw new InvalidDataException($"{CliPaths.Display(proof)} imports {imported}, a LeanCIL repository " +
                "module that the tool does not ship. Import CIL modules instead; CIL.Safety.Memory.empty replaces " +
                "Examples.empty.");
    }

    internal static int VerifyBatch(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException(BatchUsage);
        var manifestPath = Path.GetFullPath(args[0]);
        var fresh = false;
        var rebuildLibrary = false;
        var trace = false;
        string? format = null;
        int? parallelism = null;
        string? resultsPath = null;
        for (var index = 1; index < args.Length; index++)
        {
            var option = args[index];
            if (option == "--trace" && !trace)
            {
                trace = true;
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
                case "--parallel" when parallelism is null:
                    parallelism = int.TryParse(args[index], out var degree) && degree > 0 ? degree
                        : throw new ArgumentException("--parallel requires a positive integer.");
                    break;
                case "--results" when resultsPath is null:
                    resultsPath = Path.GetFullPath(args[index]);
                    break;
                case "--format" when format is null:
                    format = args[index] is "text" or "json" ? args[index]
                        : throw new ArgumentException("--format takes text or json.");
                    break;
                default:
                    throw new ArgumentException($"Unknown or duplicate option: {option}");
            }
        }
        var json = format == "json";

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
                RejectRepositoryImports(proofs[i]);
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
                // The JSON document is printed whole once every request is final.
                if (json) return passed;
                if (passed)
                    Console.WriteLine(expect == "rejected"
                        ? $"PASS rejected {CliPaths.Display(outputs[i])} {request.theorem} ({outcome.Stage})"
                        : $"PASS verified {CliPaths.Display(outputs[i])} {request.theorem}");
                else
                {
                    var error = outcome.Located() ?? new InvalidOperationException("Verification produced no result.");
                    Console.WriteLine($"FAIL {CliPaths.Display(outputs[i])} {request.theorem} (stage: {outcome.Stage})");
                    CliDiagnostics.Write(new CliFailure(outcome.Stage, error), outcome.Stage, true);
                }
                if (trace) Console.Write(TraceReport(Traced(outcome.ProofMessages(proofs[i]), true).Trace, proofs[i]));
                Console.Out.Flush();
            }
            return passed;
        }

        using (var verification = new Program
        {
            freshProofs = fresh, freshLibrary = rebuildLibrary, structuredFailures = json, tracesSteps = trace
        })
        {
            var verified = requests.Count == 0 ? [] : verification.VerifyConsumerRequests(proofRoot, requests, null, batch: true,
                parallelism ?? Math.Max(1, Environment.ProcessorCount / 8), (k, outcome) => Print(indices[k], outcome));
            for (var k = 0; k < verified.Length; k++) outcomes[indices[k]] = verified[k];
        }
        // A rejected last request leaves no certificate for its output, as in sequential runs.
        foreach (var i in lastForOutput.Where(i => !indices.Contains(i)))
            File.Delete(Path.Combine(outputs[i], "verified.json"));

        var results = new List<BatchResult>();
        var reports = new JsonArray();
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
            var failure = outcome.Located() is { } error
                ? FailureReports.Failed(outcome.Stage, error, request.theorem, proofs[i], outputs[i], proofRoot)
                : outcome.Report is { } report ? FailureReports.Refuted(report.theoremAudit, request.theorem, proofs[i], outputs[i], proofRoot)
                : FailureReports.Classify(outcome.Stage, outcome.Detail ?? "Verification produced no result.", outcome.Hidden,
                    request.theorem, proofs[i], outputs[i], proofRoot, outcome.Sources);
            if (lastForOutput.Contains(i))
            {
                if (failure is null) FailureReports.Delete(outputs[i]);
                else FailureReports.Write(outputs[i], failure);
            }
            results.Add(new(outputs[i], proofs[i], request.theorem, expect, status, outcome.Stage,
                passed ? null : (outcome.Error?.Message ?? "Verification produced no result."),
                outcome.Report?.axioms, outcome.Report?.libraryBuild, failure));
            if (json) reports.Add(BatchEntry(outcome, failure, expect, status, request.theorem, proofs[i], outputs[i]));
        }
        if (resultsPath is not null)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(resultsPath)!);
            File.WriteAllText(resultsPath, JsonSerializer.Serialize(results, Json) + "\n");
        }
        if (json)
            Console.Write(VerifyReports.Serialize(new JsonObject
            {
                ["schema"] = VerifyReports.BatchSchema,
                ["passed"] = count - failed,
                ["failed"] = failed,
                ["requests"] = reports,
            }));
        else Console.WriteLine($"Batch: {count - failed} passed, {failed} failed of {count} requests.");
        return failed == 0 ? 0 : 1;

        // A request's expectation and status, with the report `verify --format json` gives for it.
        JsonObject BatchEntry(ConsumerOutcome outcome, FailureReports.Report? failure, string expect, string status,
            string theorem, string proof, string output)
        {
            var messages = outcome.ProofMessages(proof);
            var verified = outcome.Error is null && outcome.Report is not null;
            var report = VerifyReports.Result(verified ? "verified" : "failed", failure, theorem, proof, output,
                proofRoot, verified ? null : outcome.Stage, outcome.Report?.axioms,
                outcome.Report is { } checkedReport ? StatementOf(checkedReport) : null, JsonMessages(messages), trace,
                messages is not null);
            return new JsonObject { ["expect"] = expect, ["status"] = status, ["report"] = report };
        }
    }

    internal static void VerifyArtifacts(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException(VerifyUsage);

        var output = Path.GetFullPath(args[0]);
        // A request for JSON gets JSON for every outcome, including a rejected option after it.
        var json = args.Zip(args.Skip(1)).Any(pair => pair is ("--format", "json"));
        var trace = false;
        var goals = false;
        string? format = null;
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
            if (option == "--trace" && !trace)
            {
                trace = true;
                continue;
            }
            if (option == "--goals" && !goals)
            {
                goals = true;
                continue;
            }
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw Rejected(new ArgumentException($"Missing value for {option}."));

            switch (option)
            {
                case "--format" when format is null:
                    format = args[index] is "text" or "json" ? args[index]
                        : throw Rejected(new ArgumentException("--format takes text or json."));
                    break;
                case "--full-artifact":
                    string[] artifact = args[index].Split('=', 2);
                    if (artifact.Length != 2 || string.IsNullOrWhiteSpace(artifact[0]) || string.IsNullOrWhiteSpace(artifact[1]) ||
                        !fullArtifacts.TryAdd(artifact[0], Path.GetFullPath(artifact[1])))
                        throw Rejected(new ArgumentException("--full-artifact requires unique Lib=directory values."));
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
                    throw Rejected(new ArgumentException($"Unknown or duplicate option: {option}"));
            }
        }

        // A rejected option, reported as JSON when the request asked for it.
        Exception Rejected(ArgumentException error)
        {
            if (!json) return error;
            var failure = FailureReports.Classify("arguments", error.Message, null,
                theorem ?? "ExampleProof.correctness", proof ?? Path.Combine(output, "Proof.lean"), output, proofRoot);
            Console.Write(VerifyReports.Serialize(VerifyReports.Result("failed", failure, failure.theorem,
                failure.proof, output, proofRoot, "arguments", null, null, [],
                traceRequested: args.Contains("--trace"), proofChecked: false,
                goalsRequested: args.Contains("--goals"))));
            return new CliFailure("arguments", error, reported: true);
        }

        var reportPath = Path.Combine(output, "verified.json");
        var settingsPath = Path.Combine(output, "verification.json");
        var stage = "proof selection";
        Program? verification = null;
        int OpenGoalCount() => goals ? Observed(verification?.ProofMessages, trace, goals).Goals.Length : 0;
        Exception OpenGoals(int count) => new InvalidOperationException(
            $"{count} goal{(count == 1 ? " remains" : "s remain")} in {CliPaths.Display(proof!)}.");
        // With --goals, a proof that leaves goals ends the run there: neither replay nor audit can accept it.
        void RequireNoOpenGoals()
        {
            if (OpenGoalCount() is not (> 0 and var count)) return;
            stage = OpenGoalsStage;
            throw OpenGoals(count);
        }
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
            File.Delete(Path.Combine(output, ProofMessagesText));
            if (fullArtifacts.Count > 0 && !forceFull)
                throw new ArgumentException("--full-artifact requires --force-full-verify.");
            FailureReports.Delete(output);
            proof ??= Path.Combine(output, "Proof.lean");
            theorem ??= "ExampleProof.correctness";
            if (!Regex.IsMatch(theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
                throw new ArgumentException("Invalid theorem name");
            if (!File.Exists(proof))
                throw new FileNotFoundException($"Proof file not found: {CliPaths.Display(proof)}", proof);
            RejectRepositoryImports(proof);

            // Settings are reusable inputs and survive both successful and failed proofs.
            Directory.CreateDirectory(output);
            var settings = new VerificationSettings(1, Path.GetRelativePath(output, proof).Replace('\\', '/'), theorem,
                proofRoot is null ? null : Path.GetRelativePath(output, proofRoot).Replace('\\', '/'));
            File.WriteAllText(settingsPath, JsonSerializer.Serialize(settings, Json) + "\n");
            stage = "extraction integrity";
            if (ExtractAgainIfRebuilt(output) is { } reason)
                (json ? Console.Error : Console.Out).WriteLine("Re-extracted " + CliPaths.Display(output) + ": " +
                    reason + " since extraction.");
            var manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
            var assembly = Path.GetFullPath(manifest.GetProperty("assemblyPath").GetString()!, output);
            var identity = manifest.GetProperty("assemblyIdentity").GetString()!;
            var entry = manifest.GetProperty("entry").GetString()!;

            verification = new()
            {
                freshProofs = fresh || forceFull,
                freshLibrary = rebuildLibrary,
                forceFullVerification = forceFull,
                viewsStatement = true,
                structuredFailures = json,
                tracesSteps = trace,
                showsGoals = goals
            };
            // Each stage starts after the one before it ended, so the first one after the proof check sees its goals.
            void Advance(string next)
            {
                RequireNoOpenGoals();
                stage = next;
            }
            if (forceFull) verification.fullImportAudit = (artifact, session, module, leanPath) =>
                verification.VerifyFullImports(artifact, session, module, theorem, leanPath, fullArtifacts);
            if (forceFull) verification.PreflightFullImports(output, fullArtifacts);
            var report = proofRoot is null
                ? verification.Verify(assembly, identity, entry, proof, output,
                    theorem: theorem, existingArtifacts: true, settings: settingsPath, stage: Advance)
                : verification.VerifyConsumer(assembly, proof, output, theorem, proofRoot, settingsPath, Advance);
            RequireNoOpenGoals();

            var view = verification.VerifiedStatement;
            // The certificate records the specification the report shows, read with the statement.
            if (view?.definitions is { } specification)
                File.WriteAllText(reportPath,
                    JsonSerializer.Serialize(report with { specification = specification }, Json) + "\n");
            if (json)
            {
                var refutation = FailureReports.Refuted(report.theoremAudit, theorem, proof, output, proofRoot);
                if (refutation is not null) FailureReports.Write(output, refutation);
                ProofMessagesReport(Observed(verification.ProofMessages, trace, goals).Messages, proof, output);
                Console.Write(VerifyReports.Serialize(VerifyReports.Result("verified", refutation, report.theorem,
                    proof, output, proofRoot, null, report.axioms, view?.statement ?? StatementOf(report),
                    JsonMessages(verification.ProofMessages), trace, verification.ProofMessages is not null,
                    goals, Specification(view))));
                return;
            }
            Console.WriteLine($"Verified: {report.theorem}");
            Console.WriteLine($"  Assembly: {identity}");
            foreach (var line in SubjectLines(view))
                Console.WriteLine("  " + line);
            Console.WriteLine($"  Extraction entry: {entry}");
            if (manifest.TryGetProperty("initializedTypes", out var initializedTypes))
                foreach (var name in initializedTypes.EnumerateArray())
                    Console.WriteLine($"  Caller assumption: {name.GetString()} initialization completed successfully before invocation.");
            if (manifest.TryGetProperty("staticValues", out var staticValues))
                foreach (var name in staticValues.EnumerateArray())
                    Console.WriteLine($"  Caller assumption: {name.GetString()} keeps the value its static constructor stored.");
            if (manifest.TryGetProperty("opaqueStaticValues", out var opaqueValues))
                foreach (var name in opaqueValues.EnumerateArray())
                    Console.WriteLine($"  Unknown static value: {name.GetString()} is not computed; " +
                        "loads read the caller's static binding.");
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
            var statement = view?.statement ?? StatementOf(report);
            foreach (var line in statement.Split('\n'))
                Console.WriteLine("    " + line.TrimEnd());
            Console.Write(SpecificationReport(view));
            var (proofMessages, steps, _) = Observed(verification.ProofMessages, trace, goals);
            Console.Write(ProofMessagesReport(proofMessages, proof, output));
            Console.Write(TraceReport(steps, proof));
        }
        catch (Exception error)
        {
            File.Delete(reportPath);
            // A package's goals are read after its replay and audit, which a `sorry` fails first; a Lean
            // error keeps its own stage and report.
            if (stage is not ("proof checking" or OpenGoalsStage) && OpenGoalCount() is > 0 and var open)
                (stage, error) = (OpenGoalsStage, OpenGoals(open));
            var failed = FailureReports.Failed(stage, error, theorem ?? "ExampleProof.correctness",
                proof ?? Path.Combine(output, "Proof.lean"), output, proofRoot);
            FailureReports.Write(output, failed);
            var (proofMessages, steps, openGoals) = Observed(verification?.ProofMessages, trace, goals);
            // With --goals the terminal shows the goals alone; the proof's messages stay in their file.
            var messages = proof is null ? ""
                : (goals && verification?.ProofMessages is not null ? GoalsReport(openGoals, proof) : "") +
                    ProofMessagesReport(proofMessages, proof, output, listed: !goals) + TraceReport(steps, proof);
            if (json)
            {
                Console.Write(VerifyReports.Serialize(VerifyReports.Result("failed", failed, failed.theorem,
                    failed.proof, output, proofRoot, stage, null, null, JsonMessages(verification?.ProofMessages),
                    trace, verification?.ProofMessages is not null, goals)));
                throw new CliFailure(stage, error, reported: true);
            }
            var failure = new CliFailure(stage, error);
            if (messages.Length > 0) failure.Data[CliDiagnostics.ProofMessagesKey] = messages;
            // A proof Lean or the audit refused is where an author next wants the goals.
            if (!goals && stage is "proof checking" or "theorem audit")
                failure.Data[CliDiagnostics.HintKey] = "Goals: add --goals to print the goal at each `sorry` and " +
                    "failing tactic.";
            throw failure;
        }
        finally
        {
            ((IDisposable?)verification)?.Dispose();
        }
    }

    /// <summary>
    /// Extracts `output` again from its recorded settings when its assembly or the extractor changed since
    /// extraction, and says which; null when both are unchanged. A changed artifact with unchanged inputs is
    /// left for the integrity check to reject.
    /// </summary>
    internal static string? ExtractAgainIfRebuilt(string output)
    {
        var identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
        var assembly = Path.GetFullPath(identity.GetProperty("assemblyPath").GetString()!, output);
        string? reason = !File.Exists(assembly) ? null
            : Sha(assembly) != identity.GetProperty("assemblySha256").GetString() ? "the assembly changed"
            : Sha(ExtractorPath) != identity.GetProperty("extractorSha256").GetString() ? "the extractor changed"
            : null;
        if (reason is not null) Nethermind.LeanCIL.Program.ExtractRecorded(output);
        return reason;
    }

    static IEnumerable<(string, int, int, string)> JsonMessages(ProofMessage[]? messages) =>
        (messages ?? []).Select(message => (message.severity, message.line, message.column, message.text));

    /// <summary>The verified statement as the theorem audit printed it.</summary>
    static string StatementOf(Report report) => report.theoremAudit.Split("'" + report.theorem + "'", 2)[0].Trim();

    /// <summary>
    /// The proof's messages without the step trace, and the trace when the run asked for it; a trace message
    /// in a run that did not ask for one is the proof's own, and stays with its messages.
    /// </summary>
    static (ProofMessage[]? Messages, ProofMessage[]? Trace) Traced(ProofMessage[]? messages, bool trace)
    {
        var (own, steps, _) = Observed(messages, trace, goals: false);
        return (own, steps);
    }

    /// <summary>The stage of a `--goals` run that ended at the goals its proof check left.</summary>
    const string OpenGoalsStage = "open goals";

    /// <summary>
    /// The proof's messages apart from what the observer logged for the run: the step trace under `--trace`
    /// and the open goals under `--goals`. Observer text a run did not ask for is the proof's own message.
    /// </summary>
    static (ProofMessage[]? Messages, ProofMessage[]? Trace, ProofMessage[] Goals) Observed(
        ProofMessage[]? messages, bool trace, bool goals)
    {
        if (messages is null) return (null, null, []);
        bool Step(ProofMessage message) => trace && VerifyReports.IsStep(message.text);
        bool Goal(ProofMessage message) => goals && VerifyReports.Goal(message.text) is not null;
        return ([.. messages.Where(message => !Step(message) && !Goal(message))],
            trace ? [.. messages.Where(Step)] : null, [.. messages.Where(Goal)]);
    }

    /// <summary>
    /// Each open goal at its place in the proof, in source order: the goal at a `sorry`, before a tactic that
    /// raised an error, or left unsolved by a tactic block.
    /// </summary>
    static string GoalsReport(ProofMessage[] goals, string proof)
    {
        if (goals.Length == 0) return "  Goals: none; no `sorry` or failing tactic was reached\n";
        var report = new System.Text.StringBuilder($"  Goals ({goals.Length}):\n");
        foreach (var message in goals)
        {
            var (kind, goal) = VerifyReports.Goal(message.text)!.Value;
            foreach (var line in GoalLines($"{CliPaths.Display(proof)}:{message.line}:{message.column}", kind, goal))
                report.Append(line).Append('\n');
        }
        return report.ToString();
    }

    /// <summary>The report lines of one open goal: its place and kind, then the goal as Lean prints it.</summary>
    static IEnumerable<string> GoalLines(string place, string kind, string goal) =>
        CliDiagnostics.Printable(goal).Split('\n').Select(line => ("      " + line).TrimEnd())
            .Prepend($"    {place}: {kind}");

    static IEnumerable<(string Name, string Text)>? Specification(StatementView? view) =>
        view?.definitions?.Select(definition => (definition.name, definition.text));

    /// <summary>
    /// The proof module's definitions the statement is stated with, such as its precondition and
    /// postcondition, as Lean prints their elaborated bodies; nothing when it uses none.
    /// </summary>
    static string SpecificationReport(StatementView? view)
    {
        if (view?.definitions is not { Length: > 0 } definitions) return "";
        var report = new System.Text.StringBuilder("  Specification:\n");
        foreach (var definition in definitions)
            foreach (var line in CliDiagnostics.Printable(definition.text).Split('\n'))
                report.Append(("    " + line).TrimEnd()).Append('\n');
        return report.ToString();
    }

    /// <summary>
    /// The step trace in full, each step and each tactic's summary at its location in the proof, or nothing
    /// without `--trace`.
    /// </summary>
    static string TraceReport(ProofMessage[]? steps, string proof)
    {
        if (steps is null) return "";
        var report = new System.Text.StringBuilder($"  Trace ({steps.Length} entries):\n");
        foreach (var step in steps)
        {
            var located = $"{CliPaths.Display(proof)}:{step.line}:{step.column}: {CliDiagnostics.Printable(step.text)}";
            foreach (var line in located.Split('\n'))
                report.Append(("    " + line).TrimEnd()).Append('\n');
        }
        return report.ToString();
    }

    const string ProofMessagesText = "proof-messages.txt";
    const int ProofMessageLines = 60;

    /// <summary>
    /// The proof's informational and warning messages located in its source, bounded for the terminal;
    /// the full text is written to proof-messages.txt in the output directory. Unless `listed`, the report
    /// only counts them and names that file.
    /// </summary>
    static string ProofMessagesReport(ProofMessage[]? messages, string proof, string output, bool listed = true)
    {
        if (messages is not { Length: > 0 }) return "";
        var full = string.Concat(messages.Select(message =>
            $"{CliPaths.Display(proof)}:{message.line}:{message.column}: {message.severity}: " +
            $"{CliDiagnostics.Printable(message.text)}\n"));
        var path = Path.Combine(output, ProofMessagesText);
        File.WriteAllText(path, full);
        if (!listed) return $"  Lean messages ({messages.Length}): {CliPaths.Display(path)}\n";
        var lines = full.TrimEnd('\n').Split('\n');
        var report = new System.Text.StringBuilder($"  Lean messages ({messages.Length}):\n");
        foreach (var line in lines.Take(ProofMessageLines))
            report.Append(("    " + line).TrimEnd()).Append('\n');
        if (lines.Length > ProofMessageLines)
            report.Append($"    ... {lines.Length - ProofMessageLines} more lines in {CliPaths.Display(path)}\n");
        return report.ToString();
    }

    /// <summary>
    /// Report lines naming each method the statement names through a framework predicate: `Subject` in
    /// its conclusion, `Premise` in a hypothesis. Nothing is claimed for a method the statement leaves open.
    /// </summary>
    static IEnumerable<string> SubjectLines(StatementView? view)
    {
        if (view is null)
        {
            yield return "Subject: not identified; read the statement below";
            yield break;
        }
        var subjects = view.subjects
            .DistinctBy(subject => (subject.role, subject.head, subject.extracted, subject.method)).ToArray();
        foreach (var subject in subjects)
        {
            var label = subject.role == "premise" ? "Premise" : "Subject";
            var method = subject switch
            {
                { extracted: false } => "a method of a program other than Extracted.program",
                { method: null } => "a method index the statement does not fix",
                { signature: { } signature } => $"{signature} (method {subject.method})",
                _ => $"method {subject.method}, which Extracted.program does not contain"
            };
            yield return $"{label}: {method} via {subject.head}";
        }
        if (!subjects.Any(subject => subject.role != "premise"))
            yield return "Subject: none identified; the conclusion names no method through a framework predicate";
    }
}
