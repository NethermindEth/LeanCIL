using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
    // Only generated, namespace-relative fixtures belong here. Arbitrary consumer
    // proofs keep their original module environment through Verify.
    // Assembly overrides the batch assembly for fixtures generated from a modified copy.
    sealed record GeneratedVerification(string Entry, string Proof, string Output,
        string Theorem = "ExampleProof.correctness", string? Assembly = null, string? Profile = null,
        string[]? InitializedTypes = null);

    // Per-fixture checks are dominated by Lean startup; passes are reported only after the whole batch is certified.
    sealed class GeneratedQueue(Program verification, string assembly, string identity = "Examples")
    {
        readonly List<(GeneratedVerification Request, Action Passed)> pending = [];

        public void Add(GeneratedVerification request, Action passed) => pending.Add((request, passed));

        public void Flush()
        {
            if (pending.Count == 0) return;
            verification.VerifyGeneratedBatch(assembly, identity, pending.Select(item => item.Request).ToArray());
            foreach (var (_, passed) in pending) passed();
            pending.Clear();
        }
    }

    static void ExtractGeneratedBatch(string mode, string identity, IReadOnlyList<GeneratedVerification> requests,
        string profile)
    {
        var path = Path.Combine(Path.GetTempPath(), "leancil-extractions-" + Guid.NewGuid().ToString("N") + ".json");
        try
        {
            File.WriteAllText(path, JsonSerializer.Serialize(requests.Select(request => new
            {
                assembly = request.Assembly, identity, entry = request.Entry, output = request.Output,
                profile = request.Profile ?? profile, initializedTypes = request.InitializedTypes
            })));
            Run(["dotnet", ExtractorPath, "generated-extraction-batch", mode, path]);
        }
        finally { File.Delete(path); }
    }

    // More Lean processes add memory pressure without shortening a typical fixture batch.
    const int MaxBatchShards = 8;

    void VerifyGeneratedBatch(string assembly, string identity, IReadOnlyList<GeneratedVerification> requests,
        string profile = "scalar")
    {
        if (requests.Count == 0) return;
        assembly = Path.GetFullPath(assembly);
        requests = requests.Select(r => r with { Proof = Path.GetFullPath(r.Proof),
            Output = Path.TrimEndingDirectorySeparator(Path.GetFullPath(r.Output)),
            Assembly = Path.GetFullPath(r.Assembly ?? assembly) }).ToArray();
        if (requests.Select(r => Path.GetFullPath(r.Output)).Distinct(StringComparer.OrdinalIgnoreCase).Count() != requests.Count)
            throw new ArgumentException("Batch outputs must be distinct");
        foreach (var request in requests)
        {
            if (!Regex.IsMatch(request.Theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
                throw new ArgumentException("Invalid theorem name");
            Directory.CreateDirectory(request.Output);
            File.Delete(Path.Combine(request.Output, "verified.json"));
        }
        EnsureExtractorBuilt();
        var commonBefore = CommonInputs();
        var before = requests.Select(r => Inputs(commonBefore, r.Proof)).ToArray();
        var session = Library(before[0]);
        var imports = new SortedSet<string>(StringComparer.Ordinal);
        string Body(string source)
        {
            return Regex.Replace(source, @"^import[ \t]+([A-Za-z_][A-Za-z0-9_.]*)[ \t]*\r?$", match =>
            {
                var module = match.Groups[1].Value;
                if (module is not ("Extracted" or "ExtractedSymbols")) imports.Add(module);
                return "";
            }, RegexOptions.Multiline);
        }
        var bodies = new string[requests.Count];
        var hashes = new string[requests.Count];
        ExtractGeneratedBatch("extract", identity, requests, profile);
        for (var i = 0; i < requests.Count; i++)
        {
            var request = requests[i];
            if (HasContractImports(ExtractionIdentity.Read(request.Output)))
                throw new InvalidDataException("Generated batch verification does not support contract imports.");
            hashes[i] = Sha(Path.Combine(request.Output, "identity.json"));
            var body = new StringBuilder();
            body.AppendLine($"namespace BatchCase{i}");
            body.AppendLine(Body(File.ReadAllText(Path.Combine(request.Output, "Extracted.lean"))));
            var proofSource = File.ReadAllText(request.Proof);
            if (ImportsSymbols(proofSource)) body.AppendLine(File.ReadAllText(SymbolsFor(request.Output)));
            body.AppendLine(Body(proofSource));
            body.AppendLine($"end BatchCase{i}");
            bodies[i] = body.ToString();
        }
        // One Lean process elaborates its file on one core, so disjoint shards elaborate in parallel
        // and are replayed and audited together. Largest fixtures go first to the least loaded shard.
        var shardCount = Math.Min(requests.Count, Math.Min(Environment.ProcessorCount, MaxBatchShards));
        var shardOf = new int[requests.Count];
        var loads = new long[shardCount];
        foreach (var i in Enumerable.Range(0, requests.Count).OrderByDescending(i => bodies[i].Length))
        {
            shardOf[i] = Array.IndexOf(loads, loads.Min());
            loads[shardOf[i]] += bodies[i].Length;
        }
        string[] shardModules = [.. Enumerable.Range(0, shardCount).Select(shard => $"Shard{shard}.Batch")];
        var support = imports.Where(n => n.Split('.')[0] is not ("Init" or "Lean" or "Std")).ToArray();
        if (support.Length > 0)
            Run(["lake", "build", .. support], session, progress: "Building generated batch dependencies");
        var currentModules = SessionModules(session);
        var certified = certifiedModules!;
        var altered = certified.Any(pair => !currentModules.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
        var changed = (altered ? currentModules.Keys : currentModules.Keys.Where(name => !certified.ContainsKey(name)))
            .Select(ModuleName).Distinct().ToArray();
        var checker = Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
        var fresh = Path.Combine(Path.GetTempPath(), "leancil-batch-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(fresh);
        try
        {
            var leanPath = fresh + Path.PathSeparator + SessionLeanPath(session);
            if (changed.Length > 0)
            {
                if (!ReplayModulesJointly(session, changed, leanPath, "Kernel replay of generated batch dependencies"))
                    Run([checker, .. changed], leanPath: leanPath, progress: "Kernel replay of generated batch dependencies");
                certifiedModules = currentModules;
            }
            var header = string.Join("\n", imports.Select(n => "import " + n)) + "\n";
            var sources = new string[shardCount];
            for (var shard = 0; shard < shardCount; shard++)
            {
                sources[shard] = Path.Combine(fresh, $"Shard{shard}", "Batch.lean");
                Directory.CreateDirectory(Path.GetDirectoryName(sources[shard])!);
                File.WriteAllText(sources[shard], header + string.Concat(Enumerable.Range(0, requests.Count)
                    .Where(i => shardOf[i] == shard).Select(i => bodies[i])));
            }
            // Building the batch runs its proofs' code; this session's compiled modules must survive it unchanged.
            var bound = OleanHashes(fresh, session);
            var failures = new Exception?[shardCount];
            Parallel.For(0, shardCount, shard =>
            {
                try
                {
                    Run(["lean", "--root=" + fresh, "-o", Path.ChangeExtension(sources[shard], ".olean"), sources[shard]],
                        leanPath: leanPath,
                        progress: $"Checking {requests.Count} generated fixtures, shard {shard + 1} of {shardCount}");
                }
                catch (Exception error) { failures[shard] = error; }
            });
            if (failures.FirstOrDefault(error => error is not null) is { } failure)
                System.Runtime.ExceptionServices.ExceptionDispatchInfo.Throw(failure);
            var built = OleanHashes(fresh, session);
            RequireOnlyAdded(bound, built, [.. shardModules.Select(module => module.Replace('.', '/'))]);
            AuditRequest[] proofAudits = [.. Enumerable.Range(0, requests.Count).SelectMany(i => new[] {
                ProofTheorem($"BatchCase{i}.{requests[i].Theorem}"),
                ExtractionCertificate($"BatchCase{i}.Extracted.translation_valid", $"BatchCase{i}.") })];
            AuditedOleans? audited = null;
            if (Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") != "true")
            {
                try { audited = AuditOleans(leanPath, shardModules, proofAudits, replayTargets: shardModules); }
                catch (InvalidOperationException) { }
            }
            if (audited is null)
            {
                if (!ReplayModulesJointly(session, shardModules, leanPath,
                    $"Kernel replay of {requests.Count} generated fixtures"))
                    Run([checker, .. shardModules], leanPath: leanPath,
                        progress: $"Kernel replay of {requests.Count} generated fixtures");
                audited = AuditOleans(leanPath, shardModules, proofAudits);
            }
            if (!Same(built, OleanHashes(fresh, session)))
                throw new InvalidOperationException("Compiled artifacts changed during verification");
            for (var shard = 0; shard < shardCount; shard++)
                RequireAuditedModule(audited, shardModules[shard], Path.ChangeExtension(sources[shard], ".olean"));
            ExtractGeneratedBatch("check", identity, requests, profile);
            // Every input is checked after the last subprocess, including inputs for earlier fixtures.
            var commonAfter = CommonInputs();
            var reports = new Report[requests.Count];
            for (var i = 0; i < requests.Count; i++)
            {
                var request = requests[i];
                var theorem = $"BatchCase{i}.{request.Theorem}";
                var axioms = AuditedAxioms(audited.theorems[2 * i]);
                AuditedAxioms(audited.theorems[2 * i + 1]);
                if (!Same(before[i], Inputs(commonAfter, request.Proof)) ||
                    hashes[i] != Sha(Path.Combine(request.Output, "identity.json")))
                    throw new InvalidOperationException("Batch inputs changed during verification");
                var extraction = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(request.Output, "identity.json")));
                var initializedTypes = extraction.TryGetProperty("initializedTypes", out var assumptions)
                    ? assumptions.Deserialize<string[]>() : [];
                reports[i] = new Report(4, Sha(request.Assembly!), hashes[i], request.Theorem, axioms, AuditText(audited.theorems[2 * i]), before[i],
                    libraryKey, libraryBuild, AuditText(audited.theorems[2 * i + 1]), initializedTypes, Sha(sources[shardOf[i]]), theorem,
                    staticValues: StaticValueAssumptions(extraction), imports: PublishedImports(extraction),
                    contractDependencies: DeploymentDependencies(extraction),
                    initializationAssumptions: InitializationAssumptions(extraction));
            }
            // Nothing is published until every fixture, certificate and replay passes.
            for (var i = 0; i < requests.Count; i++)
            {
                File.Copy(sources[shardOf[i]], Path.Combine(requests[i].Output, "Batch.lean"), overwrite: true);
                File.WriteAllText(Path.Combine(requests[i].Output, "verified.json"), JsonSerializer.Serialize(reports[i], Json) + "\n");
            }
        }
        finally
        {
            Directory.Delete(fresh, recursive: true);
        }
    }
}
