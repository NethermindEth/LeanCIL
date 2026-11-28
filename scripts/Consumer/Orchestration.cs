using System.Text.Json;

// Consumer and batch proof verification orchestration.
partial class Program
{
    sealed record ConsumerExportAudit(string Source, Action<string, string, string, AuditedOleans> Checked,
        AuditRequest[]? Theorems = null, Dictionary<string, string>? GeneratedSources = null,
        string[]? Closures = null);

    sealed record ConsumerRequest(string Assembly, string Output, string Proof, string Theorem, string? Settings,
        bool ExpectRejection = false, ConsumerExportAudit? ExportAudit = null, StatementRequest? Statement = null);

    sealed class ConsumerOutcome
    {
        public string Stage = "extraction integrity";
        public Report? Report;
        public Exception? Error;
        public bool Rejected;
        public bool Checked;
        public double ElapsedSeconds;
        public string? Detail;
        // Proof modules of other requests in the workspace, omitted from this request's diagnostics.
        public string[]? Hidden;
        // Display only, never read by a check: the proof's Lean messages and its printed statement.
        public ProofMessage[]? Messages;
        public StatementView? Statement;
        // The developer's files the request's workspace copied, which its diagnostics cite.
        public SourceCopies? Sources;

        /// <summary>The proof's messages, each at its position in `proof` rather than in the workspace's copy.
        /// </summary>
        public ProofMessage[]? ProofMessages(string proof) => Sources?.Relocate(proof, Messages) ?? Messages;

        /// <summary>The failure, carrying the workspace's copies so its diagnostics cite the originals.</summary>
        public Exception? Located()
        {
            if (Error is not null && Sources is not null) Error.Data[SourceCopies.Key] = Sources;
            return Error;
        }
    }

    Report VerifyConsumer(string assembly, string proof, string output, string theorem, string root,
        string? settings, Action<string>? stage, DeepCheckInputs? deepChecks = null, DeepCheckRun? deepRun = null)
    {
        ProofMessages = null;
        VerifiedStatement = null;
        var outcome = VerifyConsumerRequests(root, [new(assembly, output, proof, theorem, settings)],
            (_, value) => stage?.Invoke(value), batch: false, deepChecks: deepChecks, deepRun: deepRun)[0];
        ProofMessages = outcome.ProofMessages(proof);
        VerifiedStatement = outcome.Statement;
        if (outcome.Located() is { } error) System.Runtime.ExceptionServices.ExceptionDispatchInfo.Throw(error);
        return outcome.Report!;
    }

    /// <summary>
    /// The non-error messages of `source` in Lake's printed build output, which logs each message of a
    /// module that failed to check as `level: file:line:column: text`, with `file` relative to `package`.
    /// </summary>
    static ProofMessage[] LakeOutputMessages(string output, string package, string source) =>
        SourceMessages(LeanDiagnostics.Entries(output), package, source);

    // Capture all artifact names, including unknown parts used by module discovery.
    static SortedDictionary<string, string> ConsumerArtifactSnapshot(string directory) =>
        HashFiles(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
            .Select(path => (Path.GetRelativePath(directory, path).Replace('\\', '/'), path)));

    /// <summary>Counts each compiled module's recorded parts in one pass.</summary>
    static Dictionary<string, int> ConsumerArtifactCounts(IEnumerable<string> paths)
    {
        Dictionary<string, int> counts = new(StringComparer.Ordinal);
        foreach (var path in paths)
        {
            var module = ModuleName(path);
            counts[module] = counts.GetValueOrDefault(module) + 1;
        }
        return counts;
    }

    /// <summary>Consumer source roots cannot supply the verifier's binding namespaces.</summary>
    static void RequireConsumerDeepNamespaces(IEnumerable<string> sourceDirectories)
    {
        foreach (var directory in sourceDirectories)
            foreach (var module in new[] { "StrictBinding", "BindingAudit" })
            {
                var source = Path.Combine(directory, module);
                if (File.Exists(source + ".lean") || (Directory.Exists(source) &&
                    Directory.EnumerateFiles(source, "*.lean", SearchOption.AllDirectories).Any()))
                    throw new InvalidDataException("Consumer source uses a reserved deep-check namespace: " + source);
            }
    }

    // The replay manifest binds exactly the parts consumed by Lean.
    static SortedDictionary<string, string> ConsumerSnapshotParts(
        IReadOnlyDictionary<string, string> artifacts, string modulePath, string path)
    {
        var parts = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var suffix in new[] { "", ".server", ".private" })
            if (artifacts.TryGetValue(modulePath + suffix, out var hash)) parts[".olean" + suffix] = hash;
            // Filesystem lookup can resolve case variants absent from the ordinal snapshot.
            else if (File.Exists(path + suffix)) parts[".olean" + suffix] = Sha(path + suffix);
        return parts;
    }

    // Verifies requests against one consumer snapshot. Each request gets its own
    // certificate, proof module, theorem audit and failure; requests that share an
    // extraction share one Lake workspace, build and kernel replay.
    // `finished` reports each request once its outcome is final, possibly from parallel workspaces.
    ConsumerOutcome[] VerifyConsumerRequests(string root, IReadOnlyList<ConsumerRequest> requests,
        Action<int, string>? stage, bool batch, int parallelism = 1,
        Action<int, ConsumerOutcome>? finished = null, bool checkOnly = false, DeepCheckInputs? deepChecks = null,
        DeepCheckRun? deepRun = null, Func<Sha256Digest, Sha256Digest>? receiveDigest = null)
    {
        deepRun = DeepCheckRun.Claim(deepChecks, deepRun);
        if (deepChecks is not null && (batch || checkOnly || requests.Count != 1 ||
            requests[0].ExpectRejection || requests[0].ExportAudit is not null))
            throw new InvalidDataException("Deep checks require one ordinary consumer verification request.");
        var requestClock = System.Diagnostics.Stopwatch.StartNew();
        root = Path.GetFullPath(root);
        if (requests.Any(request => request.ExportAudit is not null) && !freshProofs && !freshLibrary)
            throw new InvalidDataException("Contract exports require fresh independent verification.");
        var outcomes = requests.Select(_ => new ConsumerOutcome()).ToArray();
        void CompleteTiming(int index) => outcomes[index].ElapsedSeconds = requestClock.Elapsed.TotalSeconds;
        bool Live(int i) => outcomes[i].Error is null && !outcomes[i].Rejected &&
            !outcomes[i].Checked && outcomes[i].Report is null;
        int[] Pending(IEnumerable<int> members) => members.Where(Live).ToArray();
        void Stage(IEnumerable<int> members, string value)
        {
            foreach (var i in Pending(members))
            {
                outcomes[i].Stage = value;
                stage?.Invoke(i, value);
            }
        }
        void Fail(IEnumerable<int> members, Exception error)
        {
            foreach (var i in Pending(members))
            {
                outcomes[i].Error = error;
                CompleteTiming(i);
            }
        }
        // A build that printed an internal error fails the request whose proof module printed it, whatever the
        // build's exit code; one printed while building anything the requests share fails them all.
        void FailInternalErrors(int[] members, string[] names, string[] command, int code, string output)
        {
            var errors = LeanOutput.InternalErrors(output);
            if (errors.Count == 0) return;
            if (LeanOutput.ByRequest(errors, names) is not { } requests)
                throw LeanOutput.Failure(command, code, output, errors);
            for (var k = 0; k < members.Length; k++)
            {
                var own = requests[k];
                if (own.Length == 0) continue;
                var failure = LeanOutput.Failure(command, code, output, own);
                failure.Data[LeanDiagnostics.HiddenModulesKey] = names.Where((_, other) => other != k).ToArray();
                Fail([members[k]], failure);
            }
        }
        var comparer = CollidingLocationComparer;
        var all = Enumerable.Range(0, requests.Count).ToArray();
        var identities = new Sha256Digest[requests.Count];
        var extractions = new ExtractionIdentity[requests.Count];
        IReadOnlyList<DeepCheckInputs.Pin>? matchedPins = null;
        var proofKeys = new string[requests.Count];
        // Symbols.lean hash for requests whose proofs import ExtractedSymbols, else null.
        var symbols = new string?[requests.Count];
        // Keyed extraction modules each request's proof closure imports, generated as re-exports.
        var selections = requests.Select(_ => Array.Empty<string>()).ToArray();
        var outputs = requests.Select(request => Path.GetFullPath(request.Output)).ToArray();
        var proofs = new string[requests.Count];
        SortedDictionary<string, string> BoundRequestInputs(int index, SortedDictionary<string, string> common)
        {
            SortedDictionary<string, string> inputs = RequestInputs(common, proofs[index], requests[index].Settings);
            if (requests[index].ExportAudit is { } audit)
            {
                inputs["export-audit"] = ContentKey(audit.Source);
                foreach (var (module, source) in audit.GeneratedSources ?? [])
                    inputs["export-generated:" + module] = ContentKey(source);
            }
            return inputs;
        }
        foreach (var i in all)
            try { proofs[i] = Within(root, AbsolutePath(requests[i].Proof)); }
            catch (Exception error) { Fail([i], error); }
        // Only the last request for an output may leave a certificate, as in sequential runs. Spellings that may name
        // one output, through a link or in another case where case is ignored or unknown, can only lose one.
        var locations = outputs.Select(ResolvedPath).ToArray();
        var last = all.GroupBy(i => locations[i], comparer)
            .ToDictionary(group => group.Key, group => group.Max(), comparer);
        foreach (var output in outputs.Distinct(StringComparer.Ordinal))
            File.Delete(Path.Combine(output, "verified.json"));
        var parallel = new ParallelOptions { MaxDegreeOfParallelism = Math.Max(1, parallelism) };
        void CheckExtractions(int[] members, bool reportStage = true)
        {
            if (reportStage) Stage(members, "extraction integrity");
            // Grouped by exact resolved spelling, so every directory is checked whatever its volume's case rule.
            Parallel.ForEach(Pending(members).GroupBy(i => locations[i], StringComparer.Ordinal), parallel, group =>
            {
                try
                {
                    var digest = CheckManifest(["dotnet", ExtractorPath, "check", outputs[group.First()]], receiveDigest);
                    foreach (var member in group)
                        if (extractions[member] is null) identities[member] = digest;
                        else if (identities[member] != digest)
                            Fail([member],
                                new InvalidDataException("Extraction identity changed during verification."));
                }
                catch (Exception error)
                {
                    Fail(group, error);
                }
            });
        }
        CheckExtractions(all);
        foreach (var i in Pending(all))
            try
            {
                extractions[i] = ExtractionIdentity.Read(outputs[i]);
                extractions[i].RequireDigest(identities[i]);
            }
            catch (Exception error) { Fail([i], error); }
        // Cache eligibility is local to each request/group, including parallel groups.
        referenceOnlyAuthoring = false;
        var live = Pending(all);
        if (live.Length == 0) return outcomes;

        // A batch shares one snapshot, so no output may be part of the consumer sources.
        string? excluded = batch ? null : outputs[live[0]];
        SortedDictionary<string, string> ReadInputs(out SortedDictionary<string, string> snapshot)
        {
            var common = CommonInputs();
            snapshot = ConsumerSnapshot(root, excluded, fullBundleDependencies, common);
            foreach (var (key, value) in snapshot) common[key] = value;
            return common;
        }
        var before = new SortedDictionary<string, string>[requests.Count];
        SortedDictionary<string, string> snapshot;
        Stage(live, "consumer source snapshot");
        try
        {
            var common = ReadInputs(out snapshot);
            var sourceLocations = batch ? ConsumerSourceLocations(snapshot) : null;
            var imports = new ConsumerImports(snapshot, root);
            foreach (var i in live)
                try
                {
                    if (sourceLocations?.Contains(locations[i]) == true)
                        throw new InvalidDataException(
                            "Batch outputs must lie outside the consumer sources, for example under artifacts/: " +
                            outputs[i]);
                    before[i] = BoundRequestInputs(i, common);
                    if (!before[i].ContainsKey("consumer:" + proofs[i]))
                        throw new InvalidDataException("Proof must be a Lean source under the consumer root, outside excluded build/artifact directories.");
                    List<(string Module, string Source)> keyed = [];
                    foreach (var import in imports.Generated(proofs[i]))
                    {
                        if (SelectionModules.Is(import.Module)) keyed.Add(import);
                        if (symbols[i] is not null ||
                            import.Module != "ExtractedSymbols" && !SelectionModules.IsSymbols(import.Module)) continue;
                        var path = Path.Combine(outputs[i], "Symbols.lean");
                        if (!File.Exists(path))
                        {
                            Stage([i], "extraction integrity");
                            throw new InvalidOperationException(MissingSymbols(outputs[i]));
                        }
                        symbols[i] = Sha(path);
                    }
                    selections[i] = [.. keyed.DistinctBy(import => import.Module, StringComparer.Ordinal)
                        .SelectMany(import =>
                            SelectionModules.Selected([import.Module], extractions[i].Root, import.Source))];
                }
                catch (Exception error) { Fail([i], error); }
        }
        catch (Exception error)
        {
            Fail(live, error);
            return outcomes;
        }
        void Recheck(int[] members, bool reportStage = true)
        {
            var started = DateTimeOffset.UtcNow;
            var elapsed = System.Diagnostics.Stopwatch.StartNew();
            CheckExtractions(members, reportStage);
            members = Pending(members);
            if (members.Length == 0) return;
            try
            {
                var common = ReadInputs(out _);
                foreach (var i in members)
                    if (!Same(before[i], BoundRequestInputs(i, common)) ||
                        (symbols[i] is not null && (!File.Exists(Path.Combine(outputs[i], "Symbols.lean")) ||
                            symbols[i] != Sha(Path.Combine(outputs[i], "Symbols.lean")))))
                        Fail([i], new InvalidOperationException("Inputs changed during consumer verification"));
            }
            catch (Exception error) { Fail(members, error); }
            Trace("Rechecking consumer inputs", started, root, elapsed.Elapsed,
                members.Any(index => outcomes[index].Error is not null) ? 1 : 0, "", []);
        }

        live = Pending(all);
        if (live.Length == 0) return outcomes;
        if (deepRun is not null)
        {
            Stage(live, "arguments");
            try
            {
                matchedPins = deepRun.Begin(extractions[0]);
            }
            catch (Exception error)
            {
                Fail(live, error);
                return outcomes;
            }
        }
        Stage(live, "Lean library build");
        string certifiedLibrary;
        Dictionary<string, string> certifiedBase;
        ConsumerDependency[] dependencies;
        TrustedSupport[] trusted;
        try
        {
            Library(Inputs(proofs[live[0]], requests[live[0]].Settings));
            if (deepChecks is not null)
            {
                deepRun!.Attempt!.RequireIdentity(extractions[0]);
                foreach (var (module, source) in extractions[0].Sources)
                {
                    var path = Path.Combine(outputs[0], module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
                    if (File.ReadAllText(path) != source)
                        throw new InvalidDataException($"Imported interface source changed: {module}");
                }
                PrepareBindingLibrary(this.session!);
            }
            certifiedLibrary = library!;
            certifiedBase = baseModules!.Where(pair => IsCertifiedLibraryModule(ModuleName(pair.Key))).ToDictionary();
            dependencies = fullBundleDependencies ?? ConsumerDependencies(root);
            trusted = TrustedConsumerSupport(root, before[live[0]]);
            // Resolve lazily initialized identities before any parallel work.
            _ = VerificationPolicy;
            if (UseSuccessCache) _ = ReceiptKey;
        }
        catch (Exception error)
        {
            Fail(live, error);
            return outcomes;
        }
        var cached = new List<int>();
        foreach (var i in live)
        {
            try
            {
                // PDB names bind only proofs that import them; identity.json does not cover the PDB.
                // A result cached without a statement view must not satisfy a run that prints one.
                proofKeys[i] = ConsumerCacheKey("proof", before[i], SemanticExtractionIdentity(extractions[i]) + "\n" + requests[i].Theorem + "\n" + Sha(requests[i].Assembly) +
                    (symbols[i] is null ? "" : "\n" + symbols[i]) + (viewsStatement ? "\nstatement-view" : "") +
                    ProofOptionsKey +
                    (requests[i].Statement is { } statement ? "\nstatement " + JsonSerializer.Serialize(statement) : ""));
                if (deepChecks is not null || checkOnly || requests[i].ExpectRejection ||
                    ReferenceOnlyImports(extractions[i])) continue;
                var receipt = Path.Combine(Path.GetTempPath(), "leancil-consumer-receipt-" + Guid.NewGuid().ToString("N"));
                Directory.CreateDirectory(receipt);
                try
                {
                    if (!RestoreSuccess(proofKeys[i], receipt)) continue;
                    // A receipt whose certificate this run does not accept is a miss, never a failure.
                    if (ReadCertificate(File.ReadAllText(Path.Combine(receipt, "report.json")), BindingMode.Default,
                        out _) is not { } report) continue;
                    var cachedMessages = Path.Combine(receipt, ProofMessagesFile);
                    outcomes[i].Messages = File.Exists(cachedMessages)
                        ? JsonSerializer.Deserialize<ProofMessage[]>(File.ReadAllText(cachedMessages)) : null;
                    outcomes[i].Statement = ReadStatementView(Path.Combine(receipt, StatementViewFile));
                    outcomes[i].Detail = JsonSerializer.Serialize(report with { libraryBuild = "consumer-proof-cache" }, Json);
                    cached.Add(i);
                }
                finally { Directory.Delete(receipt, true); }
            }
            catch (Exception error) { Fail([i], error); }
        }
        if (cached.Count > 0)
        {
            // An unchanged proof reuses its authenticated result; integrity and inputs are still rechecked.
            Recheck([.. cached]);
            foreach (var i in Pending(cached))
            {
                RequireImplementationImports(extractions[i]);
                JsonElement current = extractions[i].Root;
                var report = JsonSerializer.Deserialize<Report>(outcomes[i].Detail!)! with
                {
                    identitySha256 = identities[i].ToString(),
                    assemblySha256 = Sha(requests[i].Assembly), inputs = before[i], imports = PublishedImports(current),
                    contractImports = ContractImportAssumptions(current), contractDependencies = DeploymentDependencies(current)
                };
                outcomes[i].Detail = null;
                if (last[locations[i]] == i)
                    File.WriteAllText(Path.Combine(outputs[i], "verified.json"),
                        JsonSerializer.Serialize(report, Json) + "\n");
                outcomes[i].Report = report;
                CompleteTiming(i);
                CacheProgress("certified consumer proof: " + requests[i].Theorem);
            }
            foreach (var i in cached.Where(i => !Live(i))) finished?.Invoke(i, outcomes[i]);
        }

        var groups = new Dictionary<string, List<int>>(StringComparer.Ordinal);
        foreach (var i in Pending(all))
            try
            {
                var key = $"""
                    {extractions[i].GeneratedSha256}
                    {symbols[i]}
                    {JsonSerializer.Serialize(extractions[i].Sources)}
                    referenceOnly={ReferenceOnlyImports(extractions[i])}
                    """;
                if (!groups.TryGetValue(key, out var members)) groups[key] = members = [];
                members.Add(i);
            }
            catch (Exception error) { Fail([i], error); }
        if (groups.Count == 0) return outcomes;
        var ordered = groups.Values.Select(group => group.ToArray())
            .OrderByDescending(group => group.Count(i => !requests[i].ExpectRejection)).ToArray();
        var componentPlans = new Dictionary<int, ExtractionComponents>();
        foreach (var group in ordered)
            try
            {
                componentPlans[group[0]] = SplitExtractionComponents(
                    File.ReadAllText(Path.Combine(outputs[group[0]], "Extracted.lean")));
            }
            catch (Exception error) { Fail(group, error); }
        ordered = ordered.Where(group => componentPlans.ContainsKey(group[0])).ToArray();
        if (ordered.Length == 0) return outcomes;
        var repeatedComponents = componentPlans.Values.SelectMany(plan => plan.Sources.Keys)
            .GroupBy(module => module, StringComparer.Ordinal).Where(group => group.Count() > 1)
            .Select(group => group.Key).ToHashSet(StringComparer.Ordinal);
        // Only the first workspace publishes in-session support before parallel work.
        // Seed it with the largest common source body; other components stay monolithic.
        ordered = ordered.OrderByDescending(group => componentPlans[group[0]].Sources
            .Where(pair => repeatedComponents.Contains(pair.Key)).Sum(pair => (long)pair.Value.Length)).ToArray();
        repeatedComponents.IntersectWith(componentPlans[ordered[0][0]].Sources.Keys);
        foreach (var index in componentPlans.Keys.ToArray())
        {
            // A common header alone does not justify extra compiler processes. Split only
            // when this batch can reuse method evidence as well as profile/layout metadata.
            componentPlans[index] = SharedExtractionComponents(componentPlans[index], repeatedComponents);
        }
        var sources = ConsumerSourceHashes(snapshot, root);
        bool exporting = !checkOnly && !forceFullVerification &&
            !string.IsNullOrWhiteSpace(Environment.GetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT"));
        var export = new ConsumerSupportExport();
        string supportKey = "";
        string[] relativeImportDirectories = [];
        // Certified extraction-independent support shared by later workspaces.
        var support = Path.Combine(Path.GetTempPath(), "leancil-consumer-restored-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(support);
        var supportArtifacts = new SortedDictionary<string, string>(StringComparer.Ordinal);

        void VerifyGroup(int[] members, string session, bool first, bool share)
        {
            void RequireDeepBindingStable()
            {
                if (deepChecks is not null) RequirePreparedBindingLibrary();
            }
            // The certified library's directory, already on the consumer path, holds the StrictBinding modules.
            (string[] Directories, string LeanPath) ImportDirectories()
            {
                RequireDeepBindingStable();
                return ConsumerImportDirectories(session);
            }
            var components = componentPlans[members[0]];
            bool checkRejectedProofs = members.Any(index => requests[index].ExpectRejection);
            var groupExtraction = extractions[members[0]];
            Dictionary<string, string> bound = new(WithExtraction(sources, groupExtraction.GeneratedSha256),
                StringComparer.Ordinal);
            foreach (var (module, source) in components.Sources)
                bound["<generated>/" + module + ".lean"] = ContentKey(source);
            if (checkRejectedProofs)
                bound["<generated>/ExtractionAudit.lean"] = ContentKey(ExtractionAuditSource);
            foreach ((string module, string source) in extractions[members[0]].Sources)
                bound["<generated>/" + module.Replace('.', '/') + ".lean"] = ContentKey(source);
            var generatedSources = new Dictionary<string, string>(StringComparer.Ordinal);
            foreach (var member in members)
                foreach (var (module, source) in requests[member].ExportAudit?.GeneratedSources ?? [])
                {
                    if (generatedSources.TryGetValue(module, out var previous) && previous != source)
                        throw new InvalidDataException("Conflicting generated export module: " + module);
                    generatedSources[module] = source;
                    bound["<generated>/" + module.Replace('.', '/') + ".lean"] = ContentKey(source);
                }
            foreach (var module in members.SelectMany(member => selections[member]))
            {
                generatedSources[module] = SelectionModules.Source(module);
                bound["<generated>/" + module.Replace('.', '/') + ".lean"] =
                    ContentKey(SelectionModules.Source(module));
            }
            var names =members.Length == 1 ? ["LeanCILProof"] : members.Select((_, k) => "LeanCILProof" + k).ToArray();
            var requestModules = members.Select((member, index) => (member, module: names[index]))
                .ToDictionary(pair => pair.member, pair => pair.module);
            // Groups share one Symbols.lean hash or none.
            var symbolHash = symbols[members[0]];
            var prepared = PrepareConsumerSession(session, root, dependencies, snapshot, certifiedLibrary,
                groupExtraction,
                members.Select((i, k) => (names[k], proofs[i])).ToArray(), symbolHash,
                members.Where(i => requests[i].ExportAudit is not null).ToDictionary(
                    i => requestModules[i], i => requests[i].ExportAudit!.Source, StringComparer.Ordinal),
                generatedSources: generatedSources, components: components, checkRejectedProofs: checkRejectedProofs);
            var generatedPackage = prepared.Generated;
            if (deepChecks is not null)
            {
                var frameworkCopy = Within(session, Path.GetRelativePath(root,
                    dependencies.Single(dependency => dependency.Name == "leancil").Source));
                var packageRoots = dependencies.Where(dependency => dependency.Name != "leancil")
                    .Select(dependency => Within(session, Path.GetRelativePath(root, dependency.Source)))
                    .Prepend(session);
                // Lake lists source directories with links followed, so the session holds them by location.
                RequireConsumerDeepNamespaces(ConsumerSourceDirectories(session, packageRoots)
                    .Where(directory => !SameLocation(directory, frameworkCopy) && Inside(session, directory)));
            }
            foreach (var member in members) outcomes[member].Sources = prepared.Sources;
            var generatedInputPaths = prepared.Copied.Keys.Where(path =>
                    path.StartsWith(generatedPackage + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                .Concat([Path.Combine(generatedPackage, "lakefile.toml"),
                    Path.Combine(generatedPackage, "lean-toolchain")]).ToArray();
            SortedDictionary<string, string> GeneratedInputs() => HashFiles(generatedInputPaths.Select(path =>
                (Path.GetRelativePath(generatedPackage, path).Replace('\\', '/'), path)));
            var generatedInputs = GeneratedInputs();
            var certificateSupportKey = ConsumerCacheKey("generated-certificate-support", generatedInputs,
                JsonSerializer.Serialize(baseModules));
            var interfaceModules = extractions[members[0]].Sources.Keys
                .Where(module => module != "ExtractedImports").ToArray();
            var interfaceModuleNames = interfaceModules.ToHashSet(StringComparer.Ordinal);
            Dictionary<string, string> InterfaceArtifacts() => ModuleArtifacts(generatedPackage)
                .Where(pair => interfaceModuleNames.Contains(ModuleName(pair.Key))).ToDictionary();
            Dictionary<string, string> acceptedInterfaceArtifacts = new(StringComparer.Ordinal);
            void RequireInterfaceArtifacts()
            {
                Dictionary<string, string> current = InterfaceArtifacts();
                if (current.Count != acceptedInterfaceArtifacts.Count ||
                    current.Any(pair => !acceptedInterfaceArtifacts.TryGetValue(pair.Key, out string? accepted) || accepted != pair.Value))
                    throw new InvalidDataException("Published contract interface artifacts changed after their closure audit.");
            }
            string[] initialImportDirectories;
            if (!first && relativeImportDirectories.Length > 0)
                initialImportDirectories = relativeImportDirectories.Select(path => Path.GetFullPath(path, session)).ToArray();
            else if (!first)
                initialImportDirectories = ImportDirectories().Directories;
            else
            {
                initialImportDirectories = ImportDirectories().Directories;
                relativeImportDirectories = initialImportDirectories
                    .Select(path => Path.GetRelativePath(session, path)).ToArray();
                // Lean sources are bound per module inside each generation, not by this key.
                var configuration = prepared.Copied.Where(pair => Path.GetFileName(pair.Key) is "lakefile.toml" or "lakefile.lean" or "lake-manifest.json" or "lean-toolchain")
                    .OrderBy(pair => pair.Key, StringComparer.Ordinal)
                    .Select(pair => Path.GetRelativePath(session, pair.Key).Replace('\\', '/') + ":" + pair.Value);
                supportKey = ConsumerSupportCacheKey(snapshot, relativeImportDirectories, configuration);
                // Workspaces differ in Extracted, so only extraction-independent support is shared.
                supportArtifacts = RestoreConsumerSupport(supportKey, bound, support, dependent: false);
            }
            RestorePortableSupport(session, trusted);
            RequireDeepBindingStable();
            var sharedRecord = ReadConsumerSupportRecord(Path.Combine(support, ConsumerSupportRecordName));
            // Initial persistent restoration already selected and authenticated this bound
            // closure; its copied artifacts do not include the support manifest.
            var sharedFiles = sharedRecord is null ? (first ? supportArtifacts.Keys.ToHashSet(StringComparer.Ordinal)
                    : new HashSet<string>(StringComparer.Ordinal))
                : RestorableConsumerSupport(sharedRecord, bound).SelectMany(module => sharedRecord[module].Files)
                    .ToHashSet(StringComparer.Ordinal);
            var restoredArtifacts = new SortedDictionary<string, string>(supportArtifacts.Where(pair => sharedFiles.Contains(pair.Key))
                .ToDictionary(), StringComparer.Ordinal);
            foreach (var file in restoredArtifacts.Keys)
            {
                var target = Within(session, file);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Within(support, file), target, true);
            }
            if (restoredArtifacts.Count > 0)
            {
                CacheProgress("certified consumer support library");
                RequireDeepBindingStable();
            }
            var certificateRestoration = new SortedDictionary<string, string>(restoredArtifacts, StringComparer.Ordinal);
            // Not part of restoredArtifacts: these are rebuilt only if stale and always replayed.
            SortedDictionary<string, string> RestoreCertificateSupport(string key, bool? dependent,
                IReadOnlyCollection<string>? requiredModules = null)
            {
                var own = Path.Combine(Path.GetTempPath(), "leancil-consumer-dependent-" + Guid.NewGuid().ToString("N"));
                Directory.CreateDirectory(own);
                try
                {
                    var dependentFiles = RestoreConsumerSupport(key, bound, own, dependent, requiredModules);
                    foreach (var file in dependentFiles.Keys)
                    {
                        var target = Within(session, file);
                        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                        File.Copy(Within(own, file), target, true);
                        certificateRestoration[file] = dependentFiles[file];
                    }
                    if (dependentFiles.Count > 0) CacheProgress("certified extraction-dependent consumer modules");
                    RequireDeepBindingStable();
                    return dependentFiles;
                }
                finally { Directory.Delete(own, true); }
            }
            if (supportKey.Length > 0) RestoreCertificateSupport(supportKey, dependent: true);
            if (checkOnly)
            {
                CheckGroup(members, session, names, bound, first, share, prepared);
                return;
            }
            Dictionary<string, AuditedClosure>? checkedClosures = deepChecks is null ? null : [];
            if (interfaceModules.Length > 0)
            {
                Stage(members, "contract interface validation");
                Run(["lake", "build", .. interfaceModules.Select(module => "+" + module + ":olean")], generatedPackage,
                    progress: "Compiling published contract interfaces");
                // The audit, the replay and the proof must all read the bytes compiled here.
                acceptedInterfaceArtifacts = InterfaceArtifacts();
                string interfaceLeanPath = ImportDirectories().LeanPath;
                Stage(members, "kernel replay");
                RequireInterfaceArtifacts();
                RequireDeepBindingStable();
                string InterfaceArtifact(string module) =>
                    Path.Combine(generatedPackage, ".lake/build/lib/lean", module.Replace('.', '/') + ".olean");
                if (!TryReplayContractInterfaces(extractions[members[0]], interfaceModules, interfaceLeanPath,
                        InterfaceArtifact, checkedClosures))
                {
                    Dictionary<string, string> interfaceFailures =
                        ReplayConsumerModules(session, interfaceModules, interfaceLeanPath);
                    if (interfaceFailures.Count > 0)
                        throw new InvalidDataException("Kernel replay rejected published contract interfaces: " +
                            string.Join(", ", interfaceFailures.Keys) + "\n" +
                            string.Join("\n", interfaceFailures.Values));
                    RequireInterfaceArtifacts();
                    CheckContractInterfaces(extractions[members[0]], interfaceModules, interfaceLeanPath,
                        InterfaceArtifact, checkedClosures: checkedClosures);
                }
                RequireInterfaceArtifacts();
            }
            // Snapshot before invoking Lake: configuration elaboration and imported
            // metaprograms must not redefine the source bytes accepted by this run.
            Stage(members, "extraction certificate audit");
            var certificateTarget = checkRejectedProofs ? "+ExtractionAudit:olean" : "+Extracted:olean";
            string[] certificateModules = ["Extracted", .. components.Sources.Keys,
                .. checkRejectedProofs ? new[] { "ExtractionAudit" } : []];
            // Authenticated source-closed artifacts need no no-op Lake invocation. Their
            // bytes are still fixed before proof code, then independently replayed and audited.
            bool GeneratedModulesRestored(IEnumerable<string> modules,
                IReadOnlyDictionary<string, string> artifacts) => modules.All(module =>
            {
                var path = Path.Combine(generatedPackage, ".lake/build/lib/lean", module.Replace('.', '/') + ".olean");
                var relative = Path.GetRelativePath(session, path).Replace('\\', '/');
                var parts = ConsumerModuleParts(path);
                return parts.ContainsKey(".olean") && artifacts.ContainsKey(relative) &&
                    artifacts.ContainsKey(relative[..^".olean".Length] + ".trace") &&
                    parts.All(part => artifacts.TryGetValue(
                        relative[..^".olean".Length] + part.Key, out var hash) && hash == part.Value);
            }) && artifacts.All(pair =>
                File.Exists(Within(session, pair.Key)) && Sha(Within(session, pair.Key)) == pair.Value);
            // Source-matched modules from separate generations can have different compiled imports.
            // Restore the entire extraction closure together before accepting its fixed bytes.
            var previousRestoration = new Dictionary<string, string>(certificateRestoration, StringComparer.Ordinal);
            var coherentCertificate = RestoreCertificateSupport(certificateSupportKey, dependent: null,
                requiredModules: certificateModules);
            var restoredCertificate = GeneratedModulesRestored(certificateModules, coherentCertificate);
            var restorationUnchanged = coherentCertificate.All(pair =>
                previousRestoration.TryGetValue(pair.Key, out var hash) && hash == pair.Value);
            string extractionAudit;
            if (restoredCertificate)
            {
                CacheProgress("certified consumer extraction preparation");
                extractionAudit = "";
            }
            else extractionAudit = Run(["lake", "build", certificateTarget], generatedPackage,
                progress: "Checking consumer extraction certificate");
            Dictionary<string, SortedDictionary<string, string>> ExtractionArtifacts() => certificateModules.ToDictionary(
                module => module, module => ConsumerModuleParts(Path.Combine(generatedPackage,
                    ".lake/build/lib/lean", module.Replace('.', '/') + ".olean")), StringComparer.Ordinal);
            string ExtractionBuildState(string module)
            {
                var path = Path.Combine(generatedPackage, ".lake/build/lib/lean", module.Replace('.', '/'));
                var trace = path + ".trace";
                return "artifact modified=" + File.GetLastWriteTimeUtc(path + ".olean").ToString("O") +
                    ", trace sha256=" + (File.Exists(trace) ? Sha(trace) : "missing") +
                    ", trace modified=" + File.GetLastWriteTimeUtc(trace).ToString("O");
            }
            var checkedExtractionArtifacts = ExtractionArtifacts();
            var checkedBuildStates = certificateModules.ToDictionary(module => module, ExtractionBuildState);
            void RequireExtractionArtifacts()
            {
                var changes = new List<string>();
                foreach (var (module, current) in ExtractionArtifacts())
                {
                    var accepted = checkedExtractionArtifacts[module];
                    foreach (var part in accepted.Keys.Union(current.Keys, StringComparer.Ordinal))
                    {
                        var beforeHash = accepted.GetValueOrDefault(part, "missing");
                        var afterHash = current.GetValueOrDefault(part, "missing");
                        if (beforeHash == afterHash) continue;
                        changes.Add($"{module}{part}: sha256 before={beforeHash}, after={afterHash}\n" +
                            $"  before: {checkedBuildStates[module]}\n  after: {ExtractionBuildState(module)}");
                    }
                }
                if (changes.Count == 0) return;
                Stage(members, "extraction integrity");
                throw new InvalidDataException("Extraction certificate artifacts changed during proof checking.\n" +
                    "Preparation: " + (restoredCertificate ? "restored" : "built") +
                    "; package: " + generatedPackage + "\n" + string.Join("\n", changes));
            }
            // Generated reference modules must be fixed before consumer configuration or proof code can run.
            SortedDictionary<string, string> GeneratedArtifacts()
            {
                var directory = Path.Combine(generatedPackage, ".lake/build/lib/lean");
                return HashFiles(generatedSources.Keys.SelectMany(module =>
                {
                    var path = Within(directory, module.Replace('.', '/') + ".olean");
                    return Directory.EnumerateFiles(Path.GetDirectoryName(path)!, Path.GetFileName(path) + "*")
                        .Select(part => (Path.GetRelativePath(directory, part), part));
                }));
            }
            if (generatedSources.Count > 0)
            {
                if (restorationUnchanged && GeneratedModulesRestored(generatedSources.Keys, certificateRestoration))
                    CacheProgress("certified fixed export references");
                else
                    Run(["lake", "build", .. generatedSources.Keys.Select(module => "+" + module + ":olean")],
                        generatedPackage, progress: "Checking fixed export reference modules");
            }
            var fixedGeneratedArtifacts = GeneratedArtifacts();
            if (generatedSources.Keys.Any(module => !fixedGeneratedArtifacts.ContainsKey(
                (module.Replace('.', '/') + ".olean").Replace('/', Path.DirectorySeparatorChar))))
                throw new InvalidDataException("Missing compiled export reference module");
            void RequireGeneratedArtifacts()
            {
                var current = GeneratedArtifacts();
                if (current.Count != fixedGeneratedArtifacts.Count || fixedGeneratedArtifacts.Any(pair =>
                    !current.TryGetValue(pair.Key, out var hash) || hash != pair.Value))
                    throw new InvalidDataException("Generated export artifacts changed during proof checking");
            }
            if (first && share)
            {
                var packageRoots = dependencies.Select(dependency =>
                    Within(session, Path.GetRelativePath(root, dependency.Source))).Prepend(session);
                var sourceDirectories = ConsumerSourceDirectories(session, packageRoots);
                var candidates = ConsumerSupportCandidates(
                    ordered.SelectMany(group => group).Select(index =>
                        Within(session, Path.GetRelativePath(root, proofs[index]))),
                    sourceDirectories, ordered.SelectMany(group => group)
                        .SelectMany(index => extractions[index].Sources.Keys),
                    Path.Combine(Toolchain, "lib/lean"));
                if (candidates.Length > 0)
                {
                    // A scheduling miss or an invalid later proof must not prevent other groups from verifying.
                    Execute(["lake", "build", .. candidates.Select(module => "+" + module + ":olean")], session,
                        progress: "Building shared consumer support");
                }
            }
            Stage(members, "proof checking");
            string[] importModules = extractions[members[0]].Sources.Keys.ToArray();
            if (importModules.Length > 0)
                Run(["lake", "build", .. importModules.Select(module => "+" + module + ":olean")], generatedPackage,
                    progress: "Checking consumer contract interfaces and import assumptions");
            string[] command = ["lake", "build", .. names.Select(name => "+" + name + ":olean")];
            var build = Execute(command, session, progress: "Building fresh consumer proof and dependencies",
                internalErrors: false);
            RequireDeepBindingStable();
            RequireExtractionArtifacts();
            RequireGeneratedArtifacts();
            FailInternalErrors(members, names, command, build.Code, build.Output);
            var buildFailure = build.Code == 0 ? null
                : new InvalidOperationException($"Command failed ({build.Code}): {string.Join(' ', command)}\n{build.Output}");
            string[] importDirectories = [];
            var leanPath = "";
            bool[] built = [false];
            if (buildFailure is null || members.Length > 1)
            {
                if (members.Length == 1) Stage(members, "kernel replay");
                (importDirectories, leanPath) = ImportDirectories();
                // Lake writes a module's olean and trace only after it checks successfully.
                built = names.Select(name => importDirectories.Any(directory =>
                    File.Exists(Path.Combine(directory, name + ".olean")) && File.Exists(Path.Combine(directory, name + ".trace")))).ToArray();
                if (buildFailure is null && !built.All(value => value))
                    throw new InvalidDataException("Consumer proof or certificate is missing from the resolved import paths.");
                // Display only: later audit failures still show the messages of a proof that checked.
                for (var k = 0; k < members.Length; k++)
                    if (built[k])
                        outcomes[members[k]].Messages = LakeTraceMessages(ProofModule(members[k]) + ".trace", session,
                            Path.Combine(session, names[k] + ".lean"));
            }
            // The built proof module of a request, as a path without extension.
            string ProofModule(int i) => importDirectories
                .Select(directory => Path.Combine(directory, requestModules[i]))
                .First(path => File.Exists(path + ".olean"));
            var rejecting = new List<int>();
            for (var k = 0; k < members.Length; k++)
            {
                var i = members[k];
                if (!built[k])
                {
                    // Display only: a module that failed to check has no trace, so its messages come from the log.
                    outcomes[i].Messages = LakeOutputMessages(build.Output, session,
                        Path.Combine(session, names[k] + ".lean"));
                    if (requests[i].ExpectRejection) rejecting.Add(i);
                    else if (members.Length == 1) Fail([i], buildFailure!);
                    else
                    {
                        // Same message; the summary omits the other requests' own proof modules.
                        var own = new InvalidOperationException(buildFailure!.Message);
                        own.Data[LeanDiagnostics.HiddenModulesKey] = names.Where((_, m) => m != k).ToArray();
                        Fail([i], own);
                    }
                }
                else if (requests[i].ExpectRejection)
                    Fail([i], new InvalidOperationException("Expected proof checking to reject " + requests[i].Theorem + ", but the proof checked."));
            }
            if (rejecting.Count > 0)
            {
                // A rejection counts only for unchanged inputs and an intact extraction.
                Recheck([.. rejecting]);
                foreach (var i in Pending(rejecting))
                {
                    outcomes[i].Stage = "proof checking";
                    outcomes[i].Detail = buildFailure!.Message;
                    if (members.Length > 1) outcomes[i].Hidden = names.Where((_, m) => members[m] != i).ToArray();
                    outcomes[i].Rejected = true;
                    CompleteTiming(i);
                }
            }
            var proceeding = Pending(members);
            if (proceeding.Length == 0) return;
            Stage(proceeding, "kernel replay");
            // Replay every consumer/external module, including unused declarations.
            // Only identical artifacts in the validated framework package can reuse
            // the base certificate; a same-named consumer module cannot inherit it.
            if (!initialImportDirectories.SequenceEqual(importDirectories))
                throw new InvalidDataException("Consumer import paths changed during verification.");
            var supportUnchanged = restoredArtifacts.Count > 0 && restoredArtifacts.Where(pair =>
                Path.GetFileName(pair.Key).Contains(".olean", StringComparison.Ordinal)).All(pair =>
                File.Exists(Within(session, pair.Key)) && Sha(Within(session, pair.Key)) == pair.Value);
            var frameworkModules = CertifiedModuleDirectory(certifiedLibrary);
            var generatedModules = Path.GetFullPath(Path.Combine(generatedPackage, ".lake/build/lib/lean"));
            // No external commands run between this snapshot and the replay manifest.
            // Recorded base modules take their hashes from the producer's manifest; unrecorded ones are replayed.
            SortedDictionary<string, string> DirectoryArtifacts(string directory) =>
                LocationComparer.Equals(directory, frameworkModules) ? BaseModuleArtifacts()
                    : ConsumerArtifactSnapshot(directory);
            var existingDirectories = importDirectories.Where(Directory.Exists).ToArray();
            (string Directory, SortedDictionary<string, string> Artifacts)[] ReadArtifacts() =>
                existingDirectories.Select(directory => (directory, DirectoryArtifacts(directory))).ToArray();
            var artifactSnapshots = ReadArtifacts();
            DeepSessionContribution? deep = null;
            if (deepChecks is not null)
            {
                foreach (var (_, artifacts) in artifactSnapshots)
                    if (artifacts.Keys.Any(path => ModuleName(path) is "BindingAudit" ||
                        ModuleName(path).StartsWith("BindingAudit.", StringComparison.Ordinal)))
                        throw new InvalidDataException("Consumer module uses the reserved BindingAudit namespace.");
                var extractedPaths = artifactSnapshots.SelectMany(snapshot => snapshot.Artifacts.Keys
                    .Where(path => path == "Extracted.olean")
                    .Select(path => Path.Combine(snapshot.Directory, path))).ToArray();
                if (extractedPaths.Length != 1 || !LocationComparer.Equals(extractedPaths[0],
                    Path.Combine(generatedModules, "Extracted.olean")))
                    throw new InvalidDataException("Deep checks require the consumer's generated Extracted module.");
                if (Directory.Exists(Path.Combine(session, "BindingAudit")) ||
                    File.Exists(Path.Combine(session, "BindingAudit.lean")))
                    throw new InvalidDataException("Consumer source uses the reserved BindingAudit namespace.");
                static SortedDictionary<string, string> PhysicalArtifacts(
                    (string Directory, SortedDictionary<string, string> Artifacts)[] snapshots) => new(snapshots
                    .SelectMany(snapshot => snapshot.Artifacts.Select(pair =>
                        KeyValuePair.Create(Path.GetFullPath(Path.Combine(snapshot.Directory, pair.Key)), pair.Value)))
                    .ToDictionary(), StringComparer.Ordinal);
                var priorArtifacts = PhysicalArtifacts(artifactSnapshots);
                Stage(proceeding, "deep checks");
                RequireDeepBindingStable();
                RequireOnlyAdded(priorArtifacts, PhysicalArtifacts(ReadArtifacts()));
                var deepRoot = Path.Combine(session, ".deep-checks");
                Directory.CreateDirectory(deepRoot);
                leanPath += Path.PathSeparator + deepRoot;
                deep = BuildDeepSession(deepRoot, leanPath, extractedPaths[0],
                    extractions[members[0]], matchedPins!, () => Stage(proceeding, "deep-check sources"),
                    ConsumerDeepEnvironment(), checkedClosures);
                if (deep.Restored)
                {
                    deepCacheHits++;
                    CacheProgress("certified consumer deep checks: " + requests[members[0]].Theorem);
                }
                importDirectories = [.. importDirectories, deepRoot];
                artifactSnapshots = [.. ReadArtifacts(), (deepRoot, ConsumerArtifactSnapshot(deepRoot))];
                RequireOnlyAdded(priorArtifacts, PhysicalArtifacts(artifactSnapshots), [.. deep.Artifacts
                    .Where(pair => pair.Key != "Extracted").Select(pair => Path.ChangeExtension(pair.Value, null)!) ]);
                RequireDeepBindingStable();
            }
            // The module parts on the import path now, in the shape of the replay manifest.
            Dictionary<string, SortedDictionary<string, string>> ImportArtifactParts() => importDirectories
                .Where(Directory.Exists).SelectMany(directory =>
                {
                    var artifacts = DirectoryArtifacts(directory);
                    return Directory.EnumerateFiles(directory, "*.olean", SearchOption.AllDirectories).Select(path =>
                    {
                        var relative = Path.GetRelativePath(directory, path).Replace('\\', '/');
                        return (Name: ModuleName(relative), Parts: ConsumerSnapshotParts(artifacts, relative, path));
                    });
                })
                .OrderBy(pair => pair.Name, StringComparer.Ordinal).ToDictionary(pair => pair.Name, pair => pair.Parts);
            var baseUnchanged = importDirectories.Any(path => LocationComparer.Equals(path, frameworkModules));
            var certifiedCounts = ConsumerArtifactCounts(certifiedBase.Keys);
            var interfaceCounts = ConsumerArtifactCounts(acceptedInterfaceArtifacts.Keys);
            var moduleNames = new HashSet<string>(StringComparer.Ordinal);
            var discovered = new List<(string Name, bool Certified)>();
            foreach (var (directory, artifacts) in artifactSnapshots)
            {
                foreach (var module in artifacts.GroupBy(pair => ModuleName(pair.Key)))
                {
                    if (!moduleNames.Add(module.Key)) throw new InvalidDataException("Ambiguous consumer module: " + module.Key);
                    if (File.Exists(Path.Combine(Toolchain, "lib/lean", module.Key.Replace('.', '/') + ".olean")))
                        throw new InvalidDataException("Consumer module shadows the trusted Lean toolchain: " + module.Key);
                    var unchanged = LocationComparer.Equals(directory, frameworkModules) &&
                        module.Count() == certifiedCounts.GetValueOrDefault(module.Key) &&
                        module.All(pair => certifiedBase.TryGetValue(pair.Key, out var hash) && hash == pair.Value);
                    if (deep is not null && !unchanged && (module.Key == BindingLibrary ||
                            module.Key.StartsWith(BindingLibrary + ".", StringComparison.Ordinal)))
                        throw new InvalidDataException(
                            "Consumer module shadows the prepared StrictBinding library: " + module.Key);
                    if (!unchanged && IsCertifiedLibraryModule(module.Key)) baseUnchanged = false;
                    var certifiedSupport = supportUnchanged && module.All(pair =>
                    {
                        var relative = Path.GetRelativePath(session, Path.Combine(directory, pair.Key));
                        return restoredArtifacts.TryGetValue(relative.Replace('\\', '/'), out var hash) && hash == pair.Value;
                    });
                    bool publishedInterface = LocationComparer.Equals(directory, generatedModules) &&
                        interfaceModuleNames.Contains(module.Key);
                    if (publishedInterface && (module.Count() != interfaceCounts.GetValueOrDefault(module.Key) ||
                        module.Any(pair => !acceptedInterfaceArtifacts.TryGetValue(pair.Key, out string? accepted) || accepted != pair.Value)))
                        throw new InvalidDataException("Published contract interface artifacts changed after their closure audit: " + module.Key);
                    discovered.Add((module.Key,
                        unchanged || certifiedSupport || publishedInterface));
                }
            }
            if (!moduleNames.Contains("Extracted") || (checkRejectedProofs && !moduleNames.Contains("ExtractionAudit")) ||
                proceeding.Any(i => !moduleNames.Contains(requestModules[i])))
                throw new InvalidDataException("Consumer proof or certificate is missing from the resolved import paths.");
            var mainArtifacts = artifactSnapshots.SelectMany(snapshot =>
                Directory.EnumerateFiles(snapshot.Directory, "*.olean", SearchOption.AllDirectories)
                    .Select(path => (Name: ModuleName(Path.GetRelativePath(snapshot.Directory, path)
                        .Replace('\\', '/')), Path: path, Parts: ConsumerSnapshotParts(snapshot.Artifacts,
                            Path.GetRelativePath(snapshot.Directory, path).Replace('\\', '/'), path)))).ToArray();
            var currentArtifacts = mainArtifacts
                .ToDictionary(pair => pair.Name, pair => pair.Path, StringComparer.Ordinal);
            var checkedArtifacts = JsonSerializer.Serialize(mainArtifacts.OrderBy(pair => pair.Name, StringComparer.Ordinal)
                .ToDictionary(pair => pair.Name, pair => pair.Parts));
            // Every deep stability check independently verifies the prepared library and contribution files.
            // Keep checking every family name, including companions those inventories do not cover.
            var guardedFiles = deep is null ? null : bindingPreparation!.BaseArtifacts.Keys
                .Select(name => Path.GetFullPath(Path.Combine(frameworkModules, name)))
                .Concat(deep.Hashes.Keys).ToHashSet(StringComparer.Ordinal);
            SortedDictionary<string, string> OtherArtifactHashes() =>
                HashFiles(ModuleFamilyParts(currentArtifacts.Values)
                    .Where(path => !guardedFiles!.Contains(path)).Select(path => (path, path)));
            var checkedPhysicalArtifacts = deep is null ? null : OtherArtifactHashes();
            void RequireDeepStable()
            {
                if (deep is null) return;
                deep.RequireStable();
                RequireDeepBindingStable();
                RequireExtractionArtifacts();
                RequireGeneratedArtifacts();
                RequireInterfaceArtifacts();
                if (!Same(checkedPhysicalArtifacts!, OtherArtifactHashes()) ||
                    checkedArtifacts != JsonSerializer.Serialize(ImportArtifactParts()) ||
                    prepared.Copied.Any(pair => !File.Exists(pair.Key) || Sha(pair.Key) != pair.Value))
                    throw new InvalidDataException("Deep-check consumer sources or compiled artifacts changed.");
            }
            void RequireDiagnosticInputs()
            {
                if (auditExecutable is not null) CheckedAuditExecutable();
                Recheck(proceeding, reportStage: false);
                foreach (var index in proceeding)
                {
                    if (!Live(index)) throw outcomes[index].Error!;
                    deepRun?.Attempt?.RequireIdentity(extractions[index]);
                }
                RequireCertifiedLibraryContents();
                RequireDeepStable();
            }
            var portableSupport = ImportedConsumerSupport(session, trusted, currentArtifacts,
                publishReceipts: deepChecks is null);
            var graph = members.Length > 1 || share || UseSuccessCache || exporting || restoredArtifacts.Count > 0 || symbolHash is not null
                ? ConsumerModuleImports(session, currentArtifacts) : null;
            // Cached support was checked against another Extracted or PDB, so its importers are always replayed.
            var extractionDependent = graph is null ? new HashSet<string>(StringComparer.Ordinal)
                : DependentModules(graph, ["Extracted", "ExtractedSymbols"]);
            // A restored deep result was replayed against these Extracted bytes and certified library, which a
            // package shadowing a CIL module would no longer import, so it is replayed again then.
            HashSet<string> restoredDeep = deep is { Restored: true } && baseUnchanged
                ? [.. deep.Modules.Where(module => module != "Extracted")] : [];
            var replayTargets = discovered.Where(module => !restoredDeep.Contains(module.Name) &&
                (!baseUnchanged || extractionDependent.Contains(module.Name) ||
                    (!module.Certified && !portableSupport.Contains(module.Name))))
                .Select(module => module.Name).ToArray();
            if (deep is not null)
                replayTargets = [.. replayTargets.Concat(deep.Modules.Where(module => !restoredDeep.Contains(module)))
                    .Distinct(StringComparer.Ordinal)];
            Dictionary<int, AuditedOleans>? combinedAudits = null;
            bool jointReplayRejected = false;
            bool jointReplaySucceeded = false;
            var premise = ImportPremise(extractions[proceeding[0]]);
            var premiseIdentity = JsonSerializer.Serialize(premise);
            var replayedNames = replayTargets.ToHashSet(StringComparer.Ordinal);
            // Duplicate declarations in skipped support must not select another request's proof body.
            bool completeConsumerReplay = discovered.All(module => IsCertifiedLibraryModule(module.Name) ||
                replayedNames.Contains(module.Name));
            string[] AuditModules(int index) => [requestModules[index], "Extracted",
                .. HasContractImports(extractions[index]) ? ["ExtractedImports"] : Array.Empty<string>(),
                .. deep?.Modules.Where(module => module != "Extracted") ?? []];
            AuditRequest[] BindingRequestsForConsumer() => deep is null
                ? [ExtractionCertificate("Extracted.translation_valid")]
                : [.. deep.Requests.Select(request => request.Audit)];
            if (deep is not null && deep.Requests.Any(request => request.Audit.name == requests[members[0]].Theorem))
                throw new InvalidDataException("Proof theorem collides with a deep-check request: " +
                    requests[members[0]].Theorem);
            AuditRequest Statemented(int index, AuditRequest audit) =>
                requests[index].Statement?.Apply(audit) ?? audit;
            AuditRequest ScopedProof(int index)
            {
                var audit = Statemented(index, ProofTheorem(requests[index].Theorem, extractions[index]));
                // Another proof's declarations must not satisfy this request's missing theorem.
                return members.Length == 1 ? audit : audit with
                {
                    allowedModules = ImportClosure(graph!, AuditModules(index)).Order(StringComparer.Ordinal).ToArray()
                };
            }
            static bool RetainScopedAudit(string? error) => error is null || error.StartsWith(
                "Theorem dependency is outside its request's import closure:", StringComparison.Ordinal);
            RequireDeepStable();
            if (replayTargets.Length > 0 && fullImportAudit is null &&
                (members.Length == 1 || completeConsumerReplay) &&
                proceeding.All(index => (requests[index].ExportAudit is null || members.Length == 1) &&
                    JsonSerializer.Serialize(ImportPremise(extractions[index])) == premiseIdentity) &&
                Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") != "true")
            {
                try
                {
                    var exportAudit = members.Length == 1 ? requests[proceeding[0]].ExportAudit : null;
                    var proofAudits = exportAudit?.Theorems ?? proceeding.Select(ScopedProof).ToArray();
                    var audited = AuditOleans(leanPath,
                        proceeding.SelectMany(AuditModules).Distinct(StringComparer.Ordinal).ToArray(),
                        [.. proofAudits, .. BindingRequestsForConsumer()],
                        premise, closures: exportAudit?.Closures, replayTargets: replayTargets);
                    jointReplaySucceeded = true;
                    combinedAudits = exportAudit is not null || deep is not null
                        ? new Dictionary<int, AuditedOleans> { [proceeding[0]] = audited }
                        : proceeding.Select((index, position) => (index, position))
                        // A conservative owner scope may omit a transitive toolchain import.
                        // Hidden target dependencies are definitive failures, never audit-only fallbacks.
                        .Where(item => RetainScopedAudit(audited.theorems[item.position].error))
                        .ToDictionary(item => item.index, item => audited with
                        {
                            theorems = [audited.theorems[item.position], audited.theorems[^1]]
                        });
                }
                // An ineligible or rejected joint set still needs individual failure attribution.
                catch (InvalidOperationException error)
                {
                    // Eligibility or metadata failures may still permit a plain joint replay.
                    jointReplayRejected = error.Message.Contains("while replaying declaration", StringComparison.Ordinal);
                }
            }
            HashSet<string>? RequestClosure(int index) => graph is null ? null
                : ImportClosure(graph, [requestModules[index], "Extracted",
                    .. checkRejectedProofs ? new[] { "ExtractionAudit" } : [],
                    .. HasContractImports(extractions[index]) ? ["ExtractedImports"] : Array.Empty<string>(),
                    .. deep?.Modules ?? []]);
            var failures = new Dictionary<string, string>();
            if (!jointReplaySucceeded)
            {
                if (deep is not null) RequireDiagnosticInputs();
                if (members.Length == 1)
                    // The failed fused audit already tried this exact joint target set.
                    failures = jointReplayRejected
                        ? ReplayConsumerModulesSeparately(session, replayTargets, leanPath, profile: false)
                        : ReplayConsumerModules(session, replayTargets, leanPath);
                else
                    foreach (int index in proceeding)
                    {
                        // A sibling's undeclared constants must not make another proof replay successfully.
                        var closure = RequestClosure(index)!;
                        // An unchanged dependency already rejected by isolated replay dooms this request too.
                        if (failures.Keys.Any(closure.Contains)) continue;
                        var ownTargets = replayTargets.Where(closure.Contains).ToArray();
                        bool ownKernelRejected = false;
                        if (jointReplayRejected && ownTargets.Length > 0)
                        {
                            try
                            {
                                var audited = AuditOleans(leanPath, AuditModules(index),
                                    [ScopedProof(index), ExtractionCertificate("Extracted.translation_valid")],
                                    premise, replayTargets: ownTargets);
                                // Only this request's exact scope has been replayed and audited.
                                if (RetainScopedAudit(audited.theorems[0].error))
                                {
                                    combinedAudits ??= [];
                                    combinedAudits[index] = audited;
                                }
                                continue;
                            }
                            catch (InvalidOperationException error)
                            {
                                ownKernelRejected = error.Message.Contains(
                                    "while replaying declaration", StringComparison.Ordinal);
                            }
                        }
                        var own = ownKernelRejected
                            ? ReplayConsumerModulesSeparately(session, ownTargets, leanPath, profile: false)
                            : ReplayConsumerModules(session, ownTargets, leanPath);
                        foreach (var (module, error) in own) failures.TryAdd(module, error);
                    }
            }
            if (deep is not null && failures.Count > 0)
            {
                Stage(proceeding, "replay diagnostics");
                RequireDiagnosticInputs();
                Dictionary<string, ReplayRejection>? rejections = null;
                try
                {
                    rejections = DiagnoseReplayFailures(session, deep.OwnedFailures(failures.Keys), leanPath);
                }
                catch (Exception) { }
                RequireDiagnosticInputs();
                if (rejections is not null) deep.RejectReplay(rejections, deepRun?.Attempt);
            }
            foreach (var i in proceeding)
            {
                // A request depends only on its own proof's import closure and the extraction certificate.
                var closure = RequestClosure(i);
                var rejected = failures.Keys.Where(name => closure is null || closure.Contains(name)).Order(StringComparer.Ordinal).ToArray();
                if (rejected.Length > 0)
                    Fail([i], new InvalidOperationException("Kernel replay rejected " + string.Join(", ", rejected) + ":\n" +
                        string.Join("\n", rejected.Select(name => failures[name]))));
            }
            proceeding = Pending(proceeding);
            if (proceeding.Length == 0) return;
            // Audit the certificate and proof in one import environment containing only replayed oleans.
            var audits = new Dictionary<int,
                (string Audit, string[] Axioms, AuditedOleans Result, AuditedTheorem Proof,
                    VerifiedRefutation? Refutation)>();
            string certificateText = "";
            foreach (var i in proceeding)
            {
                try
                {
                    Stage([i], "extraction certificate audit");
                    var module = requestModules[i];
                    string[] auditModules = AuditModules(i);
                    AuditRequest[] proofAudits = requests[i].ExportAudit?.Theorems ??
                        [Statemented(i, ProofTheorem(requests[i].Theorem, extractions[i]))];
                    var audited = combinedAudits?.GetValueOrDefault(i) ?? AuditOleans(leanPath, auditModules,
                        [.. proofAudits, .. BindingRequestsForConsumer()], ImportPremise(extractions[i]),
                        closures: requests[i].ExportAudit?.Closures);
                    foreach (string audit in auditModules) RequireAuditedModule(audited, audit, currentArtifacts[audit]);
                    var namedAudits = audited.theorems.ToDictionary(result => result.name, StringComparer.Ordinal);
                    var expectedNames = proofAudits.Concat(BindingRequestsForConsumer())
                        .Select(request => request.name).ToHashSet(StringComparer.Ordinal);
                    if (!expectedNames.SetEquals(namedAudits.Keys))
                        throw new InvalidDataException("Consumer audit returned an unexpected theorem set.");
                    var certificateAudit = namedAudits["Extracted.translation_valid"];
                    AuditedAxioms(certificateAudit);
                    certificateText = AuditText(certificateAudit);
                    Stage([i], "theorem audit");
                    RequireAuditedConstants(audited);
                    deep?.RequireAudited(audited);
                    deepRun?.Attempt?.RequireIdentity(extractions[i]);
                    if (deep is not null)
                    {
                        Recheck([i], reportStage: false);
                        if (!Live(i)) throw outcomes[i].Error!;
                        RequireCertifiedLibraryContents();
                    }
                    RequireDeepStable();
                    deep?.RequireTheorems(audited, [.. proofAudits, .. BindingRequestsForConsumer()],
                        deepRun?.Attempt);
                    foreach (AuditedTheorem checkedTheorem in audited.theorems) AuditedAxioms(checkedTheorem);
                    var proofAudit = namedAudits[proofAudits[0].name];
                    var refutation = ExtractedRefutation(proofAudit, extractions[i].Root,
                        required: requests[i].Statement?.Refuted == true && proofAudit.matches == true);
                    audits[i] = (AuditText(proofAudit), AuditedAxioms(proofAudit), audited, proofAudit, refutation);
                }
                catch (Exception error) { Fail([i], error); }
            }
            extractionAudit += certificateText;
            proceeding = Pending(proceeding);
            if (proceeding.Length == 0) return;
            Recheck(proceeding);
            proceeding = Pending(proceeding);
            if (proceeding.Length == 0) return;
            if (prepared.Copied.Any(pair => !File.Exists(pair.Key) || Sha(pair.Key) != pair.Value))
                throw new InvalidOperationException("Sources changed in the fresh consumer build");
            if (checkedArtifacts != JsonSerializer.Serialize(ImportArtifactParts()))
                throw new InvalidOperationException("Compiled artifacts changed during consumer verification");
            RequireDeepStable();
            bool contractExportAudit = proceeding.Any(i => requests[i].ExportAudit is not null);
            foreach (int i in proceeding)
                requests[i].ExportAudit?.Checked(session, requestModules[i], leanPath, audits[i].Result);
            Dictionary<int, FullImportResult> fullResults = new();
            foreach (int i in proceeding)
                if (fullImportAudit is not null)
                    fullResults.Add(i, fullImportAudit(outputs[i], session, requestModules[i], leanPath));
            if (contractExportAudit || fullResults.Count > 0)
            {
                // Only callbacks can run further verification code after the first recheck.
                RequireDeepStable();
                Recheck(proceeding);
                proceeding = Pending(proceeding);
                if (proceeding.Length == 0) return;
                RequireGeneratedArtifacts();
                string auditKind = contractExportAudit ? "contract export audit" : "full import audit";
                if (prepared.Copied.Any(pair => !File.Exists(pair.Key) || Sha(pair.Key) != pair.Value))
                    throw new InvalidOperationException("Sources changed during " + auditKind);
                if (checkedArtifacts != JsonSerializer.Serialize(ImportArtifactParts()))
                    throw new InvalidOperationException("Compiled artifacts changed during " + auditKind);
            }
            // Publish only after the complete declaration replay, exact theorem
            // audit, extraction recheck and source-stability checks succeeded.
            void PublishSupport()
            {
                if (failures.Count != 0 || graph is null) return;
                RequireDeepStable();
                var dependent = DependentModules(graph,
                    ["Extracted", "ExtractedSymbols", "ExtractionAudit", .. names, .. components.Sources.Keys]);
                // Extraction-dependent modules are recorded too, bound to this Extracted; export uses only the others.
                // Records bind no PDB names, so importers of ExtractedSymbols stay unbound and are never cached.
                var excluded = DependentModules(graph, names);
                if (deep is not null) excluded.UnionWith(deep.Modules.Where(module => module != "Extracted"));
                excluded.Add("ExtractedSymbols");
                excluded.UnionWith(members.SelectMany(member => selections[member]).Where(SelectionModules.IsSymbols));
                var collected = UseSuccessCache || share || exporting
                    ? CollectConsumerSupport(session, currentArtifacts, graph, excluded, extractionDependent, bound) : null;
                try
                {
                    if (exporting)
                    {
                        RequireDeepStable();
                        void RequireNormalizedSupportStable()
                        {
                            Stage(proceeding, "support normalization");
                            Recheck(proceeding);
                            foreach (var member in proceeding)
                                if (!Live(member))
                                    throw outcomes[member].Error ?? new InvalidOperationException(
                                        "Consumer request ended during support normalization.");
                            RequireDeepStable();
                        }
                        AddExportedSupport(export, session, root, before[proceeding[0]],
                            currentArtifacts.Where(pair => !dependent.Contains(pair.Key) &&
                                (deep is null || !excluded.Contains(pair.Key))).ToDictionary(), graph, collected,
                            publishReceipts: deep is null,
                            requireStable: deep is null ? null : RequireNormalizedSupportStable);
                    }
                    if (collected is not null)
                    {
                        if (UseSuccessCache && Same(generatedInputs, GeneratedInputs()))
                        {
                            RequireDeepStable();
                            PublishConsumerCertificateSupport(certificateSupportKey, collected,
                                certificateModules.ToHashSet(StringComparer.Ordinal));
                        }
                        if (supportKey.Length > 0)
                        {
                            RequireDeepStable();
                            PublishSuccess(supportKey + "-" + Sha(Path.Combine(collected, ConsumerSupportRecordName)), collected, supportKey);
                            if (UseSuccessCache) EvictStaleSupport();
                        }
                        if (share)
                        {
                            Directory.Delete(support, true);
                            Directory.Move(collected, support);
                            // Later workspaces restore their own extraction-dependent modules.
                            var record = ReadConsumerSupportRecord(Path.Combine(support, ConsumerSupportRecordName));
                            foreach (var file in record?.Values.Where(module => module.Sources.ContainsKey(ExtractedSourceKey))
                                .SelectMany(module => module.Files) ?? [])
                                File.Delete(Within(support, file));
                            supportArtifacts = CacheFiles(support);
                        }
                    }
                }
                finally { if (collected is not null && Directory.Exists(collected)) Directory.Delete(collected, true); }
            }
            if (deep is null) PublishSupport();
            // Read from the audited proof module after every check above; the receipt caches it with the result.
            void ShowConsumerProof(int i, string receipt)
            {
                File.WriteAllText(Path.Combine(receipt, ProofMessagesFile),
                    JsonSerializer.Serialize(outcomes[i].Messages));
                if (viewsStatement)
                    outcomes[i].Statement = ViewStatement(receipt, ProofModule(i) + ".olean", leanPath,
                        File.ReadAllText(Path.Combine(session, requestModules[i] + ".lean")), requests[i].Theorem);
            }
            foreach (var i in proceeding)
            {
                var extraction = extractions[i].Root;
                var initializedTypes = extraction.TryGetProperty("initializedTypes", out var assumptions)
                    ? assumptions.Deserialize<string[]>() : [];
                RequireImplementationImports(extractions[i]);
                fullResults.TryGetValue(i, out FullImportResult? fullResult);
                var report = new Report(CertificateSchema, Sha(requests[i].Assembly), identities[i].ToString(),
                    requests[i].Theorem, audits[i].Axioms, audits[i].Audit, before[i],
                    deepChecks is null ? BindingSection.Default : DeepBindingSection(deepChecks, matchedPins!,
                        deep!.Requests, new(bindingSourcesKey!,
                            File.ReadAllText(Path.Combine(bindingPreparation!.Session, "lean-toolchain")).Trim(),
                            Sha(LeanExecutable)), audits[i].Result, deep.Uncovered),
                    libraryKey, "consumer-" + libraryBuild, extractionAudit, initializedTypes,
                    consumerSupportSha256: baseUnchanged && portableSupport.Count > 0
                        ? Environment.GetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256") : null,
                    staticValues: StaticValueAssumptions(extraction),
                    opaqueStaticValues: OpaqueStaticValues(extraction),
                    contractImports: ContractImportAssumptions(extraction),
                    imports: fullResult?.Imports ?? PublishedImports(extraction),
                    contractDependencies: fullResult?.Dependencies ?? DeploymentDependencies(extraction),
                    compositionTheorem: fullResult?.Theorem, compositionAudit: fullResult?.Audit,
                    initializationAssumptions: InitializationAssumptions(extraction),
                    statementIdentity: requests[i].Statement is null ? null : Identity(audits[i].Proof),
                    refutation: audits[i].Refutation);
                var receipt = Path.Combine(session, "certified-result-" + i);
                Directory.CreateDirectory(receipt);
                File.WriteAllText(Path.Combine(receipt, "report.json"), JsonSerializer.Serialize(report, Json));
                ShowConsumerProof(i, receipt);
                if (deep is not null)
                {
                    Recheck([i]);
                    if (!Live(i)) continue;
                    RequireDeepStable();
                    var deepStaging = Path.Combine(Path.GetTempPath(), "leancil-deep-" + Guid.NewGuid().ToString("N"));
                    try
                    {
                        // Only a result replayed against the certified CIL modules may be restored without replay.
                        var deepPublication = baseUnchanged ? StageDeepResult(deep, deepStaging) : null;
                        Stage([i], "deep result publication");
                        PublishSupport();
                        RequireDeepStable();
                        if (deepPublication is not null) PublishSuccess(deep.ResultKey!, deepPublication);
                    }
                    finally { if (Directory.Exists(deepStaging)) Directory.Delete(deepStaging, true); }
                }
                if (deep is null) PublishSuccess(proofKeys[i], receipt);
                if (last[locations[i]] == i)
                    File.WriteAllText(Path.Combine(outputs[i], "verified.json"),
                        JsonSerializer.Serialize(report, Json) + "\n");
                outcomes[i].Report = report;
                CompleteTiming(i);
            }
        }

        // Compiled support stays inside this invocation; it is never published as certified support.
        void CheckGroup(int[] members, string session, string[] names,
            IReadOnlyDictionary<string, string> bound, bool first, bool share, ConsumerSession prepared)
        {
            if (!first)
                foreach (var file in CacheFiles(support).Keys.Where(file => file != ConsumerSupportRecordName))
                {
                    var destination = Within(session, file);
                    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                    File.Copy(Within(support, file), destination, true);
                }
            Stage(members, "compile check");
            string[] command = ["lake", "build", .. names.Select(name => "+" + name + ":olean")];
            var build = Execute(command, session, progress: "Compile checking consumer proofs and dependencies",
                internalErrors: false);
            FailInternalErrors(members, names, command, build.Code, build.Output);
            var (directories, _) = ConsumerImportDirectories(session);
            if (prepared.Copied.Any(pair => !File.Exists(pair.Key) || Sha(pair.Key) != pair.Value))
                throw new InvalidDataException("Consumer sources changed during the compile check.");
            for (var index = 0; index < members.Length; index++)
            {
                var member = members[index];
                var source = Path.Combine(session, names[index] + ".lean");
                var artifact = directories.Select(directory => Path.Combine(directory, names[index]))
                    .FirstOrDefault(path => File.Exists(path + ".olean") && File.Exists(path + ".trace"));
                if (!Live(member)) continue;
                if (artifact is not null)
                {
                    outcomes[member].Messages = LakeTraceMessages(artifact + ".trace", session, source);
                    outcomes[member].Checked = true;
                    CompleteTiming(member);
                }
                else
                {
                    outcomes[member].Messages = LakeOutputMessages(build.Output, session, source);
                    var error = new InvalidOperationException("Compile check failed:\n" + build.Output);
                    error.Data[LeanDiagnostics.HiddenModulesKey] = names.Where((_, other) => other != index).ToArray();
                    Fail([member], error);
                }
            }
            if (!share) return;
            var modules = directories.Where(directory => ResolvedRelativePath(session, directory) is not (null or "."))
                .Where(Directory.Exists).SelectMany(directory => Directory.EnumerateFiles(
                    directory, "*.olean", SearchOption.AllDirectories).Select(path =>
                        (Name: ModuleName(Path.GetRelativePath(directory, path)), Path: path)))
                .ToDictionary(pair => pair.Name, pair => pair.Path, StringComparer.Ordinal);
            var graph = ConsumerModuleImports(session, modules);
            var dependent = DependentModules(graph, ["Extracted", "ExtractedSymbols",
                .. extractions[members[0]].Sources.Keys, .. names]);
            var collected = CollectConsumerSupport(session, modules, graph, dependent, dependent, bound);
            if (collected is null) return;
            Directory.Delete(support, true);
            Directory.Move(collected, support);
        }

        void RunGroup(int[] members, bool first, bool share)
        {
            bool priorReferenceOnly = referenceOnlyAuthoring;
            referenceOnlyAuthoring = ReferenceOnlyImports(extractions[members[0]]);
            var session = Path.Combine(Path.GetTempPath(), "leancil-consumer-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(session);
            try { VerifyGroup(members, session, first, share); }
            catch (Exception error) { Fail(members, error); }
            finally
            {
                referenceOnlyAuthoring = priorReferenceOnly;
                Directory.Delete(session, true);
            }
            foreach (var i in members.Where(i => !Live(i))) finished?.Invoke(i, outcomes[i]);
        }

        try
        {
            // The first workspace certifies shared support before later ones start.
            RunGroup(ordered[0], first: true, share: ordered.Length > 1);
            Parallel.ForEach(ordered.Skip(1), parallel, group => RunGroup(group, first: false, share: false));
            // One manifest per session: the union of every workspace that passed all checks.
            if (exporting) WriteExportedSupport(export);
        }
        finally
        {
            Directory.Delete(support, true);
            if (Directory.Exists(export.Staging)) Directory.Delete(export.Staging, true);
        }
        return outcomes;
    }
}
