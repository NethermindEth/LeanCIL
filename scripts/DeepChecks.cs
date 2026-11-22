using System.Globalization;
using System.Numerics;
using System.Text.Json;

// Deep verification checks that the method bodies and carried metadata rows of an extraction are
// those of assembly files whose SHA-256 digests the caller states.
partial class Program
{
    /// <summary>One call's retained inputs and attempt, available to its caller after a failure.</summary>
    sealed class DeepCheckRun(DeepCheckInputs inputs)
    {
        bool claimed;
        internal DeepCheckInputs Inputs { get; } = inputs;
        internal DeepCheckAttempt? Attempt { get; private set; }

        internal static DeepCheckRun? Claim(DeepCheckInputs? inputs, DeepCheckRun? run)
        {
            if (inputs is null)
            {
                if (run is not null) throw new ArgumentException("Deep-check holder requires inputs.");
                return null;
            }
            run ??= new(inputs);
            if (!ReferenceEquals(inputs, run.Inputs))
                throw new ArgumentException("Deep-check holder inputs do not match.");
            if (run.claimed) throw new ArgumentException("Deep-check holder was already used.");
            run.claimed = true;
            return run;
        }

        internal IReadOnlyList<DeepCheckInputs.Pin> Begin(ExtractionIdentity identity)
        {
            if (!claimed || Attempt is not null)
                throw new InvalidOperationException("Deep-check attempt requires one claimed request.");
            var pins = Inputs.MatchPins(identity.Root);
            Attempt = new(Inputs, identity.Sha256, pins);
            return pins;
        }
    }

    /// <summary>Rejected targets of an incomplete verification; successful facts are never retained.</summary>
    sealed class DeepCheckAttempt
    {
        readonly FailureReports.BindingFailureDigest digests;
        readonly (string Identity, Sha256Digest Digest)[] images;
        readonly HashSet<Sha256Digest> imageDigests;
        readonly DeepCheckInputs.Pin[] checkedPins;
        readonly Dictionary<Sha256Digest, string> rejectedImages = [];
        readonly Dictionary<BindingFact, string> rejectedFacts = [];
        internal string IdentitySha256 { get; }

        internal DeepCheckAttempt(DeepCheckInputs inputs, string identitySha256,
            IReadOnlyList<DeepCheckInputs.Pin> pins)
        {
            digests = new(inputs.Path, inputs.Digest.ToString());
            IdentitySha256 = identitySha256;
            checkedPins = [.. pins];
            images = [.. pins.Select(pin => (pin.Identity, pin.Image.Digest))];
            imageDigests = [.. images.Select(image => image.Digest)];
        }

        internal void RequireIdentity(ExtractionIdentity identity)
        {
            if (IdentitySha256 != identity.Sha256 ||
                IdentitySha256 != Sha(Path.Combine(identity.Output, "identity.json")))
                throw new InvalidDataException("Deep-check extraction identity changed.");
        }

        internal void RejectImage(Sha256Digest digest, string reason)
        {
            if (!imageDigests.Contains(digest)) throw new ArgumentException("Unknown deep-check image.");
            ArgumentException.ThrowIfNullOrWhiteSpace(reason);
            rejectedImages.TryAdd(digest, reason);
        }

        internal void RejectFact(BindingFact fact, string reason)
        {
            if (!Enum.IsDefined(fact)) throw new ArgumentException("Unknown binding fact.");
            ArgumentException.ThrowIfNullOrWhiteSpace(reason);
            try
            {
                var detail = fact switch
                {
                    BindingFact.ObjectFields => DeepCheckInputs.ObjectFieldDiagnostic(
                        checkedPins.Where(pin => pin.ObjectCoverage.HasValue)),
                    BindingFact.ValueTupleFieldOrder => DeepCheckInputs.TupleFieldDiagnostic(
                        checkedPins.Where(pin => pin.TupleCoverage.HasValue)),
                    BindingFact.PublicKeyTokens => DeepCheckInputs.ReferenceKeyDiagnostic(checkedPins),
                    _ => null
                };
                if (detail is not null) reason += ". " + detail;
            }
            catch (BadImageFormatException) { } // Preserve the kernel diagnostic for malformed metadata.
            rejectedFacts.TryAdd(fact, reason);
        }

        internal FailureReports.BindingFailure Failure(string stage, string diagnostic)
        {
            ArgumentException.ThrowIfNullOrWhiteSpace(stage);
            var incomplete = "verification did not complete: " + stage +
                (string.IsNullOrWhiteSpace(diagnostic) ? "" : ": " + diagnostic);
            return new(digests,
                [.. images.Select(image => new FailureReports.BindingFailureImage(image.Identity,
                    image.Digest.ToString(),
                    rejectedImages.ContainsKey(image.Digest) ? FailureReports.BindingFailureStatus.Failed
                        : FailureReports.BindingFailureStatus.NotCovered,
                    rejectedImages.GetValueOrDefault(image.Digest) ?? incomplete))],
                [.. Enum.GetValues<BindingFact>().Select(fact => new FailureReports.BindingFailureFact(
                    JsonSerializer.SerializeToElement(fact).GetString()!,
                    rejectedFacts.ContainsKey(fact) ? FailureReports.BindingFailureStatus.Failed
                        : FailureReports.BindingFailureStatus.NotCovered,
                    rejectedFacts.GetValueOrDefault(fact) ?? incomplete))]);
        }
    }

    /// <summary>A generated request's optional subject; a request cannot name both kinds.</summary>
    abstract record BindingSubject
    {
        internal sealed record Fact(BindingFact Value, bool Complete = true) : BindingSubject;
        internal sealed record Image(Sha256Digest Digest) : BindingSubject;
    }

    /// <summary>An assembly file the extraction read, with the digest the caller must confirm.</summary>
    sealed record BindingImagePin(string Identity, Sha256Digest Digest, byte[] Bytes)
    {
        /// <summary>The generated module that holds the file's bytes, named by its full digest.</summary>
        internal string Module => "BindingAudit.I" + Digest;

        internal string Theorem => Module + ".digest";
    }

    /// <summary>What a run audits: the extraction, the files it pinned and where the generated modules go.</summary>
    sealed record BindingPlan(string Output, BindingImagePin[] Images, int Methods,
        bool? ObjectFields = null, bool? TupleFields = null, bool? PublicKeys = null);

    /// <summary>
    /// Artifacts and requests that must join the caller's extraction and proof audit. A contribution with a result
    /// key may be published once the run succeeds; a restored one holds artifacts an earlier run replayed.
    /// </summary>
    sealed record DeepSessionContribution(string[] Modules, BindingTargets Targets,
        SortedDictionary<string, string> Artifacts, SortedDictionary<string, string> Hashes,
        SortedDictionary<string, string> SourceHashes, string SourceDirectory, string? ResultKey = null,
        bool Restored = false)
    {
        internal BindingRequest[] Requests => Targets.Requests;

        internal string[] OwnedFailures(IEnumerable<string> failures) => failures.Where(module =>
            Targets.Modules.TryGetValue(module, out var subject) && subject is not null).ToArray();

        /// <summary>Only trusted generated module ownership selects a rejected binding subject.</summary>
        internal void RejectReplay(IReadOnlyDictionary<string, ReplayRejection> rejections,
            DeepCheckAttempt? attempt)
        {
            if (attempt is null) return;
            foreach (var (module, rejection) in rejections)
            {
                if (!Targets.Modules.TryGetValue(module, out var subject)) continue;
                var reason = $"Kernel rejected {rejection.Declaration}: {rejection.Kind}";
                switch (subject)
                {
                    case BindingSubject.Fact fact: attempt.RejectFact(fact.Value, reason); break;
                    case BindingSubject.Image image: attempt.RejectImage(image.Digest, reason); break;
                }
            }
        }

        /// <summary>Attributes only complete named audit rejections after physical guards have passed.</summary>
        internal void RequireTheorems(AuditedOleans audited, IReadOnlyList<AuditRequest> expected,
            DeepCheckAttempt? attempt)
        {
            var named = audited.theorems.ToDictionary(result => result.name, StringComparer.Ordinal);
            var expectedNames = expected.Select(request => request.name).ToHashSet(StringComparer.Ordinal);
            if (expectedNames.Count != expected.Count || !expectedNames.SetEquals(named.Keys) ||
                Targets.Theorems.Keys.Any(name => !expectedNames.Contains(name)) ||
                audited.theorems.Any(result => result.error is null && result.axioms is null))
                throw new InvalidDataException("Incomplete deep-check theorem audit result.");
            RequireAudited(audited);
            foreach (var request in Requests)
            {
                var result = named[request.Audit.name];
                string? rejection = result.error;
                if (rejection is null && result.axioms is { } axioms &&
                    axioms.Any(axiom => !ApprovedAxioms.Contains(axiom)))
                    rejection = "Unapproved proof axioms: " + string.Join(", ", axioms);
                if (rejection is not null && attempt is not null)
                    switch (Targets.Theorems[request.Audit.name])
                    {
                        case BindingSubject.Fact fact: attempt.RejectFact(fact.Value, rejection); break;
                        case BindingSubject.Image image: attempt.RejectImage(image.Digest, rejection); break;
                    }
            }
            foreach (var request in Requests) AuditedAxioms(named[request.Audit.name]);
        }

        internal void RequireStable()
        {
            if (!Same(Hashes, BindingArtifactHashes(Artifacts.Values)))
                throw new InvalidDataException("Deep-check artifact changed");
            if (!Directory.Exists(SourceDirectory) || !Same(SourceHashes, BindingSourceHashes(SourceDirectory)))
                throw new InvalidDataException("Deep-check source changed: " + SourceDirectory);
        }

        internal void RequireAudited(AuditedOleans audited)
        {
            RequireStable();
            foreach (var (module, path) in Artifacts) RequireAuditedModule(audited, module, path);
        }
    }

    /// <summary>The exact generated source inventory in the contribution's owned directory.</summary>
    static SortedDictionary<string, string> BindingSourceHashes(string directory) =>
        HashFiles(Directory.EnumerateFiles(directory, "*.lean", SearchOption.AllDirectories)
            .Select(path => (path, path)));

    /// <summary>Hashes the exact compiled module families, enumerating each containing directory once.</summary>
    static SortedDictionary<string, string> BindingArtifactHashes(IEnumerable<string> artifacts) =>
        HashFiles(ModuleFamilyParts(artifacts).Select(path => (path, path)));

    /// <summary>
    /// Every part of each compiled module family: the module's `.olean` and each file beside it named by that
    /// file and a further extension. A family whose module file is missing is refused.
    /// </summary>
    static List<string> ModuleFamilyParts(IEnumerable<string> artifacts)
    {
        var families = artifacts.Select(Path.GetFullPath)
            .GroupBy(artifact => Path.GetDirectoryName(artifact)!, LocationComparer);
        List<string> files = [];
        foreach (var family in families)
        {
            var expected = family.ToHashSet(LocationComparer);
            foreach (var artifact in expected)
                if (!File.Exists(artifact))
                    throw new InvalidDataException("Deep-check artifact changed: missing " + artifact);
            foreach (var path in Directory.EnumerateFiles(family.Key))
            {
                var filename = Path.GetFileName(path);
                // Any case finds a candidate; the directory's case rule then decides whether it is an expected file.
                var marker = filename.IndexOf(".olean", StringComparison.OrdinalIgnoreCase);
                if (marker < 0) continue;
                var end = marker + ".olean".Length;
                if ((end == filename.Length || filename[end] == '.') &&
                    expected.Contains(Path.Combine(family.Key, filename[..end])))
                    files.Add(path);
            }
        }
        return files;
    }

    /// <summary>
    /// Builds deep modules against the caller's existing extraction in its verification session. Given the key of
    /// the certified environment and extraction, restores modules an earlier successful run built and replayed for
    /// the same generated sources instead.
    /// </summary>
    DeepSessionContribution BuildDeepSession(string session, string leanPath, string extractedOlean,
        ExtractionIdentity identity, IReadOnlyList<DeepCheckInputs.Pin> matchedPins, Action? sourcesReady = null,
        string? environment = null)
    {
        session = Path.GetFullPath(session);
        extractedOlean = Path.GetFullPath(extractedOlean);
        if (!File.Exists(extractedOlean)) throw new FileNotFoundException("Missing extraction module", extractedOlean);
        var extractedHashes = BindingArtifactHashes([extractedOlean]);
        Dictionary<Sha256Digest, byte[]> bytes = [];
        var pins = matchedPins.Select(pin =>
        {
            if (!bytes.TryGetValue(pin.Image.Digest, out var snapshot))
                bytes.Add(pin.Image.Digest, snapshot = pin.Image.Bytes.ToArray());
            return new BindingImagePin(pin.Identity, pin.Image.Digest, snapshot);
        }).ToArray();
        BindingPlan plan = new(session, pins,
            identity.Root.GetProperty("methods").GetArrayLength(), matchedPins.FirstOrDefault(pin =>
                pin.ObjectCoverage.HasValue)?.ObjectCoverage, matchedPins.FirstOrDefault(pin =>
                pin.TupleCoverage.HasValue)?.TupleCoverage, matchedPins.FirstOrDefault(pin =>
                pin.KeyCoverage.HasValue)?.KeyCoverage);
        var directory = Path.Combine(session, "BindingAudit");
        if (Directory.Exists(directory))
            throw new InvalidOperationException("Deep-check modules already exist in the session: " + directory);
        Directory.CreateDirectory(directory);
        var targets = new BindingTargets(BindingRequests(plan));
        WriteBindingSources(plan);
        sourcesReady?.Invoke();
        var sources = BindingSourceHashes(directory);
        // Replay is the only kernel check of the generated modules, so a restored result must bind every import.
        var imports = environment is null ? null : DeepImportClosure(session, leanPath, directory);
        deepImports = imports;
        var resultKey = environment is null || imports is null ? null : DeepResultKey(environment,
            bindingSourcesKey ?? throw new InvalidOperationException("StrictBinding has not been prepared"),
            bindingPreparation?.Toolchain ??
                throw new InvalidOperationException("StrictBinding has not been prepared"),
            imports, Relative(directory, sources), pins, targets.Requests);
        var restored = resultKey is not null && RestoreSuccess(resultKey, session);
        Dictionary<string, string> failures = restored ? new(StringComparer.Ordinal)
            : BuildBindingModules(plan, leanPath);
        if (failures.Count != 0)
            throw new InvalidOperationException("Deep-check module build failed: " +
                string.Join("; ", failures.Select(pair => pair.Key + ": " + pair.Value)));
        string[] modules = [.. targets.Requests.Select(request => request.Module).Distinct(StringComparer.Ordinal)];
        SortedDictionary<string, string> artifacts = new(StringComparer.Ordinal) { ["Extracted"] = extractedOlean };
        foreach (var module in modules.Where(module => module != "Extracted"))
        {
            var source = ModuleSource(session, module);
            var artifact = Path.ChangeExtension(source, ".olean");
            artifacts.Add(module, artifact);
        }
        if (!Same(extractedHashes, BindingArtifactHashes([extractedOlean])))
            throw new InvalidDataException("Deep-check artifact changed: " + extractedOlean);
        DeepSessionContribution contribution = new(modules, targets, artifacts,
            BindingArtifactHashes(artifacts.Values), sources, directory, resultKey, restored);
        contribution.RequireStable();
        return contribution;

        static SortedDictionary<string, string> Relative(string root, SortedDictionary<string, string> hashes) =>
            new(hashes.ToDictionary(pair => Path.GetRelativePath(root, pair.Key).Replace('\\', '/'),
                pair => pair.Value), StringComparer.Ordinal);
    }

    /// <summary>
    /// The key of a deep result: the certified environment and extraction it was checked in, the prepared
    /// StrictBinding sources and toolchain, the compiled modules the generated modules import transitively, and
    /// the generated sources, pins and requests. The generated sources hold the image bytes, identities and page size.
    /// </summary>
    static string DeepResultKey(string environment, string bindingSources, string toolchain,
        SortedDictionary<string, string> imports, SortedDictionary<string, string> sources,
        IReadOnlyList<BindingImagePin> pins, IReadOnlyList<BindingRequest> requests) =>
        ContentKey(JsonSerializer.Serialize(new
        {
            format = "deep-result-v1",
            environment,
            bindingSources,
            toolchain,
            imports,
            sources,
            pins = pins.Select(pin => new { identity = pin.Identity, digest = pin.Digest.ToString() }),
            requests = requests.Select(request => new
            {
                module = request.Module,
                audit = request.Audit,
                fact = (request.Subject as BindingSubject.Fact)?.Value,
                image = (request.Subject as BindingSubject.Image)?.Digest.ToString()
            })
        }));

    /// <summary>
    /// The environment a consumer's deep modules build in, beyond the compiled imports their key binds: the
    /// verifier and the certified library.
    /// </summary>
    string ConsumerDeepEnvironment() => ContentKey(JsonSerializer.Serialize(new
    {
        format = "consumer-deep-environment-v2",
        policy = VerificationPolicy,
        library = libraryKey ?? throw new InvalidOperationException("The certified library is not selected")
    }));

    /// <summary>The compiled import closure the key of the last keyed deep session bound.</summary>
    SortedDictionary<string, string>? deepImports;

    /// <summary>
    /// The work the last deep import closure did: header-reader launches, compiled headers read, module parts
    /// hashed and the bytes those parts hold.
    /// </summary>
    internal readonly record struct DeepClosureWork(int Launches, int Headers, int Hashed, long HashedBytes);

    DeepClosureWork deepClosureWork;

    // The library guard holds certified files to the bytes read here, so each is read once per process.
    readonly Dictionary<string, string[]> certifiedHeaders = new(LocationComparer);
    readonly Dictionary<string, string> certifiedPartHashes = new(LocationComparer);
    readonly Dictionary<string, string[]> generatedImports = new(StringComparer.Ordinal);

    /// <summary>
    /// The content hash of every compiled module part the modules generated below `directory` import,
    /// transitively, by its name below its search root. Each import resolves as Lean resolves it: to the first
    /// root of `leanPath` that holds it, then to the toolchain, whose modules the toolchain key binds.
    /// </summary>
    SortedDictionary<string, string> DeepImportClosure(string session, string leanPath, string directory)
    {
        var toolchain = Path.GetFullPath(Path.Combine(Toolchain, "lib", "lean"));
        var certified = library is null ? null : Path.GetFullPath(Path.Combine(library, ".lake/build/lib/lean"));
        if (certified is not null) RequireUnchangedLibrary();
        bool Certified(string root) => certified is not null && LocationComparer.Equals(root, certified);
        Dictionary<string, (string Root, string Path)> compiled = new(StringComparer.Ordinal);
        foreach (var root in leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(Path.GetFullPath)
            .Where(root => !LocationComparer.Equals(root, toolchain) && Directory.Exists(root)))
            foreach (var path in Directory.EnumerateFiles(root, "*.olean", SearchOption.AllDirectories))
                compiled.TryAdd(ModuleName(Path.GetRelativePath(root, path).Replace('\\', '/')), (root, path));
        int launches = 0;
        var generated = Directory.EnumerateFiles(directory, "*.lean", SearchOption.AllDirectories)
            .ToDictionary(path => Path.ChangeExtension(Path.GetRelativePath(session, path), null)
                .Replace(Path.DirectorySeparatorChar, '.'), File.ReadAllText, StringComparer.Ordinal);
        var unparsed = generated.Where(pair => !generatedImports.ContainsKey(ContentKey(pair.Value))).ToArray();
        if (unparsed.Length != 0)
        {
            launches++;
            var parsed = ContractModuleImports(session, new(unparsed.ToDictionary(), StringComparer.Ordinal));
            foreach (var (module, source) in unparsed) generatedImports[ContentKey(source)] = parsed[module];
        }
        // One launch reads every header this process has not read from the certified library.
        var unread = compiled
            .Where(pair => !Certified(pair.Value.Root) || !certifiedHeaders.ContainsKey(pair.Value.Path))
            .ToDictionary(pair => pair.Key, pair => pair.Value.Path);
        var read = unread.Count == 0 ? [] : ConsumerModuleImports(session, unread);
        if (unread.Count != 0) launches++;
        foreach (var (module, imports) in read)
            if (Certified(compiled[module].Root)) certifiedHeaders[compiled[module].Path] = imports;
        var pending = new Queue<string>(generated.Values.SelectMany(source => generatedImports[ContentKey(source)])
            .Where(module => !generated.ContainsKey(module)));
        HashSet<string> closure = new(StringComparer.Ordinal);
        while (pending.TryDequeue(out var module))
        {
            if (!closure.Add(module)) continue;
            if (compiled.TryGetValue(module, out var found))
                foreach (var imported in read.TryGetValue(module, out var imports) ? imports
                    : certifiedHeaders[found.Path]) pending.Enqueue(imported);
            else if (!File.Exists(Path.Combine(toolchain,
                module.Replace('.', Path.DirectorySeparatorChar) + ".olean")))
                throw new InvalidDataException("Deep-check import is not compiled: " + module);
        }
        Dictionary<string, string> names = new(LocationComparer);
        List<string> unhashed = [];
        List<string> certifiedUnhashed = [];
        foreach (var (root, olean) in closure.Where(compiled.ContainsKey).Select(module => compiled[module]))
            // Companion parts lie beside their module, so each part is named below its module's root.
            foreach (var part in ModuleFamilyParts([olean]))
            {
                names[part] = Path.GetRelativePath(root, part).Replace('\\', '/');
                if (!Certified(root)) unhashed.Add(part);
                else if (!certifiedPartHashes.ContainsKey(part)) certifiedUnhashed.Add(part);
            }
        var hashed = HashFiles(unhashed.Concat(certifiedUnhashed).Select(part => (part, part)));
        foreach (var part in certifiedUnhashed) certifiedPartHashes[part] = hashed[part];
        deepClosureWork = new(launches, unread.Count, hashed.Count,
            hashed.Keys.Sum(part => new FileInfo(part).Length));
        return new(names.ToDictionary(pair => pair.Value,
            pair => hashed.TryGetValue(pair.Key, out var hash) ? hash : certifiedPartHashes[pair.Key]),
            StringComparer.Ordinal);
    }

    /// <summary>
    /// Copies the generated modules a keyed deep contribution built into a new directory below
    /// `staging`, checking each copy against the audited hashes, for publication once the run succeeds.
    /// Restored and unkeyed contributions stage nothing.
    /// </summary>
    static string? StageDeepResult(DeepSessionContribution deep, string staging)
    {
        if (deep.ResultKey is null || deep.Restored) return null;
        deep.RequireStable();
        var root = Path.GetDirectoryName(deep.SourceDirectory)!;
        var publication = Path.Combine(staging, "deep-cache");
        Directory.CreateDirectory(publication);
        foreach (var (path, hash) in deep.Hashes)
        {
            var generated = Path.GetRelativePath(deep.SourceDirectory, path);
            if (generated.StartsWith("..", StringComparison.Ordinal) || Path.IsPathRooted(generated)) continue;
            var target = Path.Combine(publication, Path.GetRelativePath(root, path));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(path, target);
            if (Sha(target) != hash) throw new InvalidDataException("Deep-check artifact changed: " + path);
        }
        return publication;
    }

    /// <summary>Read the completeness constructor in the jointly audited theorem's type.</summary>
    static bool CoverageComplete(AuditedTheorem theorem)
    {
        // The structural audit binds the proposition and every extraction and image constant.
        // Read only its final argument from the replayed statement.
        if (theorem.term is not { } term || theorem.termError is not null)
            throw new InvalidDataException($"Cannot read the coverage argument of {theorem.name}: " +
                (theorem.termError ?? "audit returned no statement term"));
        var nodes = term.GetProperty("nodes");
        var application = nodes[term.GetProperty("root").GetInt32()];
        if (application[0].GetString() == "app")
        {
            var argument = nodes[application[2].GetInt32()];
            if (argument.GetArrayLength() == 4 && argument[0].GetString() == "const" &&
                argument[2].GetArrayLength() == 2 && argument[2][0].GetString() == "Bool")
                return argument[2][1].GetString() switch
                {
                    "true" => true,
                    "false" => false,
                    _ => throw new InvalidDataException("Invalid coverage constructor")
                };
        }
        throw new InvalidDataException("Expected a literal coverage argument");
    }

    /// <summary>Report each fact and image from the requests that passed the joint audit.</summary>
    static BindingSection DeepBindingSection(DeepCheckInputs inputs, IReadOnlyList<DeepCheckInputs.Pin> pins,
        IReadOnlyList<BindingRequest> audited, StatementSources sources, AuditedOleans oleanAudit)
    {
        Dictionary<BindingFact, string> factTheorems = [];
        Dictionary<Sha256Digest, string> imageTheorems = [];
        foreach (var request in audited)
        {
            if (request.Audit.name is EnumStorageTheorem or PlatformKindsTheorem or GenericConstraintsTheorem &&
                !CoverageComplete(oleanAudit.theorems.Single(result => result.name == request.Audit.name)))
                continue;
            var distinct = request.Subject switch
            {
                BindingSubject.Fact { Complete: true } fact => factTheorems.TryAdd(fact.Value, request.Audit.name),
                BindingSubject.Image image => imageTheorems.TryAdd(image.Digest, request.Audit.name),
                _ => true
            };
            if (!distinct) throw new InvalidOperationException("Two deep-check requests name one subject: " +
                request.Audit.name);
        }
        var pinnedDigests = pins.Select(pin => pin.Image.Digest).ToHashSet();
        ImageResult[] images =
        [
            .. pins.Select(pin =>
            {
                var role = pin.Platform ? ImageRole.Platform : pin.Reference ? ImageRole.Reference : ImageRole.Pinned;
                return imageTheorems.TryGetValue(pin.Image.Digest, out var theorem)
                    ? new ImageResult(pin.Identity, pin.Image.Digest.ToString(), role,
                        BindingStatus.Reconfirmed, theorem, null)
                    : new ImageResult(pin.Identity, pin.Image.Digest.ToString(), role,
                        BindingStatus.NotCovered, null, "no checked theorem states the digest of this image");
            }),
            .. inputs.Images.Where(image => !pinnedDigests.Contains(image.Digest)).Select(image =>
                new ImageResult(image.Path, image.Digest.ToString(), ImageRole.Unused, BindingStatus.NotCovered, null,
                    "no extraction pin or checked binding claim names this image"))
        ];
        BindingFactResult[] facts = [.. Enum.GetValues<BindingFact>().Select(fact =>
            factTheorems.TryGetValue(fact, out var theorem)
                ? new BindingFactResult(fact, BindingStatus.Reconfirmed, theorem, null)
                : new BindingFactResult(fact, BindingStatus.NotCovered, null, NotCoveredReason(fact)))];
        return new(BindingMode.Deep, new(inputs.Path, inputs.Digest.ToString()), sources, images, facts);
    }

    /// <summary>Why a deep run that audited no theorem about a fact does not cover it.</summary>
    static string NotCoveredReason(BindingFact fact) => fact switch
    {
        BindingFact.BodyBytes => "no checked theorem binds the method bodies to the pinned images",
        BindingFact.MetadataRows =>
            "no checked theorem binds the carried metadata rows and heap entries to the pinned images",
        BindingFact.PlatformTypeKinds => "the extraction selects no platform type or a defining or forwarding image is missing",
        BindingFact.EnumUnderlyingTypes => "the extraction selects no enum or a defining or forwarding image is missing",
        BindingFact.ValueTupleFieldOrder => "the supplied images do not cover a selected System.ValueTuple pair",
        BindingFact.ObjectFields => "the supplied images do not cover the extraction's platform definition of System.Object",
        BindingFact.LayoutContent => "no check reads field offsets, sizes or attributes from the image",
        BindingFact.DispatchCatalogs => "no check reads the types of an image",
        BindingFact.StaticData => "no checked theorem binds the static field data to the pinned images",
        BindingFact.GenericConstraints =>
            "no generic parameter was selected, or a declaration, layout or import lacks physical coverage",
        BindingFact.PublicKeyTokens => "the supplied images do not cover the extraction pins' AssemblyRef targets",
        BindingFact.ImportIdentities => "no check recomputes an import identity from its image",
        _ => throw new InvalidOperationException("Missing binding fact reason: " + fact)
    };

    const string ImagesModule = "BindingAudit.Images";
    const string GenericConstraintsModule = "BindingAudit.GenericConstraints";
    const string GenericConstraintsTheorem = "BindingAudit.genericConstraints";
    const string PlatformKindsModule = "BindingAudit.PlatformKinds";
    const string PlatformKindsTheorem = "BindingAudit.platformKinds";
    const string EnumStorageModule = "BindingAudit.EnumStorage";
    const string EnumStorageTheorem = "BindingAudit.enumStorage";
    const string PublicKeysModule = "BindingAudit.PublicKeys";
    const string TupleFieldsModule = "BindingAudit.TupleFields";
    const string ObjectFieldsModule = "BindingAudit.ObjectFields";
    const string StaticDataModule = "BindingAudit.StaticData";
    const string BodiesModule = "BindingAudit.Bodies";
    const string MetadataRowsModule = "BindingAudit.MetadataRows";

    /// <summary>The facts proved page by page over the method evidence, in the order their modules build.</summary>
    static readonly BindingFact[] PagedFacts = [BindingFact.BodyBytes, BindingFact.MetadataRows];

    /// <summary>
    /// A paged fact's generated module and the namespace of its pages; the theorem that states it, the proposition
    /// it states about `BindingAudit.images` and `Extracted.methodEvidence`, and the check and claims its pages
    /// read; the lemma its proposition conjoins before the pages, proved once over the whole evidence, if any; and
    /// the module title, summary and theorem docstring.
    /// </summary>
    static (string Module, string Pages, string Theorem, string Proposition, string Check, string Claims,
        (string Theorem, string Proposition, string Docstring)? Once, string Title, string Summary, string Statement)
        PagedFact(BindingFact fact) => fact switch
    {
        BindingFact.BodyBytes => (BodiesModule, "Bodies", "bodies", "StrictBinding.BodiesBound",
            "StrictBinding.bodyClaimBound", "StrictBinding.bodyClaims", null, "Method bodies in the pinned images",
            "Every method body of the extraction's evidence is the bytes at the place the MethodDef row of its\n" +
            "token gives in the pinned image of its assembly",
            "The method bodies of `Extracted.methodEvidence` are in the pinned images."),
        BindingFact.MetadataRows => (MetadataRowsModule, "MetadataRows", "metadataRows",
            "StrictBinding.MetadataRowsBound", "StrictBinding.methodMetadataBound", "StrictBinding.metadataClaims",
            ("blocks", "StrictBinding.ClaimsHold StrictBinding.assemblyBlockBound images\n" +
                "    (StrictBinding.assemblyBlocks (StrictBinding.metadataClaims Extracted.methodEvidence))",
                "Each distinct Assembly block of the evidence is the pinned image's."),
            "Method metadata in the pinned images",
            "Every metadata block of the extraction's evidence holds the table header, Assembly row, table rows\n" +
            "and heap entries of the pinned image its identity names, under one numbering of the #Strings and\n" +
            "#Blob offsets per heap and with MethodDef RVAs zeroed, each distinct Assembly block checked once",
            "The metadata blocks of `Extracted.methodEvidence` belong to the pinned images."),
        _ => throw new ArgumentOutOfRangeException(nameof(fact), fact, "Not a paged binding fact")
    };

    /// <summary>The method bodies per page until the page cap applies; each page is one kernel evaluation.</summary>
    const int PageMethodsTarget = 250;

    /// <summary>The most pages; each page prepares the image again, so this bounds the preparation work.</summary>
    const int MaximumPages = 8;

    // Pages number ceil(methods / 250) up to 8, and then grow as methods / 8, so the image is prepared at most
    // nine times whatever the method count.
    static int BindingPageCount(int methods) =>
        Math.Clamp((methods + PageMethodsTarget - 1) / PageMethodsTarget, 1, MaximumPages);

    static int BindingPageSize(int methods)
    {
        var pages = BindingPageCount(methods);
        return Math.Max(1, (methods + pages - 1) / pages);
    }

    static int BindingPageCount(int methods, int pageSize) => Math.Max(1, (methods + pageSize - 1) / pageSize);

    string? bindingSession, bindingSourcesKey, bindingLeanVersion;
    BindingLibraryPreparation? bindingPreparation;

    /// <summary>The exact library and session artifacts certified for the strict binding sources.</summary>
    sealed record BindingLibraryPreparation(string Library, string LibraryKey, string Toolchain,
        SortedDictionary<string, string> BaseArtifacts, SortedDictionary<string, string> SessionArtifacts,
        SortedDictionary<string, string> CertifiedArtifacts);

    /// <summary>Builds and replays StrictBinding in the caller's selected, certified library session.</summary>
    void PrepareBindingLibrary(string package)
    {
        if (session is null || library is null || libraryKey is null || certifiedModules is null ||
            !SameLocation(package, session))
            throw new InvalidOperationException("StrictBinding requires the selected certified library session");
        RequireUnchangedLibrary();
        if (bindingPreparation is not null)
        {
            if (!Same(RequirePreparedBindingLibrary(), certifiedModules))
                throw new InvalidOperationException("The certified library changed before preparing StrictBinding");
            return;
        }
        var beforeBase = ModuleArtifacts(library);
        var beforeSession = ModuleArtifacts(session);
        var current = new SortedDictionary<string, string>(beforeBase, StringComparer.Ordinal);
        foreach (var (name, hash) in beforeSession) current[name] = hash;
        if (!Same(current, certifiedModules) ||
            baseModules!.Any(pair => !beforeBase.TryGetValue(pair.Key, out var hash) || hash != pair.Value))
            throw new InvalidOperationException("The certified library changed before preparing StrictBinding");
        var toolchain = BindingToolchainKey(session);
        CopyBindingSources(session);
        var sourcesKey = BindingSourcesKey(session);
        var leanVersion = Run([LeanExecutable, "--version"]).Trim();
        Run(["lake", "build", "StrictBinding"], session, progress: "Building the strict binding library");
        var afterBase = ModuleArtifacts(library);
        var afterSession = ModuleArtifacts(session);
        current = new(afterBase, StringComparer.Ordinal);
        foreach (var (name, hash) in afterSession) current[name] = hash;
        if (!Same(beforeBase, afterBase) ||
            !ModuleArtifactsPreserved(beforeSession, afterSession) ||
            !ModuleArtifactsPreserved(certifiedModules, current))
            throw new InvalidOperationException("The certified library changed while building StrictBinding");
        string[] added =
            [.. current.Keys.Where(name => !certifiedModules.ContainsKey(name)).Select(ModuleName).Distinct()];
        if (sourcesKey != BindingSourcesKey(session) || toolchain != BindingToolchainKey(session))
            throw new InvalidOperationException("The strict binding sources or toolchain changed during preparation");
        if (added.Length != 0)
            ReplayCheckedModules(added, SessionLeanPath(session), "Kernel replay of the strict binding library");
        if (!Same(afterBase, ModuleArtifacts(library)) || !Same(afterSession, ModuleArtifacts(session)) ||
            sourcesKey != BindingSourcesKey(session) || toolchain != BindingToolchainKey(session))
            throw new InvalidOperationException("The strict binding library changed during preparation");
        certifiedModules = current;
        bindingSession = session;
        bindingSourcesKey = sourcesKey;
        bindingLeanVersion = leanVersion;
        bindingPreparation = new(library, libraryKey, toolchain, afterBase, afterSession,
            new(current, StringComparer.Ordinal));
    }

    /// <summary>The prepared library retains its sources, toolchain and every original artifact family.</summary>
    SortedDictionary<string, string> RequirePreparedBindingLibrary()
    {
        var prepared = bindingPreparation ??
            throw new InvalidOperationException("StrictBinding has not been prepared");
        RequireUnchangedLibrary();
        if (session is null || bindingSession != session || prepared.Library != library ||
            prepared.LibraryKey != libraryKey || prepared.Toolchain != BindingToolchainKey(session) ||
            bindingSourcesKey != BindingSourcesKey(session))
            throw new InvalidOperationException("The prepared StrictBinding library changed");
        var baseArtifacts = ModuleArtifacts(library!);
        var sessionArtifacts = ModuleArtifacts(session);
        var current = new SortedDictionary<string, string>(baseArtifacts, StringComparer.Ordinal);
        foreach (var (name, hash) in sessionArtifacts) current[name] = hash;
        if (!Same(prepared.BaseArtifacts, baseArtifacts) ||
            !ModuleArtifactsPreserved(prepared.SessionArtifacts, sessionArtifacts) ||
            !ModuleArtifactsPreserved(prepared.CertifiedArtifacts, current))
            throw new InvalidOperationException("The prepared StrictBinding library changed");
        return current;
    }

    /// <summary>Existing module families retain exactly their artifacts; additional families are permitted.</summary>
    static bool ModuleArtifactsPreserved(SortedDictionary<string, string> before,
        SortedDictionary<string, string> after)
    {
        HashSet<string> families = new(StringComparer.Ordinal);
        foreach (var (name, hash) in before)
        {
            if (!after.TryGetValue(name, out var current) || current != hash) return false;
            families.Add(ModuleName(name));
        }
        foreach (var name in after.Keys)
            if (families.Contains(ModuleName(name)) && !before.ContainsKey(name)) return false;
        return true;
    }

    /// <summary>The toolchain declaration and compiler bytes used to prepare the binding library.</summary>
    string BindingToolchainKey(string package) => ContentKey(Sha(Path.Combine(package, "lean-toolchain")) +
        "\n" + Toolchain + "\n" + Sha(LeanExecutable));

    /// <summary>Copies the StrictBinding library's sources into a package, below the same relative paths.</summary>
    static void CopyBindingSources(string package)
    {
        var sources = Directory.EnumerateFiles(At("StrictBinding"), "*.lean", SearchOption.AllDirectories)
            .Append(At("StrictBinding.lean"));
        foreach (var source in sources)
        {
            var destination = Path.Combine(package, Path.GetRelativePath(Root, source));
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(source, destination, true);
        }
    }

    /// <summary>Derives a coverage bit from the physical checks and proves its value for the selected methods.</summary>
    static string CoverageSource(string check, string proposition, string theorem, string macro, string module,
        string arguments = "Extracted.platformDefinitions Extracted.methodEvidence") => $$"""
            import BindingAudit.Images
            import Extracted
            import StrictBinding.{{module}}
            import Lean

            namespace BindingAudit

            open Lean Elab Term in
            elab "{{macro}}%" : term => do
              return toExpr ((StrictBinding.{{check}} images {{arguments}}).toOption == some true)

            set_option debug.skipKernelTC true in
            /-- Supplied definitions pass the physical check. The last argument records completeness. -/
            theorem {{theorem}} : StrictBinding.{{proposition}} images {{arguments}} {{macro}}% := by decide +kernel

            end BindingAudit

            """;

    /// <summary>Writes one image module per digest and retains every pinned identity association.</summary>
    static void WriteBindingSources(BindingPlan plan)
    {
        foreach (var image in plan.Images.DistinctBy(image => image.Digest))
            File.WriteAllText(ModuleSource(plan.Output, image.Module), ImageModuleSource(image));
        File.WriteAllText(ModuleSource(plan.Output, ImagesModule), ImagesModuleSource(plan));
        File.WriteAllText(ModuleSource(plan.Output, EnumStorageModule), CoverageSource(
            "checkEnumStorage", "EnumStorageChecked", "enumStorage", "enumCoverage", "EnumStorage"));
        File.WriteAllText(ModuleSource(plan.Output, GenericConstraintsModule), CoverageSource(
            "checkGenericConstraints", "GenericConstraintsChecked", "genericConstraints", "constraintCoverage",
            "GenericConstraints", "Extracted.methodEvidence Extracted.rawLayouts Extracted.imports"));
        File.WriteAllText(ModuleSource(plan.Output, PlatformKindsModule), CoverageSource(
            "checkPlatformKinds", "PlatformKindsChecked", "platformKinds", "kindCoverage", "PlatformKinds"));
        File.WriteAllText(ModuleSource(plan.Output, StaticDataModule), """
            import BindingAudit.Images
            import Extracted
            import StrictBinding.StaticData

            namespace BindingAudit

            set_option debug.skipKernelTC true in
            /-- The complete RVA data of each static site agrees with the pinned assembly. -/
            theorem staticData : StrictBinding.StaticDataBound images Extracted.methodEvidence := by
              decide +kernel

            end BindingAudit

            """);
        if (plan.ObjectFields is { } complete)
            File.WriteAllText(ModuleSource(plan.Output, ObjectFieldsModule), $$"""
                import BindingAudit.Images
                import Extracted
                import StrictBinding.ObjectFields

                namespace BindingAudit

                set_option debug.skipKernelTC true in
                /-- The supplied reference images agree with these methods about System.Object fields. -/
                theorem objectFields :
                    StrictBinding.{{ObjectProposition(complete)}} images Extracted.methodEvidence := by decide +kernel

                end BindingAudit

                """);
        if (plan.TupleFields is { } pairComplete)
            File.WriteAllText(ModuleSource(plan.Output, TupleFieldsModule), $$"""
                import BindingAudit.Images
                import Extracted
                import StrictBinding.TupleFields

                namespace BindingAudit

                set_option debug.skipKernelTC true in
                /-- The pinned platform pair declares the selected layout's two fields in generic slot order. -/
                theorem tupleFields : StrictBinding.{{TupleProposition(pairComplete)}} images
                    Extracted.methodEvidence Extracted.rawLayouts := by decide +kernel

                end BindingAudit

                """);
        if (plan.PublicKeys is { } keysComplete)
            File.WriteAllText(ModuleSource(plan.Output, PublicKeysModule), $$"""
                import BindingAudit.Images
                import Extracted
                import StrictBinding.PublicKeys

                namespace BindingAudit

                set_option debug.skipKernelTC true in
                /-- The supplied reference images carry the keys named by the extraction pins. -/
                theorem publicKeyTokens : StrictBinding.{{KeyProposition(keysComplete)}} images
                    Extracted.assemblies Extracted.methodEvidence := by decide +kernel

                end BindingAudit

                """);
        foreach (var fact in PagedFacts)
            File.WriteAllText(ModuleSource(plan.Output, PagedFact(fact).Module), PagedFactModuleSource(fact,
                plan.Methods, BindingPageSize(plan.Methods)));
    }

    static string KeyProposition(bool complete) => complete ? "PublicKeysBound" : "SuppliedPublicKeysValid";

    static string TupleProposition(bool complete) => complete ? "TupleFieldsBound" : "SuppliedTupleFieldsValid";

    static string ObjectProposition(bool complete) => complete ? "ObjectFieldsBound" : "SuppliedObjectFieldsValid";

    static string ModuleSource(string directory, string module) =>
        Path.Combine(directory, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");

    static string ImageModuleSource(BindingImagePin image) => $$"""
        import StrictBinding.Sha256
        import CIL.Extraction.FixedDigits

        /-!
        # Image of an assembly file

        The bytes of one assembly file as an `ImageBytes` constant, and the SHA-256 digest of those
        bytes proved page by page. Each page lemma is kernel-checked only when this module is replayed.
        -/

        namespace {{image.Module}}

        {{BindingImage.Definitions(image.Bytes)}}
        {{BindingImage.PagedDigestTheorem(image.Bytes, skipCompileCheck: true)}}
        end {{image.Module}}
        """;

    static string ImagesModuleSource(BindingPlan plan)
    {
        var imports = string.Concat(plan.Images.DistinctBy(image => image.Digest)
            .Select(image => $"import {image.Module}\n"));
        var entries = string.Join(",\n   ", plan.Images.Select(image =>
            $"{{ identity := {LeanString(image.Identity)}, image := {image.Module}.image }}"));
        return $"""
            import Lean
            import StrictBinding.Image
            {imports}
            /-!
            # The pinned images

            Each assembly the extraction read, under the identity the extraction records for it, with the
            image constant whose SHA-256 digest its own module proves.
            -/

            namespace BindingAudit

            open Lean Elab in
            /-- Exact pinned-image list constructors with independently elaborated elements. -/
            elab "pinnedImages%[" items:term,* "]" : term => do
              let type := mkConst ``StrictBinding.PinnedImage
              let values <- items.getElems.mapM fun item => Term.elabTermEnsuringType item (some type)
              return values.foldr (mkApp3 (mkConst ``List.cons [.zero]) type)
                (mkApp (mkConst ``List.nil [.zero]) type)

            /-- The pinned images the audit reads. -/
            def images : List StrictBinding.PinnedImage :=
              pinnedImages%[{entries}]

            /-- The identities and image constants of `images`, as the driver states them. -/
            theorem images_eq : images =
              pinnedImages%[{entries}] := rfl

            end BindingAudit
            """;
    }

    /// <summary>
    /// The module of a paged fact: one theorem per page of the claims the method evidence makes, each its own kernel
    /// evaluation, and the fact's theorem, which the kernel-checked composition `claimsHold_of_pages` derives for
    /// the whole evidence. The composition needs the pages to number enough to cover the evidence and to be the
    /// first pages in order, so no claim is skipped, repeated or reordered.
    /// </summary>
    static string PagedFactModuleSource(BindingFact fact, int methods, int size)
    {
        var paged = PagedFact(fact);
        var pages = BindingPageCount(methods, size);
        var lemmas = string.Concat(Enumerable.Range(0, pages).Select(page => $$"""
            set_option debug.skipKernelTC true in
            /-- The claims of page {{page}} hold in the pinned images. -/
            theorem page{{page}} : StrictBinding.ClaimsHold {{paged.Check}} images
                (StrictBinding.claimPage ({{paged.Claims}} Extracted.methodEvidence) {{size}} {{page}}) := by
              decide +kernel


            """));
        var chain = string.Concat(Enumerable.Range(0, pages).Reverse()
            .Select(page => $"(.succ {paged.Pages}.page{page} "));
        var composed = $"StrictBinding.claimsHold_of_pages (size := {size}) (count := {pages}) " +
            $"{paged.Pages}.prepared\n    (by decide +kernel) {chain}.zero{new string(')', pages)}";
        var once = paged.Once is { } whole ? $$"""
            set_option debug.skipKernelTC true in
            /-- {{whole.Docstring}} -/
            theorem {{whole.Theorem}} : {{whole.Proposition}} := by
              decide +kernel


            """ : "";
        var proof = paged.Once is { } conjoined
            ? $"And.intro {paged.Pages}.{conjoined.Theorem}\n  " +
                $"({composed.Replace("\n", "\n  ", StringComparison.Ordinal)})"
            : composed;
        return $$"""
            import BindingAudit.Images
            import Extracted
            import StrictBinding.Evidence

            /-!
            # {{paged.Title}}

            {{paged.Summary}}, proved page by page. The preparation and each page lemma are kernel-checked
            when this module is replayed.
            -/

            namespace BindingAudit
            namespace {{paged.Pages}}

            set_option debug.skipKernelTC true in
            /-- The pinned images decode and spell the identities they are pinned under. -/
            theorem prepared : StrictBinding.ok (StrictBinding.prepare images) = true := by decide +kernel

            {{once}}{{lemmas}}end {{paged.Pages}}

            /-- {{paged.Statement}} -/
            theorem {{paged.Theorem}} : {{paged.Proposition}} images Extracted.methodEvidence :=
              {{proof}}

            end BindingAudit
            """;
    }

    /// <summary>A theorem the audit expects in a module, with the type the driver derives from the plan.</summary>
    sealed record BindingRequest(string Module, AuditRequest Audit, BindingSubject? Subject = null);

    /// <summary>Generator-owned request and module subjects, indexed before any generated code runs.</summary>
    sealed class BindingTargets(BindingRequest[] requests)
    {
        internal BindingRequest[] Requests { get; } = requests;
        internal Dictionary<string, BindingSubject?> Theorems { get; } = requests.ToDictionary(
            request => request.Audit.name, request => request.Subject, StringComparer.Ordinal);
        internal Dictionary<string, BindingSubject?> Modules { get; } = requests.ToDictionary(
            request => request.Module, request => request.Subject, StringComparer.Ordinal);
    }

    /// <summary>The audited theorems with expected types built from the plan, never from module text.</summary>
    static BindingRequest[] BindingRequests(BindingPlan plan)
    {
        static object Const(string name, params int[] levels) =>
            levels.Length == 0 ? new { @const = name } : new { @const = name, levels };
        static object App(params object[] parts) => new { app = parts };
        static JsonElement Nat(Sha256Digest digest)
        {
            Span<byte> bytes = stackalloc byte[Sha256Digest.Length];
            digest.CopyTo(bytes);
            var value = new BigInteger(bytes, isUnsigned: true, isBigEndian: true);
            return JsonDocument.Parse("{\"nat\":" + value.ToString(CultureInfo.InvariantCulture) + "}").RootElement;
        }
        var pinned = Const("StrictBinding.PinnedImage");
        var images = new
        {
            list = new
            {
                type = pinned,
                level = 0,
                items = plan.Images.Select(image =>
                    App(Const("StrictBinding.PinnedImage.mk"), new { str = image.Identity },
                        Const(image.Module + ".image"))).ToArray()
            }
        };
        var imagesEq = App(Const("Eq", 1), App(Const("List", 0), pinned), Const("BindingAudit.images"), images);
        List<BindingRequest> platform = [];
        if (plan.ObjectFields is { } complete)
        {
            var statement = App(Const("StrictBinding." + ObjectProposition(complete)), Const("BindingAudit.images"),
                Const("Extracted.methodEvidence"));
            platform.Add(new(ObjectFieldsModule, new("BindingAudit.objectFields", statement, ApprovedAxioms),
                new BindingSubject.Fact(BindingFact.ObjectFields, complete)));
        }
        if (plan.TupleFields is { } pairComplete)
        {
            var statement = App(Const("StrictBinding." + TupleProposition(pairComplete)), Const("BindingAudit.images"),
                Const("Extracted.methodEvidence"), Const("Extracted.rawLayouts"));
            platform.Add(new(TupleFieldsModule, new("BindingAudit.tupleFields", statement, ApprovedAxioms),
                new BindingSubject.Fact(BindingFact.ValueTupleFieldOrder, pairComplete)));
        }
        if (plan.PublicKeys is { } keysComplete)
        {
            var statement = App(Const("StrictBinding." + KeyProposition(keysComplete)), Const("BindingAudit.images"),
                Const("Extracted.assemblies"), Const("Extracted.methodEvidence"));
            platform.Add(new(PublicKeysModule, new("BindingAudit.publicKeyTokens", statement, ApprovedAxioms),
                new BindingSubject.Fact(BindingFact.PublicKeyTokens, keysComplete)));
        }
        return
        [
            new("Extracted", ExtractionCertificate("Extracted.translation_valid")),
            new(ImagesModule, new("BindingAudit.images_eq", imagesEq, ApprovedAxioms)),
            new(GenericConstraintsModule, new(GenericConstraintsTheorem,
                App(Const("StrictBinding.GenericConstraintsChecked"),
                Const("BindingAudit.images"), Const("Extracted.methodEvidence"), Const("Extracted.rawLayouts"),
                Const("Extracted.imports"), "_"), ApprovedAxioms, term: true),
                new BindingSubject.Fact(BindingFact.GenericConstraints)),
            new(PlatformKindsModule, new(PlatformKindsTheorem, App(Const("StrictBinding.PlatformKindsChecked"),
                Const("BindingAudit.images"), Const("Extracted.platformDefinitions"),
                Const("Extracted.methodEvidence"), "_"), ApprovedAxioms, term: true),
                new BindingSubject.Fact(BindingFact.PlatformTypeKinds)),
            new(EnumStorageModule, new(EnumStorageTheorem, App(Const("StrictBinding.EnumStorageChecked"),
                Const("BindingAudit.images"), Const("Extracted.platformDefinitions"),
                Const("Extracted.methodEvidence"), "_"), ApprovedAxioms, term: true),
                new BindingSubject.Fact(BindingFact.EnumUnderlyingTypes)),
            .. PagedFacts.Select(fact => (Fact: fact, Paged: PagedFact(fact))).Select(item => new BindingRequest(
                item.Paged.Module, new("BindingAudit." + item.Paged.Theorem, App(Const(item.Paged.Proposition),
                    Const("BindingAudit.images"), Const("Extracted.methodEvidence")), ApprovedAxioms),
                new BindingSubject.Fact(item.Fact))),
            new(StaticDataModule, new("BindingAudit.staticData", App(Const("StrictBinding.StaticDataBound"),
                Const("BindingAudit.images"), Const("Extracted.methodEvidence")), ApprovedAxioms),
                new BindingSubject.Fact(BindingFact.StaticData)),
            .. platform,
            .. plan.Images.DistinctBy(image => image.Digest).Select(image => new BindingRequest(image.Module,
                new(image.Theorem,
                App(Const("StrictBinding.DigestIs"), Const(image.Module + ".image"), Nat(image.Digest)),
                ApprovedAxioms), new BindingSubject.Image(image.Digest)))
        ];
    }

    /// <summary>
    /// Builds the binding modules against the selected extraction and records failures by module.
    /// A module whose prerequisite failed is recorded as skipped.
    /// </summary>
    Dictionary<string, string> BuildBindingModules(BindingPlan plan, string leanPath)
    {
        string? Build(string module)
        {
            var source = ModuleSource(plan.Output, module);
            var olean = Path.ChangeExtension(source, ".olean");
            var result = Execute([LeanExecutable, "--root=" + plan.Output, "-o", olean, source], leanPath: leanPath,
                progress: "Checking " + module, environment: LeanEnvironment);
            return result.Code == 0 ? null : BindingDiagnostic(result.Output);
        }
        Dictionary<string, string> failures = new(StringComparer.Ordinal);
        foreach (var image in plan.Images.DistinctBy(image => image.Digest))
            if (Build(image.Module) is { } error) failures[image.Module] = "build: " + error;
        if (plan.Images.Any(image => failures.ContainsKey(image.Module)))
            failures[ImagesModule] = "build: an image module did not build";
        else if (Build(ImagesModule) is { } imagesError) failures[ImagesModule] = "build: " + imagesError;
        var facts = PagedFacts.Select(fact => PagedFact(fact).Module)
            .Append(StaticDataModule).Append(EnumStorageModule).Append(PlatformKindsModule)
            .Append(GenericConstraintsModule);
        if (plan.ObjectFields.HasValue) facts = facts.Append(ObjectFieldsModule);
        if (plan.TupleFields.HasValue) facts = facts.Append(TupleFieldsModule);
        if (plan.PublicKeys.HasValue) facts = facts.Append(PublicKeysModule);
        foreach (var module in facts)
            if (failures.ContainsKey(ImagesModule)) failures[module] = "build: " + ImagesModule + " did not build";
            else if (Build(module) is { } pagedError) failures[module] = "build: " + pagedError;
        return failures;
    }

    static string BindingSourcesKey(string root) => ContentKey(string.Join("\n", Directory
        .EnumerateFiles(Path.Combine(root, "StrictBinding"), "*.lean", SearchOption.AllDirectories)
        .Append(Path.Combine(root, "StrictBinding.lean"))
        .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/') + "=" + Sha(path))
        .Order(StringComparer.Ordinal)));

    /// <summary>The first error of a Lean message, flattened and shortened for a report line.</summary>
    static string BindingDiagnostic(string output)
    {
        var lines = output.Split('\n').Select(line => line.Trim()).Where(line => line.Length > 0).ToArray();
        var first = Math.Max(0,
            Array.FindIndex(lines, line => line.Contains("error", StringComparison.OrdinalIgnoreCase) ||
                line.Contains("while replaying declaration", StringComparison.Ordinal)));
        var text = string.Join(" ", lines.Skip(first).Take(3));
        return text.Length > 300 ? text[..300] + "..." : text;
    }
}
