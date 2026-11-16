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
        readonly Dictionary<Sha256Digest, string> rejectedImages = [];
        readonly Dictionary<BindingFact, string> rejectedFacts = [];
        internal string IdentitySha256 { get; }

        internal DeepCheckAttempt(DeepCheckInputs inputs, string identitySha256,
            IReadOnlyList<DeepCheckInputs.Pin> pins)
        {
            digests = new(inputs.Path, inputs.Digest.ToString());
            IdentitySha256 = identitySha256;
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
        internal sealed record Fact(BindingFact Value) : BindingSubject;
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
    sealed record BindingPlan(string Output, BindingImagePin[] Images, int Methods);

    /// <summary>Artifacts and requests that must join the caller's extraction and proof audit.</summary>
    sealed record DeepSessionContribution(string[] Modules, BindingTargets Targets,
        SortedDictionary<string, string> Artifacts, SortedDictionary<string, string> Hashes,
        SortedDictionary<string, string> SourceHashes, string SourceDirectory)
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
    static SortedDictionary<string, string> BindingArtifactHashes(IEnumerable<string> artifacts)
    {
        var families = artifacts.Select(Path.GetFullPath)
            .GroupBy(artifact => Path.GetDirectoryName(artifact)!, LocationComparer);
        List<(string Name, string Path)> files = [];
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
                    files.Add((path, path));
            }
        }
        return HashFiles(files);
    }

    /// <summary>Builds deep modules against the caller's existing extraction in its verification session.</summary>
    DeepSessionContribution BuildDeepSession(string session, string leanPath, string extractedOlean,
        ExtractionIdentity identity, IReadOnlyList<DeepCheckInputs.Pin> matchedPins, Action? sourcesReady = null)
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
            identity.Root.GetProperty("methods").GetArrayLength());
        var directory = Path.Combine(session, "BindingAudit");
        if (Directory.Exists(directory))
            throw new InvalidOperationException("Deep-check modules already exist in the session: " + directory);
        Directory.CreateDirectory(directory);
        var targets = new BindingTargets(BindingRequests(plan));
        WriteBindingSources(plan);
        sourcesReady?.Invoke();
        var sources = BindingSourceHashes(directory);
        var failures = BuildBindingModules(plan, leanPath);
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
            BindingArtifactHashes(artifacts.Values), sources, directory);
        contribution.RequireStable();
        return contribution;
    }

    /// <summary>
    /// The facts and images of a complete, stable joint deep audit, read from the subjects of the requests that
    /// audit passed: each subject is reconfirmed by its request's theorem, and every fact no request names is not
    /// covered for its recorded reason.
    /// </summary>
    static BindingSection DeepBindingSection(DeepCheckInputs inputs, IReadOnlyList<DeepCheckInputs.Pin> pins,
        IReadOnlyList<BindingRequest> audited, StatementSources sources)
    {
        Dictionary<BindingFact, string> factTheorems = [];
        Dictionary<Sha256Digest, string> imageTheorems = [];
        foreach (var request in audited)
        {
            var distinct = request.Subject switch
            {
                BindingSubject.Fact fact => factTheorems.TryAdd(fact.Value, request.Audit.name),
                BindingSubject.Image image => imageTheorems.TryAdd(image.Digest, request.Audit.name),
                _ => true
            };
            if (!distinct) throw new InvalidOperationException("Two deep-check requests name one subject: " +
                request.Audit.name);
        }
        var pinnedDigests = pins.Select(pin => pin.Image.Digest).ToHashSet();
        ImageResult[] images =
        [
            .. pins.Select(pin => imageTheorems.TryGetValue(pin.Image.Digest, out var theorem)
                ? new ImageResult(pin.Identity, pin.Image.Digest.ToString(), ImageRole.Pinned,
                    BindingStatus.Reconfirmed, theorem, null)
                : new ImageResult(pin.Identity, pin.Image.Digest.ToString(), ImageRole.Pinned, BindingStatus.NotCovered,
                    null,
                    "no checked theorem states the digest of this image")),
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
        BindingFact.PlatformTypeKinds => "no check reads platform type kinds from an image",
        BindingFact.EnumUnderlyingTypes => "no check reads platform enum underlying types from an image",
        BindingFact.ValueTupleFieldOrder => "no check reads platform tuple field order from an image",
        BindingFact.ObjectFields => "no check reads System.Object fields from an image",
        BindingFact.LayoutContent => "no check reads field offsets, sizes or attributes from the image",
        BindingFact.DispatchCatalogs => "no check reads the types of an image",
        BindingFact.StaticData => "no check reads static data from the image",
        BindingFact.GenericConstraints => "no check reads constraints from the image",
        BindingFact.PublicKeyTokens => "no check compares a reference's token with the key of its image",
        BindingFact.ImportIdentities => "no check recomputes an import identity from its image",
        _ => throw new InvalidOperationException("Missing binding fact reason: " + fact)
    };

    const string ImagesModule = "BindingAudit.Images";
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

    /// <summary>Writes one image module per digest and retains every pinned identity association.</summary>
    static void WriteBindingSources(BindingPlan plan)
    {
        foreach (var image in plan.Images.DistinctBy(image => image.Digest))
            File.WriteAllText(ModuleSource(plan.Output, image.Module), ImageModuleSource(image));
        File.WriteAllText(ModuleSource(plan.Output, ImagesModule), ImagesModuleSource(plan));
        foreach (var fact in PagedFacts)
            File.WriteAllText(ModuleSource(plan.Output, PagedFact(fact).Module), PagedFactModuleSource(fact,
                plan.Methods, BindingPageSize(plan.Methods)));
    }

    static string ModuleSource(string directory, string module) =>
        Path.Combine(directory, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");

    static string ImageModuleSource(BindingImagePin image) => $$"""
        import StrictBinding.Sha256

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
        return
        [
            new("Extracted", ExtractionCertificate("Extracted.translation_valid")),
            new(ImagesModule, new("BindingAudit.images_eq", imagesEq, ApprovedAxioms)),
            .. PagedFacts.Select(fact => (Fact: fact, Paged: PagedFact(fact))).Select(item => new BindingRequest(
                item.Paged.Module, new("BindingAudit." + item.Paged.Theorem, App(Const(item.Paged.Proposition),
                    Const("BindingAudit.images"), Const("Extracted.methodEvidence")), ApprovedAxioms),
                new BindingSubject.Fact(item.Fact))),
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
        foreach (var module in PagedFacts.Select(fact => PagedFact(fact).Module))
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
