using System.Globalization;
using System.Numerics;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

// The opt-in strict binding audit: kernel-checked proof that the method bodies of an extraction are the bytes of
// assembly files whose SHA-256 digests the caller states. Nothing here is read by `check`, `extract` or `verify`.
partial class Program
{
    internal const string BindingAuditUsage =
        "Usage: leancil audit-binding extraction-directory --sha256 hex [--assembly-path assembly.dll] " +
        "[--reference-sha256 Lib=hex]... [--require item,...] [--output directory] " +
        "[--format text|json] [--results results.json]";

    /// <summary>An assembly file the extraction read, with the digest the caller must confirm.</summary>
    sealed record BindingImagePin(string Identity, string Path, string Sha256, string Source, byte[] Bytes)
    {
        /// <summary>The generated module that holds the file's bytes, named by its full digest.</summary>
        internal string Module => "BindingAudit.I" + Sha256;

        internal string Theorem => Module + ".digest";

        /// <summary>The assembly's simple name, which names it in `--reference-sha256` and in item ids.</summary>
        internal string Name => Identity.Split(',')[0];
    }

    /// <summary>What a run audits: the extraction, the files it pinned and where the generated modules go.</summary>
    sealed record BindingPlan(string Extraction, string Output, string GeneratedSha256, string IdentitySha256,
        BindingImagePin[] Images, int Methods, int? PageSize = null);

    /// <summary>Artifacts and requests that must join the caller's extraction and proof audit.</summary>
    sealed record DeepSessionContribution(string[] Modules, BindingRequest[] Requests,
        SortedDictionary<string, string> Artifacts, SortedDictionary<string, string> Hashes,
        SortedDictionary<string, string> SourceHashes)
    {
        internal void RequireStable()
        {
            if (!Same(Hashes, BindingArtifactHashes(Artifacts.Values)))
                throw new InvalidDataException("Deep-check artifact changed");
            foreach (var (path, hash) in SourceHashes)
                if (!File.Exists(path) || Sha(path) != hash)
                    throw new InvalidDataException("Deep-check source changed: " + path);
        }

        internal void RequireAudited(AuditedOleans audited)
        {
            RequireStable();
            foreach (var (module, path) in Artifacts) RequireAuditedModule(audited, module, path);
        }
    }

    /// <summary>Hashes the exact compiled module families, enumerating each containing directory once.</summary>
    static SortedDictionary<string, string> BindingArtifactHashes(IEnumerable<string> artifacts)
    {
        var comparer = OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;
        var families = artifacts.Select(Path.GetFullPath).GroupBy(Path.GetDirectoryName, comparer);
        List<(string Name, string Path)> files = [];
        foreach (var family in families)
        {
            var expected = family.ToHashSet(comparer);
            foreach (var artifact in expected)
                if (!File.Exists(artifact))
                    throw new InvalidDataException("Deep-check artifact changed: missing " + artifact);
            foreach (var path in Directory.EnumerateFiles(family.Key!))
            {
                var filename = Path.GetFileName(path);
                var marker = filename.IndexOf(".olean", OperatingSystem.IsWindows()
                    ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal);
                if (marker < 0) continue;
                var end = marker + ".olean".Length;
                if ((end == filename.Length || filename[end] == '.') &&
                    expected.Contains(Path.Combine(family.Key!, filename[..end])))
                    files.Add((path, path));
            }
        }
        return HashFiles(files);
    }

    /// <summary>Builds deep modules against the caller's existing extraction in its verification session.</summary>
    DeepSessionContribution BuildDeepSession(string session, string leanPath, string extractedOlean,
        ExtractionIdentity identity, DeepCheckInputs inputs)
    {
        session = Path.GetFullPath(session);
        extractedOlean = Path.GetFullPath(extractedOlean);
        if (!File.Exists(extractedOlean)) throw new FileNotFoundException("Missing extraction module", extractedOlean);
        var extractedHashes = BindingArtifactHashes([extractedOlean]);
        Dictionary<string, byte[]> bytes = new(StringComparer.Ordinal);
        var pins = inputs.MatchPins(identity.Root).Select(pin =>
        {
            if (!bytes.TryGetValue(pin.Image.Digest, out var snapshot))
                bytes.Add(pin.Image.Digest, snapshot = pin.Image.Bytes.ToArray());
            return new BindingImagePin(pin.Identity, pin.Image.Path, pin.Image.Digest, "stated", snapshot);
        }).ToArray();
        BindingPlan plan = new(identity.Output, session,
            identity.Root.GetProperty("generatedSha256").GetString()!, identity.Sha256, pins,
            identity.Root.GetProperty("methods").GetArrayLength());
        var directory = Path.Combine(session, "BindingAudit");
        if (Directory.Exists(directory))
            throw new InvalidOperationException("Deep-check modules already exist in the session: " + directory);
        Directory.CreateDirectory(directory);
        WriteBindingSources(plan);
        var failures = BuildBindingModules(plan, leanPath, buildExtracted: false);
        if (failures.Count != 0)
            throw new InvalidOperationException("Deep-check module build failed: " +
                string.Join("; ", failures.Select(pair => pair.Key + ": " + pair.Value)));
        var requests = BindingRequests(plan);
        string[] modules = [.. requests.Select(request => request.Module).Distinct(StringComparer.Ordinal)];
        SortedDictionary<string, string> artifacts = new(StringComparer.Ordinal) { ["Extracted"] = extractedOlean };
        SortedDictionary<string, string> sources = new(StringComparer.Ordinal);
        foreach (var module in modules.Where(module => module != "Extracted"))
        {
            var source = ModuleSource(session, module);
            var artifact = Path.ChangeExtension(source, ".olean");
            artifacts.Add(module, artifact);
            sources.Add(source, Sha(source));
        }
        if (!Same(extractedHashes, BindingArtifactHashes([extractedOlean])))
            throw new InvalidDataException("Deep-check artifact changed: " + extractedOlean);
        DeepSessionContribution contribution = new(modules, requests, artifacts,
            BindingArtifactHashes(artifacts.Values), sources);
        contribution.RequireStable();
        return contribution;
    }

    /// <summary>One line of the report: a fact the audit covers or does not, and what it found.</summary>
    sealed record BindingItem(string Id, string Title, string Status, string? Theorem = null, string? Reason = null)
    {
        internal string Group => Id.Split(':')[0];
    }

    sealed record BindingReport(string Extraction, string GeneratedSha256, BindingImagePin[] Images,
        BindingItem[] Items, string[] Axioms, string SourcesKey, string Toolchain, string LeanVersion);

    const string Reconfirmed = "reconfirmed";
    const string Matched = "matches the pinned digest";
    const string NotCovered = "not covered";
    const string Failed = "failed";
    const string DigestGroup = "digests";
    const string BodiesGroup = "body-locations";
    const string ImagesModule = "BindingAudit.Images";
    const string BodiesModule = "BindingAudit.Bodies";

    /// <summary>Marks a directory as an earlier audit's output, which a new audit replaces.</summary>
    const string BindingReportFile = "binding-audit.json";

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

    /// <summary>Facts the default flow trusts that the audit has no check for, in report order.</summary>
    static readonly (string Id, string Title, string Reason)[] UncoveredBindingFacts =
    [
        ("metadata-rows", "Copied metadata rows and heap entries",
            "the extraction's evidence carries no copied metadata rows or heap entries to check"),
        ("static-data", "Initial values of static data", "no check reads static data from the image"),
        ("layouts", "Type layouts", "no check reads field offsets, sizes or attributes from the image"),
        ("key-tokens", "Public key tokens of referenced assemblies",
            "no check compares a reference's token with the key of its image"),
        ("platform-definitions", "Definitions in platform assemblies", "no platform assembly is read"),
        ("dispatch-catalogs", "Completeness of dispatch catalogs", "no check reads the types of an image"),
        ("import-identities", "Hashed part of generic import identities",
            "no check recomputes an import identity from its image"),
        ("generic-constraints", "Generic parameter constraints", "no check reads constraints from the image")
    ];

    internal static int AuditBinding(string[] args)
    {
        string? extraction = null, assemblyPath = null, sha256 = null, output = null, results = null, format = "text";
        Dictionary<string, string> references = new(StringComparer.Ordinal);
        HashSet<string> required = new(StringComparer.Ordinal);
        for (var index = 0; index < args.Length; index++)
        {
            var option = args[index];
            if (!option.StartsWith("--", StringComparison.Ordinal))
            {
                if (extraction is not null)
                    throw new ArgumentException($"Unexpected argument: {option}\n{BindingAuditUsage}");
                extraction = Path.GetFullPath(option);
                continue;
            }
            if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) ||
                args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException($"Missing value for {option}.\n{BindingAuditUsage}");
            var value = args[index];
            switch (option)
            {
                case "--sha256" when sha256 is null: sha256 = StatedDigest(value, option); break;
                case "--assembly-path" when assemblyPath is null: assemblyPath = Path.GetFullPath(value); break;
                case "--output" when output is null: output = Path.GetFullPath(value); break;
                case "--results" when results is null: results = Path.GetFullPath(value); break;
                case "--format" when value is "text" or "json": format = value; break;
                case "--require":
                    required.UnionWith(value.Split(',',
                        StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries));
                    break;
                case "--reference-sha256":
                    var pair = value.Split('=', 2);
                    if (pair.Length != 2 || pair[0].Length == 0 ||
                        !references.TryAdd(pair[0], StatedDigest(pair[1], option)))
                        throw new ArgumentException($"--reference-sha256 takes one Library=hex, got {value}.");
                    break;
                default: throw new ArgumentException($"Unknown or duplicate option: {option}\n{BindingAuditUsage}");
            }
        }
        if (extraction is null || sha256 is null) throw new ArgumentException(BindingAuditUsage);
        var known = UncoveredBindingFacts.Select(fact => fact.Id)
            .Append(DigestGroup).Append(BodiesGroup).Append("all");
        if (required.FirstOrDefault(item => !known.Contains(item)) is { } unknown)
            throw new ArgumentException($"Unknown item in --require: {unknown}\n{BindingAuditUsage}");

        using Program verification = new();
        output ??= extraction.TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar) + ".binding-audit";
        var report = verification.RunBindingAudit(extraction, assemblyPath, sha256, references, output);
        var problems = BindingProblems(report, required);
        File.WriteAllText(Path.Combine(output, BindingReportFile), BindingJson(report) + "\n");
        if (results is not null) File.WriteAllText(results, BindingJson(report) + "\n");
        Console.WriteLine(format == "json" ? BindingJson(report) : BindingText(report, problems.Length == 0));
        if (problems.Length > 0)
            throw new InvalidOperationException("Strict binding audit: " + string.Join("; ", problems));
        return 0;
    }

    static string StatedDigest(string value, string option) =>
        Sha256Digest().IsMatch(value) ? value.ToLowerInvariant()
            : throw new ArgumentException($"{option} takes a SHA-256 digest of 64 hexadecimal digits, got {value}.");

    [GeneratedRegex(@"\A[0-9a-fA-F]{64}\z")]
    private static partial Regex Sha256Digest();

    /// <summary>The failed items and the required ones that are not reconfirmed.</summary>
    static string[] BindingProblems(BindingReport report, HashSet<string> required) =>
    [
        .. report.Items.Where(item => item.Status == Failed).Select(item => $"{item.Title} {Failed}: {item.Reason}"),
        .. report.Items
            .Where(item => item.Status is NotCovered or Matched &&
                (required.Contains("all") || required.Contains(item.Group)))
            .Select(item => $"{item.Title} is required but {item.Status}: {item.Reason}")
    ];

    /// <summary>Checks the extraction, generates, builds and replays the modules, then audits the theorems.</summary>
    BindingReport RunBindingAudit(string extraction, string? assemblyPath, string selectedSha256,
        Dictionary<string, string> referenceSha256, string output)
    {
        // The check only fails fast; the evidence is the digest theorem and the replayed modules.
        string[] assembly = assemblyPath is null ? [] : ["--assembly-path", assemblyPath];
        RunExtractor(["dotnet", ExtractorPath, "check", extraction, .. assembly]);

        var plan = BindingPlanOf(extraction, assemblyPath, selectedSha256, referenceSha256, output);
        BindingSession();
        WriteBindingModules(plan);
        return CheckBindingModules(plan);
    }

    /// <summary>The files an extraction pinned, each with its stated or else its recorded digest.</summary>
    static BindingPlan BindingPlanOf(string extraction, string? assemblyPath, string selectedSha256,
        Dictionary<string, string> referenceSha256, string output)
    {
        var identity = ExtractionIdentity.Read(extraction);
        var root = identity.Root;
        var selectedPath = assemblyPath ??
            ExtractionIdentity.Resolve(extraction, root.GetProperty("assemblyPath").GetString()!);
        var recorded = root.TryGetProperty("references", out var references)
            ? references.EnumerateArray().ToArray() : [];
        // Names clash before any file is read, so the message names the clash and not a digest of one of the files.
        var names = recorded.Select(item => item.GetProperty("assemblyIdentity").GetString()!.Split(',')[0])
            .Append(root.GetProperty("assemblyIdentity").GetString()!.Split(',')[0]);
        if (names.GroupBy(name => name).FirstOrDefault(group => group.Count() > 1) is { } clash)
            throw new ArgumentException($"Two pinned assemblies are named {clash.Key}; their report items and " +
                "--reference-sha256 names would collide.");
        List<BindingImagePin> pins =
            [Pin(root.GetProperty("assemblyIdentity").GetString()!, selectedPath, selectedSha256, "stated")];
        foreach (var reference in recorded)
        {
            var name = reference.GetProperty("assemblyIdentity").GetString()!;
            var stated = referenceSha256.GetValueOrDefault(name.Split(',')[0]);
            var path = ExtractionIdentity.Resolve(extraction, reference.GetProperty("path").GetString()!);
            pins.Add(Pin(name, path, stated ?? reference.GetProperty("sha256").GetString()!,
                stated is null ? "recorded, not stated" : "stated"));
        }
        if (referenceSha256.Keys.FirstOrDefault(name => pins.All(pin => pin.Name != name)) is { } unpinned)
            throw new ArgumentException($"--reference-sha256 names {unpinned}, which the extraction did not pin.");
        return new(extraction, output, root.GetProperty("generatedSha256").GetString()!, identity.Sha256, [.. pins],
            root.GetProperty("methods").GetArrayLength());

        static BindingImagePin Pin(string identity, string path, string digest, string source)
        {
            var bytes = File.ReadAllBytes(path);
            var actual = BindingImage.Digest(bytes);
            if (actual != digest)
                throw new InvalidDataException($"SHA-256 of {path} is {actual}; " +
                    $"the {(source == "stated" ? "stated" : "recorded")} digest is {digest}.");
            return new(identity, path, digest, source, bytes);
        }
    }

    string? bindingSession, bindingSourcesKey, bindingLeanVersion;
    BindingLibraryPreparation? bindingPreparation;

    /// <summary>The exact library and session artifacts certified for the strict binding sources.</summary>
    sealed record BindingLibraryPreparation(string Library, string LibraryKey, string Toolchain,
        SortedDictionary<string, string> BaseArtifacts, SortedDictionary<string, string> SessionArtifacts);

    /// <summary>
    /// The session package with the strict binding library built on the certified library and kernel-replayed, once
    /// per process. The library's sources come from the checkout or, in the tool, from its bundled framework files.
    /// </summary>
    string BindingSession()
    {
        var session = Library(Inputs(At("CIL.lean")));
        PrepareBindingLibrary(session);
        return session;
    }

    /// <summary>Builds and replays StrictBinding in the caller's selected, certified library session.</summary>
    void PrepareBindingLibrary(string package)
    {
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        if (session is null || library is null || libraryKey is null || certifiedModules is null ||
            !string.Equals(Path.GetFullPath(package), Path.GetFullPath(session), comparison))
            throw new InvalidOperationException("StrictBinding requires the selected certified library session");
        RequireUnchangedLibrary();
        var beforeBase = ModuleArtifacts(library);
        var beforeSession = ModuleArtifacts(session);
        var current = new SortedDictionary<string, string>(beforeBase, StringComparer.Ordinal);
        foreach (var (name, hash) in beforeSession) current[name] = hash;
        if (!Same(current, certifiedModules) ||
            baseModules!.Any(pair => !beforeBase.TryGetValue(pair.Key, out var hash) || hash != pair.Value))
            throw new InvalidOperationException("The certified library changed before preparing StrictBinding");
        var toolchain = BindingToolchainKey(session);
        if (bindingPreparation is { } prepared)
        {
            if (bindingSession != session || prepared.Library != library || prepared.LibraryKey != libraryKey ||
                prepared.Toolchain != toolchain || bindingSourcesKey != BindingSourcesKey(session) ||
                !Same(prepared.BaseArtifacts, beforeBase) || !Same(prepared.SessionArtifacts, beforeSession))
                throw new InvalidOperationException("The prepared StrictBinding library changed");
            return;
        }
        CopyBindingSources(session);
        var sourcesKey = BindingSourcesKey(session);
        var leanVersion = Run([LeanExecutable, "--version"]).Trim();
        Run(["lake", "build", "StrictBinding"], session, progress: "Building the strict binding library");
        var afterBase = ModuleArtifacts(library);
        var afterSession = ModuleArtifacts(session);
        current = new(afterBase, StringComparer.Ordinal);
        foreach (var (name, hash) in afterSession) current[name] = hash;
        if (!Same(beforeBase, afterBase) ||
            !BindingArtifactsPreserved(beforeSession, afterSession) ||
            !BindingArtifactsPreserved(certifiedModules, current))
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
        bindingPreparation = new(library, libraryKey, toolchain, afterBase, afterSession);
    }

    /// <summary>Existing module families retain exactly their artifacts; additional families are permitted.</summary>
    static bool BindingArtifactsPreserved(SortedDictionary<string, string> before,
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

    /// <summary>Writes a plan's generated modules below its output directory, replacing an earlier audit's.</summary>
    void WriteBindingModules(BindingPlan plan)
    {
        var inside = Path.GetRelativePath(plan.Extraction, plan.Output);
        if (!Path.IsPathRooted(inside) && inside != ".." && !inside.StartsWith(".." + Path.DirectorySeparatorChar))
            throw new InvalidOperationException("--output must not be the extraction directory or below it.");
        if (Directory.Exists(plan.Output))
        {
            // Only a directory that holds nothing but what an audit writes is replaced.
            var entries = Directory.EnumerateFileSystemEntries(plan.Output).Select(Path.GetFileName).ToArray();
            if (entries.Length > 0 && (!entries.Contains(BindingReportFile) || entries.Any(entry =>
                    entry is not (BindingReportFile or "BindingAudit") &&
                    !(entry!.StartsWith("Extracted.", StringComparison.Ordinal)))))
                throw new InvalidOperationException(
                    $"{plan.Output} exists and is not an earlier binding audit; " +
                    "remove it or choose another --output.");
            DeleteTree(plan.Output);
        }
        var modules = Path.Combine(plan.Output, "BindingAudit");
        Directory.CreateDirectory(modules);
        File.WriteAllText(Path.Combine(plan.Output, BindingReportFile), "{}\n");
        // `check` matched this module with the assembly; the hash ties the copy to the extraction's record.
        var extracted = Path.Combine(plan.Output, "Extracted.lean");
        File.Copy(Path.Combine(plan.Extraction, "Extracted.lean"), extracted);
        if (Sha(extracted) != plan.GeneratedSha256 ||
            Sha(Path.Combine(plan.Extraction, "identity.json")) != plan.IdentitySha256)
            throw new InvalidOperationException("The extraction changed while the binding audit read it");
        WriteBindingSources(plan);
    }

    /// <summary>Writes one image module per digest and retains every pinned identity association.</summary>
    static void WriteBindingSources(BindingPlan plan)
    {
        foreach (var image in plan.Images.DistinctBy(image => image.Sha256))
            File.WriteAllText(ModuleSource(plan.Output, image.Module), ImageModuleSource(image));
        File.WriteAllText(ModuleSource(plan.Output, ImagesModule), ImagesModuleSource(plan));
        File.WriteAllText(ModuleSource(plan.Output, BodiesModule), BodiesModuleSource(plan.Methods,
            plan.PageSize ?? BindingPageSize(plan.Methods)));
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
        var imports = string.Concat(plan.Images.DistinctBy(image => image.Sha256)
            .Select(image => $"import {image.Module}\n"));
        var entries = string.Join(",\n   ", plan.Images.Select(image =>
            $"{{ identity := {LeanString(image.Identity)}, image := {image.Module}.image }}"));
        return $"""
            import StrictBinding.Image
            {imports}
            /-!
            # The pinned images

            Each assembly the extraction read, under the identity the extraction records for it, with the
            image constant whose SHA-256 digest its own module proves.
            -/

            namespace BindingAudit

            /-- The pinned images the audit reads. -/
            def images : List StrictBinding.PinnedImage :=
              [{entries}]

            /-- The identities and image constants of `images`, as the driver states them. -/
            theorem images_eq : images =
              [{entries}] := rfl

            end BindingAudit
            """;
    }

    /// <summary>
    /// The bodies module: one theorem per page of methods, each its own kernel evaluation, and `bodies`, which the
    /// kernel-checked composition `claimsHold_of_pages` derives for the whole evidence. The composition
    /// needs the pages to number enough to cover the evidence and to be the first pages in order, so no method is
    /// skipped, repeated or reordered.
    /// </summary>
    static string BodiesModuleSource(int methods, int size)
    {
        var pages = BindingPageCount(methods, size);
        var lemmas = string.Concat(Enumerable.Range(0, pages).Select(page => $$"""
            set_option debug.skipKernelTC true in
            /-- The bodies of page {{page}} of the claims are in the pinned images. -/
            theorem page{{page}} : StrictBinding.ClaimsHold StrictBinding.bodyClaimBound images
                (StrictBinding.claimPage (StrictBinding.bodyClaims Extracted.methodEvidence) {{size}} {{page}}) := by
              decide +kernel


            """));
        var chain = string.Concat(Enumerable.Range(0, pages).Reverse().Select(page => $"(.succ page{page} "));
        return $$"""
            import BindingAudit.Images
            import Extracted
            import StrictBinding.Evidence

            /-!
            # Method bodies in the pinned images

            Every method body of the extraction's evidence is the bytes at the place the MethodDef row of its
            token gives in the pinned image of its assembly, proved page by page. The preparation and
            each page lemma are kernel-checked when this module is replayed.
            -/

            namespace BindingAudit

            set_option debug.skipKernelTC true in
            /-- The pinned images decode and spell the identities they are pinned under. -/
            theorem prepared : StrictBinding.ok (StrictBinding.prepare images) = true := by decide +kernel

            {{lemmas}}/-- The method bodies of `Extracted.methodEvidence` are in the pinned images. -/
            theorem bodies : StrictBinding.BodiesBound images Extracted.methodEvidence :=
              StrictBinding.claimsHold_of_pages (size := {{size}}) (count := {{pages}}) prepared
                (by decide +kernel) {{chain}}.zero{{new string(')', pages)}}

            end BindingAudit
            """;
    }

    /// <summary>A theorem the audit expects in a module, with the type the driver derives from the plan.</summary>
    sealed record BindingRequest(string Module, AuditRequest Audit);

    /// <summary>The audited theorems with expected types built from the plan, never from module text.</summary>
    static BindingRequest[] BindingRequests(BindingPlan plan)
    {
        static object Const(string name, params int[] levels) =>
            levels.Length == 0 ? new { @const = name } : new { @const = name, levels };
        static object App(params object[] parts) => new { app = parts };
        static JsonElement Nat(string hex) => JsonDocument.Parse("{\"nat\":" +
            BigInteger.Parse("0" + hex, NumberStyles.HexNumber, CultureInfo.InvariantCulture) + "}").RootElement;
        var pinned = Const("StrictBinding.PinnedImage");
        var images = plan.Images.Reverse().Aggregate(App(Const("List.nil", 0), pinned), (rest, image) =>
            App(Const("List.cons", 0), pinned,
                App(Const("StrictBinding.PinnedImage.mk"), new { str = image.Identity },
                    Const(image.Module + ".image")), rest));
        var imagesEq = App(Const("Eq", 1), App(Const("List", 0), pinned), Const("BindingAudit.images"), images);
        var bodies = App(Const("StrictBinding.BodiesBound"), Const("BindingAudit.images"),
            Const("Extracted.methodEvidence"));
        return
        [
            new("Extracted", ExtractionCertificate("Extracted.translation_valid")),
            new(ImagesModule, new("BindingAudit.images_eq", imagesEq, ApprovedAxioms)),
            new(BodiesModule, new("BindingAudit.bodies", bodies, ApprovedAxioms)),
            .. plan.Images.DistinctBy(image => image.Sha256).Select(image => new BindingRequest(image.Module,
                new(image.Theorem,
                App(Const("StrictBinding.DigestIs"), Const(image.Module + ".image"), Nat(image.Sha256)),
                ApprovedAxioms)))
        ];
    }

    /// <summary>
    /// Builds, replays and audits the modules in a plan's output directory, whatever text they hold. A fact is
    /// reconfirmed only when its module built and replayed and its theorem has the expected type and approved
    /// axioms in the same audit as the extraction's certificate; otherwise it is failed and names the stage.
    /// </summary>
    BindingReport CheckBindingModules(BindingPlan plan)
    {
        var session = BindingSession();
        var leanPath = SessionLeanPath(session) + Path.PathSeparator + plan.Output;
        foreach (var stale in Directory.EnumerateFiles(plan.Output, "*.olean*", SearchOption.AllDirectories))
            File.Delete(stale);
        var requests = BindingRequests(plan);
        var failures = BuildBindingModules(plan, leanPath);
        string[] built = ["Extracted", .. requests.Skip(1).Select(request => request.Module)
            .Where(module => !failures.ContainsKey(module))];
        var before = OleanHashes(plan.Output, session);
        ReplayBindingModules(built, leanPath, failures);
        string[] replayed = [.. built.Where(module => !failures.ContainsKey(module))];
        BindingRequest[] audited = [.. requests.Where(request => replayed.Contains(request.Module))];
        var result = AuditOleans(leanPath, replayed, [.. audited.Select(request => request.Audit)]);
        foreach (var module in replayed)
            RequireAuditedModule(result, module, Path.ChangeExtension(ModuleSource(plan.Output, module), ".olean"));
        if (!Same(before, OleanHashes(plan.Output, session)) ||
            Sha(Path.Combine(plan.Output, "Extracted.lean")) != plan.GeneratedSha256 ||
            Sha(Path.Combine(plan.Extraction, "identity.json")) != plan.IdentitySha256 ||
            Sha(Path.Combine(plan.Extraction, "Extracted.lean")) != plan.GeneratedSha256)
            throw new InvalidOperationException("Compiled artifacts or extraction files changed during the audit");
        var theorems = audited.Zip(result.theorems).ToDictionary(pair => pair.First.Audit.name, pair => pair.Second);
        var items = BindingVerdicts(plan, failures, theorems);
        if (items.Any(item => item.Id == BodiesGroup && item.Status == Failed) && !failures.ContainsKey(ImagesModule))
            items = [.. items.Select(item => item.Id == BodiesGroup
                ? item with { Reason = item.Reason + Diagnose(plan, leanPath) } : item)];
        string[] axioms = [.. result.theorems.Where(theorem => theorem.error is null)
            .SelectMany(theorem => theorem.axioms ?? []).Distinct().Order(StringComparer.Ordinal)];
        return new(plan.Extraction, plan.GeneratedSha256, plan.Images, items, axioms, bindingSourcesKey!,
            File.ReadAllText(At("lean-toolchain")).Trim(), bindingLeanVersion!);
    }

    /// <summary>
    /// Builds each module and returns the failures by module. The extraction's own module must build, or nothing it
    /// says can be audited; a module that needs a failed one fails with it.
    /// </summary>
    Dictionary<string, string> BuildBindingModules(BindingPlan plan, string leanPath, bool buildExtracted = true)
    {
        string? Build(string module)
        {
            var source = ModuleSource(plan.Output, module);
            var olean = Path.ChangeExtension(source, ".olean");
            var result = Execute([LeanExecutable, "--root=" + plan.Output, "-o", olean, source], leanPath: leanPath,
                progress: "Checking " + module, environment: LeanEnvironment);
            return result.Code == 0 ? null : BindingDiagnostic(result.Output);
        }
        if (buildExtracted && Build("Extracted") is { } extractedError)
            throw new InvalidOperationException("The extraction's Lean module did not build: " + extractedError);
        Dictionary<string, string> failures = new(StringComparer.Ordinal);
        foreach (var image in plan.Images.DistinctBy(image => image.Sha256))
            if (Build(image.Module) is { } error) failures[image.Module] = "build: " + error;
        if (plan.Images.Any(image => failures.ContainsKey(image.Module)))
            failures[ImagesModule] = "build: an image module did not build";
        else if (Build(ImagesModule) is { } imagesError) failures[ImagesModule] = "build: " + imagesError;
        if (failures.ContainsKey(ImagesModule)) failures[BodiesModule] = "build: " + ImagesModule + " did not build";
        else if (Build(BodiesModule) is { } bodiesError) failures[BodiesModule] = "build: " + bodiesError;
        return failures;
    }

    /// <summary>Kernel-replays each module alone, so a rejected one is attributed to its own fact.</summary>
    void ReplayBindingModules(string[] modules, string leanPath, Dictionary<string, string> failures)
    {
        foreach (var module in modules)
        {
            try { ReplayCheckedModules([module], leanPath, "Kernel replay of " + module); }
            catch (InvalidOperationException error)
            {
                failures[module] = "replay: " + BindingDiagnostic(error.Message);
            }
        }
        if (failures.TryGetValue("Extracted", out var replayError))
            throw new InvalidOperationException(
                "The extraction's Lean module was not kernel-replayed: " + replayError);
    }

    /// <summary>
    /// The report items from what built, replayed and audited. The extraction's certificate must have passed. A digest
    /// is reconfirmed when the caller stated it, and only matches the extraction's pinned digest when it was recorded.
    /// </summary>
    static BindingItem[] BindingVerdicts(BindingPlan plan, Dictionary<string, string> failures,
        Dictionary<string, AuditedTheorem> theorems)
    {
        string? Problem(string module, string theorem) =>
            failures.TryGetValue(module, out var failure) ? failure
            : !theorems.TryGetValue(theorem, out var found) ? "audit: " + theorem + " was not audited"
            : found.error is not null ? "audit: " + BindingDiagnostic(found.error)
            : found.axioms is null || found.axioms.Any(axiom => !ApprovedAxioms.Contains(axiom))
                ? "audit: unapproved axioms"
            : null;
        if (Problem("Extracted", "Extracted.translation_valid") is { } certificate)
            throw new InvalidOperationException("The extraction certificate did not pass the audit: " + certificate);
        List<BindingItem> items =
            [.. plan.Images.Select(image => DigestVerdict(image, Problem(image.Module, image.Theorem)))];
        var unconfirmed = items.Where(item => item.Status is Failed).Select(item => item.Title).ToArray();
        var bodiesProblem = Problem(BodiesModule, "BindingAudit.bodies");
        if (bodiesProblem is null && Problem(ImagesModule, "BindingAudit.images_eq") is { } identities)
            bodiesProblem = "the identities of the pinned images are not confirmed: " + identities;
        if (bodiesProblem is null && unconfirmed.Length > 0)
            bodiesProblem = "a digest is not reconfirmed: " + unconfirmed[0];
        const string bodiesTitle = "PE container and method body locations";
        var recordedOnly = items.FirstOrDefault(item => item.Status == Matched);
        items.Add(bodiesProblem is not null
                ? new(BodiesGroup, bodiesTitle, Failed, "BindingAudit.bodies", bodiesProblem)
            : recordedOnly is not null ? new(BodiesGroup, bodiesTitle, Matched, "BindingAudit.bodies",
                $"the bodies are in an image with the digest the extraction recorded ({recordedOnly.Title}); " +
                "state that digest with --reference-sha256 to reconfirm them")
            : new(BodiesGroup, bodiesTitle, Reconfirmed, "BindingAudit.bodies"));
        items.AddRange(UncoveredBindingFacts.Select(fact =>
            new BindingItem(fact.Id, fact.Title, NotCovered, Reason: fact.Reason)));
        return [.. items];
    }

    static BindingItem DigestVerdict(BindingImagePin image, string? problem)
    {
        var id = $"{DigestGroup}:{image.Name}";
        var title = $"SHA-256 digest of {image.Identity}";
        if (problem is not null) return new(id, title, Failed, image.Theorem, problem);
        return image.Source == "stated" ? new(id, title, Reconfirmed, image.Theorem)
            : new(id, title, Matched, image.Theorem, "the image has the digest the extraction recorded; " +
                "state it with --reference-sha256 to reconfirm it against your own");
    }

    /// <summary>The hash of the StrictBinding sources, which define what the audited theorems mean.</summary>
    static string BindingSourcesKey(string root) => ContentKey(string.Join("\n", Directory
        .EnumerateFiles(Path.Combine(root, "StrictBinding"), "*.lean", SearchOption.AllDirectories)
        .Append(Path.Combine(root, "StrictBinding.lean"))
        .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/') + "=" + Sha(path))
        .Order(StringComparer.Ordinal)));

    /// <summary>
    /// Evaluates the bodies check on its own and prints the error it finds. This is a diagnosis for a person to
    /// read, run by the interpreter and outside the kernel, so it is never evidence for a status.
    /// </summary>
    string Diagnose(BindingPlan plan, string leanPath)
    {
        var path = ModuleSource(plan.Output, "BindingAudit.Diagnose");
        File.WriteAllText(path, """
            import BindingAudit.Images
            import Extracted
            import StrictBinding.Evidence

            #eval match StrictBinding.checkAll StrictBinding.bodyClaimBound BindingAudit.images
                (StrictBinding.bodyClaims Extracted.methodEvidence) with
              | .ok _ => "the bodies check found no error"
              | .error error => reprStr error
            """);
        var result = Execute([LeanExecutable, "--root=" + plan.Output, path], leanPath: leanPath,
            environment: LeanEnvironment);
        return " (diagnostic, not evidence: " + BindingDiagnostic(result.Output) + ")";
    }

    /// <summary>The report as the lines `leancil audit-binding` prints.</summary>
    static string BindingText(BindingReport report, bool valid)
    {
        var text = new StringBuilder(valid ? "Valid: strict binding audit of " : "Strict binding audit of ")
            .Append(report.Extraction).Append('\n');
        text.Append("  Certificate: Extracted.translation_valid audited with the binding theorems; " +
            $"generatedSha256 {report.GeneratedSha256}\n");
        foreach (var image in report.Images)
            text.Append($"  Image {image.Identity}: SHA-256 {image.Sha256} {image.Source}\n");
        foreach (var item in report.Items)
        {
            var detail = item.Status switch
            {
                Reconfirmed => item.Theorem,
                Matched => item.Theorem + "; " + item.Reason,
                _ => item.Reason
            };
            text.Append($"  {item.Title}: {item.Status} ({detail})\n");
        }
        var axioms = report.Axioms.Length == 0 ? "none" : string.Join(", ", report.Axioms);
        text.Append($"  Axioms: {axioms}\n");
        return text.Append($"  Statements defined by: StrictBinding sources {report.SourcesKey}, " +
            $"Lean {report.Toolchain} (ran {report.LeanVersion})").ToString();
    }

    /// <summary>The report as JSON: the extraction, its generated hash, its images and its items.</summary>
    static string BindingJson(BindingReport report) => JsonSerializer.Serialize(new
    {
        extraction = report.Extraction,
        generatedSha256 = report.GeneratedSha256,
        images = report.Images.Select(image =>
            new { identity = image.Identity, sha256 = image.Sha256, source = image.Source, check = "kernel" }),
        items = report.Items.Select(item =>
            new { id = item.Id, status = item.Status, theorem = item.Theorem, reason = item.Reason }),
        axioms = report.Axioms,
        strictBindingSourcesSha256 = report.SourcesKey,
        leanToolchain = report.Toolchain,
        leanVersion = report.LeanVersion
    }, new JsonSerializerOptions { WriteIndented = true });

    /// <summary>The first error of a Lean message, flattened and shortened for a report line.</summary>
    static string BindingDiagnostic(string output)
    {
        var lines = output.Split('\n').Select(line => line.Trim()).Where(line => line.Length > 0).ToArray();
        var first = Math.Max(0,
            Array.FindIndex(lines, line => line.Contains("error", StringComparison.OrdinalIgnoreCase)));
        var text = string.Join(" ", lines.Skip(first).Take(3));
        return text.Length > 300 ? text[..300] + "..." : text;
    }
}
