using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Nethermind.LeanCIL;

partial class Program
{
    // Id names one independently checked export; Dependencies are the ids filling its own import slots in order.
    sealed record FullLibrary(int Id, string Module, string ExpectedModule, string BundleDigest,
        string Contract, string Kind, string TransferSource, string GeneratedSource, StaticIdentityRecord[] Statics,
        string AssemblyIdentity, int[] Dependencies);
    sealed record FullSelection(JsonElement Binding, string Sidecar, string SidecarSha256, string Implementation,
        string ImplementationSha256, ContractInterface Contract, string Bundle, string Digest,
        ContractBundleManifest Inventory);
    // Caller slot j has id j; dependency exports reached through libraries take the following ids.
    sealed record FullImport(FullSelection Selection, ContractExport Export, ContractCertification Certification,
        int Id);
    sealed record FullSlot(FullImport Import, string Author, string Artifact, string Generated, string GeneratedSha256,
        ContractExportRequest Request, StaticIdentityRecord[] Statics, JsonElement[] Imports);

    const string FullCompositionModule = "LeanCILFullComposition";
    const string FullCompositionTheorem = FullCompositionModule + ".certified";
    const string FullLibraryPrefix = "LeanCILFullLibrary";
    const string FullExpectedPrefix = "LeanCILFullExpected";
    const string MissingFullBundle = "Full verification source bundle is missing: ";
    const string NoFullImports = "Full verification requires at least one contract import.";
    const string FullDeploymentObligation =
        "The composed CIL theorem checks this exact implementation and profile; " +
        "DLL decoding and runtime/model correspondence remain trusted, " +
        "and an untrusted source bundle must be checked in an isolated environment.";

    static StringComparer PathComparer =>
        OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;

    static int BindingSlot(JsonElement binding) => binding.GetProperty("slot").GetInt32();

    static string BundleName(string path) => Path.GetFileName(Path.TrimEndingDirectorySeparator(path));

    // The sidecar names a content-addressed bundle; an override may relocate it but not change its identity.
    static FullSelection SelectFullBundle(string output, JsonElement binding,
        IReadOnlyDictionary<string, string> overrides, ISet<string> used)
    {
        string sidecar = ExtractionIdentity.Resolve(output, binding.GetProperty("sidecarPath").GetString()!);
        string implementation =
            ExtractionIdentity.Resolve(output, binding.GetProperty("implementationPath").GetString()!);
        byte[] sidecarBytes = File.ReadAllBytes(sidecar);
        string sidecarSha256 = ContractInterface.Hash(sidecarBytes);
        string implementationSha256 = Sha(implementation);
        if (sidecarSha256 != binding.GetProperty("sidecarSha256").GetString() ||
            implementationSha256 != binding.GetProperty("implementationSha256").GetString())
            throw new InvalidDataException("Full-verification imported implementation or sidecar changed: " +
                binding.GetProperty("identity").GetString());
        ContractInterface contract = ContractInterface.Read(sidecarBytes);
        (string bundle, string digest, ContractBundleManifest inventory) =
            LocateFullBundle(contract, sidecar, overrides, used);
        return new(binding, sidecar, sidecarSha256, implementation, implementationSha256, contract, bundle, digest,
            inventory);
    }

    static (string Bundle, string Digest, ContractBundleManifest Inventory) LocateFullBundle(
        ContractInterface contract, string sidecar, IReadOnlyDictionary<string, string> overrides, ISet<string> used)
    {
        string locator = contract.FullVerificationLocator
            ?? throw new InvalidDataException(MissingFullBundle + contract.AssemblyIdentity);
        string digest = BundleName(locator);
        if (!ContractInterface.Digest(digest))
            throw new InvalidDataException("Full-verification locator must name a content-addressed source bundle.");
        string simple = AssemblyNameReference.Parse(contract.AssemblyIdentity).Name;
        if (overrides.TryGetValue(simple, out string? replacement)) used.Add(simple);
        string bundle = replacement is not null
            ? Path.GetFullPath(replacement)
            : Path.GetFullPath(locator, Path.GetDirectoryName(sidecar)!);
        if (!Directory.Exists(bundle)) throw new InvalidDataException(MissingFullBundle + bundle);
        if (BundleName(bundle) != digest)
            throw new InvalidDataException("Full-verification source bundle override has the wrong content identity.");
        return (bundle, digest, ContractSourceBundle.Validate(bundle, digest));
    }

    // The graph nodes the caller's bindings reach through declared dependencies; other supplied libraries are unused.
    static IEnumerable<JsonElement> ReachableGraph(ExtractionIdentity extraction)
    {
        Dictionary<string, JsonElement> nodes = extraction.Graph.ToDictionary(
            node => node.GetProperty("assemblyIdentity").GetString()!, StringComparer.Ordinal);
        Queue<string> pending = new(extraction.Imports.Select(binding => ContractInterface.Read(File.ReadAllBytes(
            ExtractionIdentity.Resolve(extraction.Output, binding.GetProperty("sidecarPath").GetString()!)))
            .AssemblyIdentity));
        HashSet<string> reached = new(StringComparer.Ordinal);
        while (pending.TryDequeue(out string? assembly))
        {
            if (!reached.Add(assembly)) continue;
            JsonElement node = nodes.TryGetValue(assembly, out JsonElement found) ? found
                : throw new InvalidDataException("Full verification has no unique pinned dependency graph node: " +
                    assembly);
            foreach (JsonElement dependency in node.GetProperty("dependencies").EnumerateArray())
                pending.Enqueue(dependency.GetProperty("assemblyIdentity").GetString()!);
            yield return node;
        }
    }

    // Every reached graph node is located and validated before any build; regeneration still binds each one.
    static void PreflightFullNode(string output, JsonElement node, IReadOnlyDictionary<string, string> overrides,
        ISet<string> used)
    {
        string assemblyIdentity = node.GetProperty("assemblyIdentity").GetString()!;
        string sidecar = ExtractionIdentity.Resolve(output, node.GetProperty("sidecarPath").GetString()!);
        string implementation =
            ExtractionIdentity.Resolve(output, node.GetProperty("implementationPath").GetString()!);
        ContractInterface contract = ContractInterface.Read(File.ReadAllBytes(sidecar));
        if (contract.InterfaceDigest != node.GetProperty("interfaceDigest").GetString() ||
            Sha(implementation) != node.GetProperty("implementationSha256").GetString())
            throw new InvalidDataException(
                "Full-verification imported implementation or sidecar changed: " + assemblyIdentity);
        LocateFullBundle(contract, sidecar, overrides, used);
    }

    static void RequireUsedOverrides(IReadOnlyDictionary<string, string> overrides, ISet<string> used)
    {
        if (overrides.Keys.Any(name => !used.Contains(name)))
            throw new InvalidDataException(
                "Unused --full-artifact override; supply the imported assembly simple name.");
    }

    void PreflightFullImports(string output, IReadOnlyDictionary<string, string> overrides)
    {
        ExtractionIdentity extraction = ExtractionIdentity.Read(output);
        if (extraction.Imports.Length == 0) throw new InvalidDataException(NoFullImports);
        HashSet<string> used = new(StringComparer.Ordinal);
        foreach (JsonElement binding in extraction.Imports)
            RequireAgreedStaticRecords(binding, SelectFullBundle(output, binding, overrides, used));
        foreach (JsonElement node in ReachableGraph(extraction)) PreflightFullNode(output, node, overrides, used);
        RequireUsedOverrides(overrides, used);
    }

    // The caller binding, certification and bundled extraction must name one static set before any build;
    // the fresh extraction is compared with all three after regeneration.
    static void RequireAgreedStaticRecords(JsonElement binding, FullSelection selection)
    {
        string identity = binding.GetProperty("identity").GetString()!;
        string profile = binding.GetProperty("profile").GetString()!;
        ContractCertification[] certifications = selection.Contract.Certifications
            .Where(item => item.Identity == identity && item.Profile == profile).ToArray();
        int[] matches = selection.Inventory.Exports.EnumerateArray().Select((record, index) => (record, index))
            .Where(item => item.record.GetProperty("identity").GetString() == identity &&
                item.record.GetProperty("profile").GetString() == profile)
            .Select(item => item.index).ToArray();
        if (certifications.Length != 1 || matches.Length != 1)
            throw new InvalidDataException("Full source bundle has no unique selected export/profile.");
        JsonElement bundled = JsonSerializer.Deserialize<JsonElement>(
            File.ReadAllText(Within(selection.Bundle, "exports/" + matches[0] + "/identity.json")));
        StaticIdentityRecord[] pinned = StaticIdentitySet(binding);
        bool agreed = pinned.SequenceEqual(StaticIdentitySet(bundled)) && pinned.SequenceEqual(
            certifications[0].StaticIdentities.OrderBy(item => item.Identity, StringComparer.Ordinal));
        if (!agreed)
            throw new InvalidDataException("Full-verification static identity records disagree: " + identity);
    }

    // Search roots without the toolchain, which a supported run keeps read-only instead of rehashing.
    string WithoutToolchain(string leanPath)
    {
        string toolchain = Path.GetFullPath(Toolchain);
        return string.Join(Path.PathSeparator, leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Where(root => !Inside(toolchain, Path.GetFullPath(root))));
    }

    static bool Inside(string root, string path)
    {
        string relative = Path.GetRelativePath(root, path);
        bool escapes = relative == ".." ||
            relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal) ||
            Path.IsPathRooted(relative);
        return relative == "." || !escapes;
    }

    // The caller's roots resolved against its session, then the toolchain library, each root once.
    string CallerLeanPath(string leanPath, string session) => string.Join(Path.PathSeparator,
        leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(path => Path.GetFullPath(path, session)).Append(Path.Combine(Toolchain, "lib/lean"))
            .Distinct(PathComparer));

    FullImportResult VerifyFullImports(string output, string callerSession, string callerModule, string callerTheorem,
        string callerLeanPath, IReadOnlyDictionary<string, string> overrides)
    {
        string originalLeanPath = CallerLeanPath(callerLeanPath, callerSession);
        string callerRoots = WithoutToolchain(originalLeanPath);
        SortedDictionary<string, string> acceptedCaller = FullModuleArtifacts(callerRoots);
        SortedDictionary<string, string> originalModules = FullModulePaths(originalLeanPath);
        CheckFullResolution(callerSession, originalLeanPath, originalModules);
        JsonElement[] bindings = ExtractionIdentity.Read(output).Imports.OrderBy(BindingSlot).ToArray();
        if (bindings.Length == 0) throw new InvalidDataException(NoFullImports);
        for (int index = 0; index < bindings.Length; index++)
            if (BindingSlot(bindings[index]) != index)
                throw new InvalidDataException("Full verification requires contiguous unique import slots.");
        // Outside every search root, so no staged or generated file can shadow a checked module.
        string workspace = Path.Combine(Path.GetTempPath(), "leancil-full-" + Guid.NewGuid().ToString("N"));
        if (originalLeanPath.Split(Path.PathSeparator).Any(root => Inside(Path.GetFullPath(root), workspace)))
            throw new InvalidDataException("Full-verification workspace lies inside a Lean search root: " + workspace);
        Directory.CreateDirectory(workspace);
        try
        {
            return VerifyFullImports(output, callerSession, callerModule, callerTheorem, overrides, bindings,
                originalLeanPath, callerRoots, acceptedCaller, originalModules, workspace);
        }
        finally
        {
            try { Directory.Delete(workspace, true); }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException)
            {
                Console.Error.WriteLine("warning: full-verification workspace cleanup failed: " + error.Message);
            }
        }
    }

    FullImportResult VerifyFullImports(string output, string callerSession, string callerModule, string callerTheorem,
        IReadOnlyDictionary<string, string> overrides, JsonElement[] bindings, string originalLeanPath,
        string callerRoots, SortedDictionary<string, string> acceptedCaller,
        SortedDictionary<string, string> originalModules, string workspace)
    {
        string staging = Path.Combine(workspace, "staging");
        Directory.CreateDirectory(staging);
        SortedDictionary<string, string> original = new(StringComparer.Ordinal);
        Dictionary<string, string> bundles = new(StringComparer.Ordinal);
        void RecheckOriginal()
        {
            foreach ((string path, string digest) in original)
                if (!File.Exists(path) || Sha(path) != digest)
                    throw new InvalidDataException("Full-verification input changed: " + path);
            foreach ((string directory, string digest) in bundles) ContractSourceBundle.Validate(directory, digest);
        }
        // One snapshot after each run that elaborates producer-derived code.
        // It detects accidental, not hostile, mutation.
        void RequireCallerUnchanged()
        {
            RecheckOriginal();
            RequireFullArtifacts(acceptedCaller);
            RequireFullModuleArtifactSet(callerRoots, acceptedCaller);
            RequireFullModulePaths(originalLeanPath, originalModules);
        }
        foreach (string file in new[] { "identity.json", "Extracted.lean" })
            original[Path.Combine(output, file)] = Sha(Path.Combine(output, file));
        JsonElement[] graph = ExtractionIdentity.Read(output).Graph;
        HashSet<string> usedOverrides = new(StringComparer.Ordinal);
        Dictionary<string, int> unitIds = new(StringComparer.Ordinal);
        List<FullImport> pending = [];
        foreach (JsonElement binding in bindings)
        {
            FullImport import = BindFullImport(output, output, binding, overrides, usedOverrides, original, bundles,
                graph, BindingSlot(binding));
            unitIds.TryAdd(FullUnitKey(import), import.Id);
            pending.Add(import);
        }
        int nextId = bindings.Length;
        List<FullLibrary> libraries = [];
        int bundleIndex = 0;
        // Each round checks the exports the previous round's libraries import; a shared export is checked once.
        while (pending.Count != 0)
        {
            List<FullImport> discovered = [];
            int DependencyId(string importer, JsonElement binding)
            {
                FullImport import = BindFullImport(output, importer, binding, overrides, usedOverrides, original,
                    bundles, graph, nextId);
                if (unitIds.TryGetValue(FullUnitKey(import), out int existing)) return existing;
                unitIds.Add(FullUnitKey(import), nextId);
                discovered.Add(import);
                return nextId++;
            }
            // One library build per bundle in a round, however many of its methods are imported.
            foreach (IGrouping<string, FullImport> group in pending.GroupBy(item => item.Selection.Bundle,
                StringComparer.Ordinal))
            {
                int implementations = group
                    .Select(item => (item.Selection.SidecarSha256, item.Selection.ImplementationSha256))
                    .Distinct().Count();
                if (implementations != 1)
                    throw new InvalidDataException(
                        "Full-verification source bundle is shared by different implementations: " + group.Key);
                libraries.AddRange(CheckFullBundle(group.ToArray(), Path.Combine(staging, "bundle-" + bundleIndex++),
                    output, graph, DependencyId));
                RequireCallerUnchanged();
            }
            pending = discovered;
        }
        // Preflight required a bundle for every reachable node, so an override for one is used.
        usedOverrides.UnionWith(ReachableGraph(ExtractionIdentity.Read(output)).Select(node =>
            AssemblyNameReference.Parse(node.GetProperty("assemblyIdentity").GetString()!).Name));
        RequireUsedOverrides(overrides, usedOverrides);
        libraries.Sort((left, right) => left.Id.CompareTo(right.Id));
        // Names a colliding pair before the kernel decides compatibility of the whole linked program.
        StaticIdentity.Validate(StaticIdentitySet(ExtractionIdentity.Read(output).Root)
            .Concat(libraries.SelectMany(library => library.Statics)));
        string compositionDirectory = Path.Combine(workspace, "composition");
        Directory.CreateDirectory(compositionDirectory);
        // First: leanchecker names each olean by the first root containing it.
        string fullLeanPath = compositionDirectory + Path.PathSeparator + originalLeanPath;
        HashSet<string> generatedModules = new(StringComparer.Ordinal);
        SortedDictionary<string, string> generatedArtifacts = new(StringComparer.Ordinal);
        void RecheckResolution()
        {
            RequireCallerUnchanged();
            RequireFullArtifacts(generatedArtifacts);
            SortedDictionary<string, string> generated = FullModulePaths(compositionDirectory);
            foreach ((string name, string path) in generated)
                if (!generatedModules.Contains(name) || originalModules.ContainsKey(name))
                    throw new InvalidDataException(
                        "Unexpected full-verification composition module: " + name + " at " + path);
            foreach (string path in FullModuleArtifactPaths(compositionDirectory))
                if (!generatedModules.Contains(RelativeModuleName(compositionDirectory, path)))
                    throw new InvalidDataException("Unexpected full-verification composition artifact: " + path);
        }
        void Compile(string name, string progress, bool untrusted)
        {
            string olean = Path.Combine(compositionDirectory, name + ".olean");
            string source = Path.Combine(compositionDirectory, name + ".lean");
            // Rechecking expanded kernel terms can cost more than elaborating the original tactic proof.
            Run([LeanExecutable, "-DmaxHeartbeats=2000000", "--root=" + compositionDirectory, "-o", olean, source],
                callerSession, fullLeanPath, progress: progress);
            generatedModules.Add(name);
            if (untrusted) RecheckResolution();
            generatedArtifacts = FullArtifacts(compositionDirectory);
        }
        IEnumerable<string> plannedModules = libraries
            .SelectMany(library => new[] { library.ExpectedModule, library.Module }).Append(FullCompositionModule);
        foreach (string name in plannedModules)
            if (originalModules.ContainsKey(name))
                throw new InvalidDataException(
                    "Full-verification generated module collides with an existing module: " + name);
        string checkerName = OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker";
        string checker = Path.Combine(Toolchain, "bin", checkerName);
        const string RecheckProgress = "Rechecking full-verification program and author kernel terms: ";
        foreach (FullLibrary library in libraries)
        {
            File.WriteAllText(Path.Combine(compositionDirectory, library.ExpectedModule + ".lean"),
                NamespacedExtraction(library.GeneratedSource, library.ExpectedModule));
            Compile(library.ExpectedModule, RecheckProgress + library.ExpectedModule, untrusted: false);
            File.WriteAllText(Path.Combine(compositionDirectory, library.Module + ".lean"),
                "import " + callerModule + "\n" + library.TransferSource);
            Compile(library.Module, RecheckProgress + library.Module, untrusted: true);
            Run([checker, library.ExpectedModule, library.Module], callerSession, fullLeanPath,
                progress: "Independent kernel replay of transferred library declarations");
        }
        string composition = FullCompositionModule;
        File.WriteAllText(Path.Combine(compositionDirectory, composition + ".lean"),
            FullCompositionSource(callerModule, callerTheorem, libraries, bindings.Length));
        CheckFullResolution(compositionDirectory, fullLeanPath, FullModulePaths(fullLeanPath));
        Compile(composition, "Checking concrete library relocation and caller composition", untrusted: true);
        Run([checker, composition], callerSession, fullLeanPath,
            progress: "Independent kernel replay of the composed caller theorem");
        AuditRequest certified =
            new(FullCompositionTheorem, type: FullCompositionType(), axioms: ApprovedAxioms, statement: true);
        AuditedOleans audited = AuditOleans(fullLeanPath, [composition], [certified],
            FullCompositionConstants(callerTheorem, libraries, bindings.Length));
        RequireAuditedModule(audited, composition, Path.Combine(compositionDirectory, composition + ".olean"));
        RecheckResolution();
        RequireAuditedConstants(audited);
        AuditedAxioms(audited.theorems[0]);
        string audit = AuditText(audited.theorems[0]);
        JsonElement identity = JsonSerializer.Deserialize<JsonElement>(
            File.ReadAllText(Path.Combine(output, "identity.json")));
        return new(FullCompositionTheorem, audit, IndependentlyVerifiedImports(identity, libraries),
            IndependentlyVerifiedClosure(identity, libraries));
    }

    // The caller's published imports, each now accepted through its checked bundle instead of its sidecar.
    static PublishedImport[] IndependentlyVerifiedImports(JsonElement identity, List<FullLibrary> libraries) =>
        PublishedImports(identity).Select(import => import with
        {
            acceptedVia = "independently-verified",
            sourceBundleDigest = libraries.Single(library => library.Id == import.slot).BundleDigest,
            deploymentObligation = FullDeploymentObligation
        }).ToArray();

    // Every graph node with a checked export names its bundle; a node no selected export reaches stays unmarked.
    static DeploymentDependency[] IndependentlyVerifiedClosure(JsonElement identity, List<FullLibrary> libraries) =>
        DeploymentDependencies(identity).Select(node =>
        {
            string[] digests = libraries.Where(library => library.AssemblyIdentity == node.assemblyIdentity)
                .Select(library => library.BundleDigest).Distinct(StringComparer.Ordinal).ToArray();
            if (digests.Length > 1)
                throw new InvalidDataException(
                    "Full-verification dependency was checked from different bundles: " + node.assemblyIdentity);
            return digests.Length == 0 ? node : node with
            {
                acceptedVia = "independently-verified",
                sourceBundleDigest = digests.Single()
            };
        }).ToArray();

    static string FullUnitKey(FullImport import) => JsonSerializer.Serialize(new[]
    {
        import.Selection.Contract.AssemblyIdentity, import.Export.Identity, import.Certification.Profile,
        import.Selection.ImplementationSha256
    });

    // The caller's dependency graph names one implementation and interface per assembly.
    static JsonElement FullGraphNode(JsonElement[] graph, string assemblyIdentity)
    {
        JsonElement[] nodes = graph
            .Where(node => node.GetProperty("assemblyIdentity").GetString() == assemblyIdentity).ToArray();
        return nodes.Length == 1 ? nodes[0] : throw new InvalidDataException(
            "Full verification has no unique pinned dependency graph node: " + assemblyIdentity);
    }

    // Pins the binding's sidecar, implementation and bundle identity, and requires the caller's graph node for it.
    static FullImport BindFullImport(string callerOutput, string output, JsonElement binding,
        IReadOnlyDictionary<string, string> overrides, ISet<string> usedOverrides,
        SortedDictionary<string, string> original, Dictionary<string, string> bundles, JsonElement[] graph, int id)
    {
        string identity = binding.GetProperty("identity").GetString()!;
        FullSelection selection = SelectFullBundle(output, binding, overrides, usedOverrides);
        original[selection.Sidecar] = selection.SidecarSha256;
        original[selection.Implementation] = selection.ImplementationSha256;
        ContractInterface contract = selection.Contract;
        if (contract.IsReferenceAssembly)
            throw new InvalidDataException("Full verification requires implementation libraries: " + identity);
        JsonElement node = FullGraphNode(graph, contract.AssemblyIdentity);
        string nodeImplementation = ExtractionIdentity.Resolve(callerOutput,
            node.GetProperty("implementationPath").GetString()!);
        bool selectedNode = node.GetProperty("implementationSha256").GetString() == selection.ImplementationSha256 &&
            node.GetProperty("interfaceDigest").GetString() == contract.InterfaceDigest &&
            PathComparer.Equals(Path.GetFullPath(nodeImplementation), Path.GetFullPath(selection.Implementation));
        if (!selectedNode)
            throw new InvalidDataException(
                "Full-verification dependency differs from the caller's selected graph node: " +
                contract.AssemblyIdentity);
        string profile = binding.GetProperty("profile").GetString()!;
        ContractExport export = contract.Exports.Single(item => item.Identity == identity);
        ContractCertification certification =
            contract.Certifications.Single(item => item.Identity == identity && item.Profile == profile);
        bool certificationBound = certification.ImplementationSha256 == selection.ImplementationSha256 &&
            certification.InterfaceDigest == contract.InterfaceDigest &&
            certification.ClosureDigest == export.ClosureDigest &&
            certification.StatementDigest == binding.GetProperty("certificationStatementDigest").GetString();
        if (!certificationBound)
            throw new InvalidDataException("Full-verification certification binding mismatch: " + identity);
        if (bundles.TryGetValue(selection.Bundle, out string? previousDigest) && previousDigest != selection.Digest)
            throw new InvalidDataException(
                "Full-verification source bundle path has conflicting content identities: " + selection.Bundle);
        bundles.TryAdd(selection.Bundle, selection.Digest);
        return new(selection, export, certification, id);
    }

    // Checks one bundle's selected exports; dependencyId binds each regenerated import before the library build.
    FullLibrary[] CheckFullBundle(FullImport[] imports, string staging, string callerOutput, JsonElement[] graph,
        Func<string, JsonElement, int> dependencyId)
    {
        Directory.CreateDirectory(staging);
        FullSelection selection = imports[0].Selection;
        (ContractInterface contract, string bundle, string digest, ContractBundleManifest inventory) =
            (selection.Contract, selection.Bundle, selection.Digest, selection.Inventory);
        JsonElement[] metadata = inventory.Exports.EnumerateArray().ToArray();
        JsonElement originalManifest =
            JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Within(bundle, "producer/manifest.json")));
        string consumer = Path.Combine(staging, "consumer");
        ConsumerDependency dependency =
            StageFullConsumer(bundle, inventory, consumer, digest, contract.InterfaceModules);
        Dictionary<string, string> dependencyInterfaces = FullDependencyInterfaces(contract, callerOutput, graph);
        ContractSource[] interfaces = contract.InterfaceModules
            .Select(module => StageFullInterface(bundle, consumer, module, dependencyInterfaces)).ToArray();
        string implementation = selection.Implementation;
        List<FullSlot> slots = [];
        foreach (FullImport import in imports)
            slots.Add(RegenerateFullSlot(import, metadata, originalManifest, contract, bundle, consumer, staging,
                implementation, callerOutput, graph));
        // A missing or tampered dependency bundle fails here, before this library's build.
        int[][] dependencies = slots
            .Select(slot => slot.Imports.Select(binding => dependencyId(slot.Artifact, binding)).ToArray()).ToArray();
        ContractExportManifest manifest =
            new(1, implementation, consumer, interfaces, slots.Select(slot => slot.Request).ToArray());
        using ModuleDefinition module =
            ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(implementation)));
        PreparedContractExport[] prepared =
            slots.Select(slot => PrepareContractExport(manifest, module, slot.Request)).ToArray();
        using Program independent = new()
        {
            freshLibrary = true, forceFullVerification = true, fullBundleDependencies = [dependency]
        };
        string?[] transfers = new string?[slots.Count];
        ConsumerRequest[] requests = slots.Select((slot, index) =>
        {
            ContractExport export = slot.Import.Export;
            string auditSource = ExportAuditSource(prepared[index], export.Kind);
            ConsumerExportAudit audit = new(auditSource, (session, proofModule, leanPath) =>
            {
                ExportClosure actual =
                    independent.CheckExportClosure(session, proofModule, export.ContractConstant, leanPath);
                (string statementDigest, string _) = independent.CheckExportStatement(session, proofModule, leanPath);
                if (actual.Digest != export.ClosureDigest || actual.Kind != export.Kind ||
                    statementDigest != slot.Import.Certification.StatementDigest)
                    throw new InvalidDataException(
                        "Independent library export closure or canonical statement mismatch.");
                transfers[index] = independent.CaptureFullTerms(session, proofModule,
                    FullLibraryPrefix + slot.Import.Id, contract.InterfaceModules, leanPath);
            }, [ExportTheoremRequest(export.ContractConstant, export.Kind, prepared[index].Conditional),
                ExportTheoremRequest(export.ContractConstant, export.Kind, prepared[index].Conditional)
                    with { name = slot.Author }]);
            return new ConsumerRequest(implementation, slot.Artifact, prepared[index].Proof, ExportTheorem, null,
                ExportAudit: audit);
        }).ToArray();
        ConsumerOutcome[] outcomes = independent.VerifyConsumerRequests(consumer, requests, null, batch: false);
        return slots.Select((slot, index) =>
        {
            if (outcomes[index].Error is not null)
                System.Runtime.ExceptionServices.ExceptionDispatchInfo.Throw(outcomes[index].Error!);
            if (outcomes[index].Report is null || transfers[index] is null)
                throw new InvalidDataException(
                    "Independent library verification did not complete its exact export audit.");
            if (Sha(Path.Combine(slot.Artifact, "Extracted.lean")) != slot.GeneratedSha256)
                throw new InvalidDataException(
                    "Full-verification regenerated extraction changed after its library check: " + slot.Artifact);
            int id = slot.Import.Id;
            return new FullLibrary(id, FullLibraryPrefix + id, FullExpectedPrefix + id,
                selection.Digest, slot.Import.Export.ContractConstant, slot.Import.Export.Kind, transfers[index]!,
                slot.Generated, slot.Statics, contract.AssemblyIdentity, dependencies[index]);
        }).ToArray();
    }

    // Graph nodes reached from the declared dependencies; each declaration must match its node's pins.
    static IEnumerable<JsonElement> DependencyClosure(JsonElement[] graph, IEnumerable<ContractDependency> declared)
    {
        Queue<ContractDependency> pending = new(declared);
        HashSet<string> reached = new(StringComparer.Ordinal);
        while (pending.TryDequeue(out ContractDependency? dependency))
        {
            JsonElement node = FullGraphNode(graph, dependency.AssemblyIdentity);
            if (node.GetProperty("implementationSha256").GetString() != dependency.ImplementationSha256 ||
                node.GetProperty("interfaceDigest").GetString() != dependency.InterfaceDigest)
                throw new InvalidDataException(
                    "Full-verification dependency pin differs from the caller's graph node: " +
                    dependency.AssemblyIdentity);
            if (!reached.Add(dependency.AssemblyIdentity)) continue;
            yield return node;
            foreach (JsonElement next in node.GetProperty("dependencies").EnumerateArray())
                pending.Enqueue(new(next.GetProperty("assemblyIdentity").GetString()!,
                    next.GetProperty("implementationSha256").GetString()!,
                    next.GetProperty("interfaceDigest").GetString()!));
        }
    }

    // Interface sources of the direct dependencies, read from the caller's pinned graph sidecars.
    static Dictionary<string, string> FullDependencyInterfaces(ContractInterface contract, string callerOutput,
        JsonElement[] graph)
    {
        Dictionary<string, string> sources = new(StringComparer.Ordinal);
        foreach (ContractDependency dependency in contract.Dependencies)
        {
            JsonElement node = FullGraphNode(graph, dependency.AssemblyIdentity);
            ContractInterface pinned = ContractInterface.Read(File.ReadAllBytes(
                ExtractionIdentity.Resolve(callerOutput, node.GetProperty("sidecarPath").GetString()!)));
            if (pinned.InterfaceDigest != dependency.InterfaceDigest ||
                pinned.ImplementationSha256 != dependency.ImplementationSha256)
                throw new InvalidDataException(
                    "Full-verification dependency sidecar differs from its pin: " + dependency.AssemblyIdentity);
            foreach (InterfaceModule module in pinned.InterfaceModules)
                if (sources.TryGetValue(module.Name, out string? previous) && previous != module.Source)
                    throw new InvalidDataException("Conflicting dependency interface source: " + module.Name);
                else sources[module.Name] = module.Source;
        }
        return sources;
    }

    // A module the bundle publishes must equal its pinned source; one it does not must be a dependency's.
    // Any copy already in the consumer must equal the pinned source as well.
    static ContractSource StageFullInterface(string bundle, string consumer, InterfaceModule module,
        IReadOnlyDictionary<string, string> dependencyInterfaces)
    {
        string bundled = Within(bundle, "interface/" + module.Name.Replace('.', '/') + ".lean");
        bool published = File.Exists(bundled)
            ? File.ReadAllText(bundled) == module.Source
            : dependencyInterfaces.TryGetValue(module.Name, out string? inherited) && inherited == module.Source;
        if (!published)
            throw new InvalidDataException(
                "Full source bundle interface differs from the pinned source: " + module.Name);
        string target = Within(consumer, module.Name.Replace('.', '/') + ".lean");
        if (File.Exists(target) && File.ReadAllText(target) != module.Source)
            throw new InvalidDataException(
                "Bundled author interface source differs from the pinned interface: " + module.Name);
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        File.WriteAllText(target, module.Source);
        return new ContractSource(module.Name, target);
    }

    // Binds one import to its bundle records, then re-extracts it from the current DLL for the library run.
    FullSlot RegenerateFullSlot(FullImport import, JsonElement[] metadata, JsonElement originalManifest,
        ContractInterface contract, string bundle, string consumer, string staging, string implementation,
        string callerOutput, JsonElement[] graph)
    {
        (ContractExport export, ContractCertification certification) = (import.Export, import.Certification);
        int[] matches = Enumerable.Range(0, metadata.Length).Where(index =>
            metadata[index].GetProperty("identity").GetString() == export.Identity &&
            metadata[index].GetProperty("profile").GetString() == certification.Profile).ToArray();
        if (matches.Length != 1)
            throw new InvalidDataException("Full source bundle has no unique selected export/profile.");
        int selected = matches[0];
        JsonElement record = metadata[selected];
        bool recordBound = record.GetProperty("contract").GetString() == export.ContractConstant &&
            record.GetProperty("digest").GetString() == export.ClosureDigest &&
            record.GetProperty("statementDigest").GetString() == certification.StatementDigest &&
            record.GetProperty("statement").GetString() == certification.Statement;
        if (!recordBound)
            throw new InvalidDataException("Full source bundle export statement or closure binding mismatch.");
        JsonElement request = originalManifest.GetProperty("exports")[selected];
        string bundledIdentityPath = Within(bundle, "exports/" + selected + "/identity.json");
        JsonElement bundledIdentity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(bundledIdentityPath));
        bool extractionMatches =
            bundledIdentity.GetProperty("assemblySha256").GetString() == contract.ImplementationSha256 &&
            bundledIdentity.GetProperty("assemblyIdentity").GetString() == contract.AssemblyIdentity &&
            bundledIdentity.GetProperty("entry").GetString() == export.Signature &&
            bundledIdentity.GetProperty("profile").Deserialize<FeatureProfile>()?.Name == certification.Profile;
        if (!extractionMatches)
            throw new InvalidDataException(
                "Full source bundle extraction metadata differs from the selected implementation, method or profile.");
        string author = record.GetProperty("theorem").GetString()!;
        if (request.GetProperty("theorem").GetString() != author || !ContractInterface.Constant(author) ||
            request.GetProperty("contract").GetString() != export.ContractConstant)
            throw new InvalidDataException("Full source bundle author theorem binding mismatch.");
        if (!record.TryGetProperty("proofPath", out JsonElement recordedProof) ||
            recordedProof.ValueKind != JsonValueKind.String)
            throw new InvalidDataException("Source bundle lacks a portable proof path; export the contracts again.");
        string proof = Within(consumer, recordedProof.GetString()!);
        if (!File.Exists(proof))
            throw new InvalidDataException("Full source bundle is missing its rebased author proof.");
        string artifact = Path.Combine(staging, "regenerated-" + import.Id);
        string entry = export.DefinitionSignature ?? export.Signature;
        List<string> extraction =
            ["dotnet", ExtractorPath, "extract", implementation, entry, artifact, certification.Profile];
        foreach (string argument in export.TypeArguments ?? []) extraction.AddRange(["--type-argument", argument]);
        // Every dependency the library reaches resolves only to the caller's pinned graph nodes.
        foreach (JsonElement node in DependencyClosure(graph, contract.Dependencies))
        {
            string nodeSha256 = node.GetProperty("implementationSha256").GetString()!;
            string nodeInterface = node.GetProperty("interfaceDigest").GetString()!;
            string name = AssemblyNameReference.Parse(node.GetProperty("assemblyIdentity").GetString()!).Name;
            string nodeImplementation =
                ExtractionIdentity.Resolve(callerOutput, node.GetProperty("implementationPath").GetString()!);
            extraction.AddRange([
                "--import", ExtractionIdentity.Resolve(callerOutput, node.GetProperty("sidecarPath").GetString()!),
                "--import-implementation", name + "=" + nodeImplementation,
                "--import-sha256", name + "=" + nodeSha256, "--import-interface-sha256", name + "=" + nodeInterface]);
        }
        Run(extraction, progress: "Fresh extraction of the current imported library DLL");
        // Composition compiles these exact bytes, which the library run below binds to the DLL.
        byte[] generated = File.ReadAllBytes(Path.Combine(artifact, "Extracted.lean"));
        JsonElement regenerated =
            JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "identity.json")));
        foreach (string property in new[] { "initializedTypes", "staticValues" })
            if (regenerated.TryGetProperty(property, out JsonElement assumptions) && assumptions.GetArrayLength() != 0)
                throw new InvalidDataException(
                    "Full verification rejects static-value and initialization assumptions: " + property);
        // The fresh extraction decides the reachable RVA tables; every pinned record must name exactly them.
        StaticIdentityRecord[] statics = StaticIdentitySet(regenerated);
        StaticIdentity.Validate(statics);
        bool staticsBound = statics.All(item => item.AssemblyIdentity == contract.AssemblyIdentity) &&
            statics.SequenceEqual(StaticIdentitySet(import.Selection.Binding)) &&
            statics.SequenceEqual(StaticIdentitySet(bundledIdentity)) &&
            statics.SequenceEqual(
                certification.StaticIdentities.OrderBy(item => item.Identity, StringComparer.Ordinal));
        if (!staticsBound)
            throw new InvalidDataException(
                "Full-verification static identities differ from the current implementation: " + export.Identity);
        JsonElement[] imported = regenerated.TryGetProperty("imports", out JsonElement bindings)
            ? bindings.EnumerateArray().OrderBy(BindingSlot).ToArray() : [];
        if (imported.Select(BindingSlot).Where((slot, index) => slot != index).Any())
            throw new InvalidDataException("Full verification requires contiguous unique import slots.");
        VerificationSettings settings =
            new(1, Path.GetRelativePath(artifact, proof), author, Path.GetRelativePath(artifact, consumer));
        File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(settings, Json));
        return new(import, author, artifact, Encoding.UTF8.GetString(generated), ContractInterface.Hash(generated),
            new(entry, artifact, export.ContractConstant, author, export.TypeArguments), statics, imported);
    }

    // A record's scoped static identities in identity order; a missing list is malformed, not empty.
    static StaticIdentityRecord[] StaticIdentitySet(JsonElement record) =>
        (record.TryGetProperty("staticIdentities", out JsonElement statics)
            ? statics.Deserialize<StaticIdentityRecord[]>(ContractInterface.Json) : null)?
            .OrderBy(item => item.Identity, StringComparer.Ordinal).ToArray()
        ?? throw new InvalidDataException("Full-verification record lacks its static identities.");

    ConsumerDependency StageFullConsumer(string bundle, ContractBundleManifest inventory, string consumer,
        string digest, InterfaceModule[] interfaces)
    {
        string originalLockPath = Within(bundle, "consumer/lake-manifest.json");
        JsonElement originalLock = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(originalLockPath));
        JsonElement[] packages = originalLock.GetProperty("packages").EnumerateArray().ToArray();
        if (packages.Length != 1 || !IsRootLeanCilGitPackage(packages[0]))
            throw new InvalidDataException("Full source bundle version 1 supports the leancil source dependency only.");
        Directory.CreateDirectory(consumer);
        IEnumerable<string> consumerFiles =
            inventory.Files.Keys.Where(path => path.StartsWith("consumer/", StringComparison.Ordinal));
        foreach (string relative in consumerFiles)
        {
            string local = relative["consumer/".Length..];
            bool lakeFile = local.StartsWith(".lake/", StringComparison.Ordinal) ||
                local is "lakefile.lean" or "lakefile.toml" or "lake-manifest.json";
            if (lakeFile) continue;
            string target = Within(consumer, local);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Within(bundle, relative), target);
        }
        string framework = Within(consumer, ".lake/packages/leancil");
        foreach (string path in FrameworkBundleSources())
        {
            string relative = PortableRelativePath(Root, path);
            string source = Within(bundle, "framework/" + relative);
            if (File.ReadAllBytes(source).AsSpan().SequenceEqual(File.ReadAllBytes(path)) is false)
                throw new InvalidDataException(
                    "Full source bundle framework/toolchain differs from the verifier: " + relative);
            string target = Within(framework, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(source, target);
        }
        string[] modules = Directory.EnumerateFiles(consumer, "*.lean", SearchOption.AllDirectories)
            .Select(path => PortableRelativePath(consumer, path))
            .Where(path => !path.StartsWith(".lake/", StringComparison.Ordinal))
            .Select(path => path[..^5].Replace('/', '.')).Concat(interfaces.Select(module => module.Name))
            .Distinct(StringComparer.Ordinal).ToArray();
        bool unsupportedLayout = modules.Any(module => !ContractInterface.Constant(module) || module == "CIL" ||
            module.StartsWith("CIL.", StringComparison.Ordinal));
        if (unsupportedLayout) throw new InvalidDataException("Unsupported full source bundle module layout.");
        File.WriteAllText(Path.Combine(consumer, "lakefile.toml"),
            "name = \"leancil_full_source\"\n[[require]]\nname = \"leancil\"\npath = \".lake/packages/leancil\"\n" +
            string.Join("", modules.Select(module => "[[lean_lib]]\nname = \"" + module + "\"\n")));
        File.WriteAllText(Path.Combine(consumer, "lake-manifest.json"), JsonSerializer.Serialize(new
        {
            version = "1.2.0",
            packagesDir = ".lake/packages",
            lakeDir = ".lake",
            name = "leancil_full_source",
            fixedToolchain = false,
            packages = new[]
            {
                new { type = "path", name = "leancil", inherited = false, dir = ".lake/packages/leancil" }
            }
        }));
        return new("leancil", framework, framework, packages[0].GetProperty("rev").GetString()!, "bundle:" + digest);
    }

    // Version 1 bundles depend only on leancil itself, fetched from git at its repository root.
    static bool IsRootLeanCilGitPackage(JsonElement package) =>
        package.GetProperty("name").GetString() == "leancil" &&
        package.GetProperty("type").GetString() == "git" &&
        !(package.TryGetProperty("subDir", out JsonElement subdirectory) &&
            subdirectory.ValueKind == JsonValueKind.String && subdirectory.GetString() is not ("" or "."));

    string CaptureFullTerms(string session, string proofModule, string destination, InterfaceModule[] interfaces,
        string leanPath)
    {
        string toolchainLibrary = Path.Combine(Toolchain, "lib/lean");
        string[] shared = Directory.EnumerateFiles(toolchainLibrary, "*.olean", SearchOption.AllDirectories)
            .Select(path => PortableRelativePath(toolchainLibrary, path)[..^".olean".Length].Replace('/', '.'))
            .Concat(Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories)
                .Select(path => PortableRelativePath(Root, path)[..^".lean".Length].Replace('/', '.')))
            .Concat(["CIL"]).Concat(interfaces.Select(module => module.Name))
            .Distinct(StringComparer.Ordinal).ToArray();
        string captured = Path.Combine(session, destination + ".transfer");
        string probe = Path.Combine(session, "LeanCILCapture" + destination + ".lean");
        string sharedNames = JsonSerializer.Serialize(shared);
        string capture =
            $"CIL.Interface.FullTransfer.capture (<- Lean.getEnv) shared `{destination} #[`{ExportTheorem}]";
        string capturedPath = JsonSerializer.Serialize(captured);
        // Composition uses only the certified theorem; its closure carries the producer program.
        File.WriteAllText(probe, $$"""
import {{proofModule}}
import CIL.Interface.FullTransfer
run_cmd do
  let shared : Array Lean.Name := ({{sharedNames}} : List String).toArray.map String.toName
  let source <- match {{capture}} with
    | .ok source => pure source
    | .error message => throwError "{message}"
  IO.FS.writeFile {{capturedPath}} source
""");
        Run([LeanExecutable, probe], session, leanPath,
            progress: "Capturing actual checked author and extraction kernel terms");
        return File.ReadAllText(captured);
    }

    static string NamespacedExtraction(string source, string name)
    {
        int start = source.IndexOf("\nnamespace Extracted\n", StringComparison.Ordinal);
        if (start < 0 || source.Contains("_root_.Extracted", StringComparison.Ordinal))
            throw new InvalidDataException("Unsupported generated extraction namespace layout for full verification.");
        string header = source[..start];
        bool foreignImport = header.Split('\n')
            .Any(line => line.Length != 0 && !line.StartsWith("import CIL.", StringComparison.Ordinal));
        if (foreignImport)
            throw new InvalidDataException("Unsupported generated extraction import layout for full verification.");
        return header + "\nnamespace " + name + "\n" + source[(start + 1)..] + "\nend " + name + "\n";
    }

    static bool IsOleanFile(string path) => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal);

    static string RelativeModuleName(string root, string path) => ModuleName(PortableRelativePath(root, path));

    static SortedDictionary<string, string> FullArtifacts(string leanPath)
    {
        SortedDictionary<string, string> files = new(StringComparer.Ordinal);
        IEnumerable<string> directories =
            leanPath.Split(Path.PathSeparator).Where(Directory.Exists).Distinct(StringComparer.Ordinal);
        foreach (string directory in directories)
            foreach (string path in Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories))
                if (IsOleanFile(path)) files[path] = Sha(path);
        return files;
    }

    static void RequireFullArtifacts(SortedDictionary<string, string> accepted)
    {
        foreach ((string path, string digest) in accepted)
            if (!File.Exists(path) || Sha(path) != digest)
                throw new InvalidDataException("Full-verification source or compiled artifact changed: " + path);
    }

    static SortedDictionary<string, string> FullModulePaths(string leanPath)
    {
        SortedDictionary<string, string> modules = new(StringComparer.Ordinal);
        foreach (string root in leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(Path.GetFullPath).Distinct(PathComparer))
        {
            if (!Directory.Exists(root)) continue;
            foreach (string path in Directory.EnumerateFiles(root, "*.olean", SearchOption.AllDirectories))
            {
                string name = RelativeModuleName(root, path);
                if (!ContractInterface.Constant(name)) continue;
                string absolute = Path.GetFullPath(path);
                if (modules.TryGetValue(name, out string? previous) && !PathComparer.Equals(previous, absolute))
                    throw new InvalidDataException("Ambiguous full-verification module: " + name);
                modules[name] = absolute;
            }
        }
        return modules;
    }

    static IEnumerable<string> FullModuleArtifactPaths(string leanPath)
    {
        foreach (string root in leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Distinct(StringComparer.Ordinal))
            if (Directory.Exists(root))
                foreach (string path in Directory.EnumerateFiles(root, "*", SearchOption.AllDirectories))
                    if (IsOleanFile(path) && ContractInterface.Constant(RelativeModuleName(root, path)))
                        yield return Path.GetFullPath(path);
    }

    static SortedDictionary<string, string> FullModuleArtifacts(string leanPath) =>
        HashFiles(FullModuleArtifactPaths(leanPath).Distinct(StringComparer.Ordinal).Select(path => (path, path)));

    static void RequireFullModuleArtifactSet(string leanPath, SortedDictionary<string, string> expected)
    {
        foreach (string path in FullModuleArtifactPaths(leanPath))
            if (!expected.ContainsKey(path))
                throw new InvalidDataException("Unexpected full-verification caller artifact: " + path);
    }

    static void RequireFullModulePaths(string leanPath, SortedDictionary<string, string> expected)
    {
        SortedDictionary<string, string> current = FullModulePaths(leanPath);
        foreach ((string name, string path) in current)
            if (!expected.TryGetValue(name, out string? previous) || previous != path)
                throw new InvalidDataException("Full-verification module resolution changed: " + name);
        if (current.Count != expected.Count)
            throw new InvalidDataException("Full-verification module resolution lost a checked module.");
    }

    static object FullCompositionType()
    {
        static object App(params object[] parts) => new { app = parts };
        object program = AuditConstant("CIL.Program");
        object app = AuditConstant("Extracted.program");
        object libraries = AuditConstant("LeanCILFullComposition.libraries");
        object linked = App(AuditConstant("CIL.Safety.link"), app, libraries);
        object except = App(new { @const = "Except", levels = new[] { 0, 0 } }, AuditConstant("String"), program);
        object success = App(new { @const = "Except.ok", levels = new[] { 0, 0 } }, AuditConstant("String"), program,
            linked);
        object checkedLink = App(new { @const = "Eq", levels = new[] { 1 } }, except,
            App(AuditConstant("CIL.Safety.linkChecked"), app, libraries), success);
        object callerClaim = App(AuditConstant("LeanCILFullComposition.fullCallerClaim"), linked);
        return App(AuditConstant("And"), checkedLink, callerClaim);
    }

    static AuditConstantRequest[] FullCompositionConstants(string callerTheorem, IReadOnlyList<FullLibrary> libraries,
        int callers)
    {
        static object App(params object[] parts) => new { app = parts };
        static object ListConstant(string name) => new { @const = "List." + name, levels = new[] { 0 } };
        object libraryType = AuditConstant("CIL.Safety.Library");
        object LibraryList(IEnumerable<int> ids) => ids.Reverse().Aggregate(App(ListConstant("nil"), libraryType),
            (tail, id) => App(ListConstant("cons"), libraryType, AuditConstant("LeanCILFullComposition.library" + id),
                tail));
        object list = LibraryList(Enumerable.Range(0, callers));
        object claimType = new { forall = new object[] { AuditConstant("CIL.Program"), new { sort = 0 } } };
        object givenType = App(AuditConstant("CIL.Safety.HoldsGiven"), AuditConstant("Extracted.program"),
            AuditConstant("Extracted.ImportsHold"), new { bvar = 0 });
        object selectClaim =
            new { lam = new object[] { claimType, new { lam = new object[] { givenType, new { bvar = 1 } } } } };
        object callerClaim =
            App(AuditConstant("LeanCILFullComposition.selectFullCallerClaim"), "_", AuditConstant(callerTheorem));
        List<AuditConstantRequest> constants = [
            new("LeanCILFullComposition.libraries", list),
            new("LeanCILFullComposition.selectFullCallerClaim", selectClaim),
            new("LeanCILFullComposition.fullCallerClaim", callerClaim)];
        foreach (FullLibrary library in libraries)
        {
            // A library's program is its own extraction linked with exactly its pinned dependencies.
            object program = AuditConstant(library.ExpectedModule + ".Extracted.program");
            if (library.Dependencies.Length != 0)
            {
                string dependencies = "LeanCILFullComposition.dependencies" + library.Id;
                constants.Add(new(dependencies, LibraryList(library.Dependencies)));
                program = App(AuditConstant("CIL.Safety.link"), program, AuditConstant(dependencies));
            }
            object helpers = App(ListConstant("drop"), AuditConstant("CIL.Method"), new { nat = 1 }, program);
            object definition = App(AuditConstant("CIL.Safety.Library.mk"),
                AuditConstant(library.ExpectedModule + ".Extracted.method0"), helpers);
            constants.Add(new("LeanCILFullComposition.library" + library.Id, definition));
        }
        return [.. constants];
    }

    static string FullClaimSelector(string theorem) =>
        "def selectFullCallerClaim {claim : _root_.CIL.Program -> Prop} " +
        "(_given : _root_.CIL.Safety.HoldsGiven _root_.Extracted.program _root_.Extracted.ImportsHold claim) : " +
        "_root_.CIL.Program -> Prop := claim\n" +
        "def fullCallerClaim : _root_.CIL.Program -> Prop := selectFullCallerClaim _root_." + theorem + "\n";

    // Libraries ordered so each follows every library it links.
    static List<FullLibrary> DependencyOrder(IReadOnlyList<FullLibrary> libraries)
    {
        List<FullLibrary> ordered = [];
        HashSet<int> visiting = [];
        void Visit(FullLibrary library)
        {
            if (ordered.Contains(library)) return;
            if (!visiting.Add(library.Id))
                throw new InvalidDataException("Full-verification dependency cycle at library " + library.Id);
            foreach (int dependency in library.Dependencies) Visit(libraries.Single(item => item.Id == dependency));
            ordered.Add(library);
        }
        foreach (FullLibrary library in libraries) Visit(library);
        return ordered;
    }

    static string FullCompositionSource(string callerModule, string callerTheorem,
        IReadOnlyList<FullLibrary> libraries,
        int callerSlots)
    {
        StringBuilder source = new("import " + callerModule +
            "\nimport CIL.Safety.Linking\nimport CIL.Safety.StaticLinking\nimport CIL.Interface.Closure\n");
        foreach (FullLibrary library in libraries)
            source.AppendLine("import " + library.Module).AppendLine("import " + library.ExpectedModule);
        source.AppendLine("namespace LeanCILFullComposition\nopen CIL.Safety");
        foreach (FullLibrary library in DependencyOrder(libraries))
            source.Append(FullLibrarySource(library, libraries));
        int[] callers = Enumerable.Range(0, callerSlots).ToArray();
        source.AppendLine("def libraries : List Library := [" +
            string.Join(", ", callers.Select(id => "library" + id)) + "]");
        source.AppendLine("def specifications : List Relocatable := [" + Specifications(callers, libraries) + "]");
        source.AppendLine("theorem app_prefix : Links Extracted.program (link Extracted.program libraries) := " +
            "link_links _ _");
        // Equal static identities must name equal descriptors across the whole linked program.
        source.AppendLine("theorem staticLink : linkChecked Extracted.program libraries = " +
            ".ok (link Extracted.program libraries) :=\n  linkChecked_of_compatible (by decide +kernel)");
        foreach (int slot in callers)
            source.AppendLine("theorem relocation" + slot + " : RelocatesInto library" + slot +
                ".program " + "(link Extracted.program libraries) (linkSlot Extracted.program libraries " +
                slot + ") := link_relocates Extracted.program libraries (j := " + slot + ") (by decide)");
        source.AppendLine("theorem bridge (linked : CIL.Program) " +
            "(met : Imports Extracted.program specifications linked) : Extracted.ImportsHold linked := by\n  exact " +
            Conjunction(callers.Select(slot => "met " + slot + " (by decide)").ToArray()));
        source.AppendLine("def discharge {claim : CIL.Program -> Prop} " +
            "(callerProof : HoldsGiven Extracted.program Extracted.ImportsHold claim) :\n" +
            "    claim (link Extracted.program libraries) :=\n  composed (callerProof.mono bridge) rfl");
        source.AppendLine(FiniteLibraryProof("libraries", callers, "closed", false));
        source.AppendLine(FiniteLibraryProof("libraries", callers, "holds", true));
        source.AppendLine(FullClaimSelector(callerTheorem));
        source.AppendLine("theorem certified : linkChecked Extracted.program libraries = " +
            ".ok (link Extracted.program libraries) /\\\n    fullCallerClaim (link Extracted.program libraries) :=\n" +
            "  And.intro staticLink (discharge _root_." + callerTheorem + ")");
        source.AppendLine("#print axioms certified");
        source.AppendLine("end LeanCILFullComposition");
        return source.ToString();
    }

    static string Specifications(IEnumerable<int> ids, IReadOnlyList<FullLibrary> libraries) =>
        string.Join(", ", ids.Select(id => libraries.Single(library => library.Id == id)).Select(library =>
            "_root_.CIL.Safety." + ContractNamespace(library.Kind) + ".relocatable _root_." + library.Contract));

    // Proves one library's contract on its own linked program; a library with imports discharges them first.
    static string FullLibrarySource(FullLibrary library, IReadOnlyList<FullLibrary> libraries)
    {
        StringBuilder source = new();
        string index = library.Id.ToString(System.Globalization.CultureInfo.InvariantCulture);
        string program = library.ExpectedModule + ".Extracted.program";
        string holds = HoldsTerm(library.Kind, library.Contract);
        source.AppendLine("theorem programIdentity" + index + " : " + library.Module + ".Extracted.program = " +
            program + " := rfl");
        source.AppendLine("theorem extraction" + index + " : CIL.Extraction.TranslationValid " +
            library.ExpectedModule + ".Extracted.rawLayouts " +
            library.ExpectedModule + ".Extracted.computedLayouts " +
            library.ExpectedModule + ".Extracted.methodEvidence " +
            library.ExpectedModule + ".Extracted.imports " + program + " := " +
            library.ExpectedModule + ".Extracted.translation_valid");
        string certified = library.Module + ".LeanCILExportAudit.certified";
        if (library.Dependencies.Length == 0)
        {
            source.AppendLine("def library" + index + " : Library := { entry := " + library.ExpectedModule +
                ".Extracted.method0, helpers := " + program + ".drop 1 }");
            source.AppendLine("theorem libraryProgram" + index + " : library" + index + ".program = " + program +
                " := rfl");
            source.AppendLine("theorem closed" + index + " : Closed library" + index +
                ".program := Closed.of_check (by decide +kernel)");
            source.AppendLine("theorem holds" + index + " : " + holds + " library" + index +
                ".program 0 := by\n  simpa only [libraryProgram" + index + ", programIdentity" + index + "] using " +
                certified);
            return source.ToString();
        }
        string dependencies = "dependencies" + index;
        string linked = "(link " + program + " " + dependencies + ")";
        source.AppendLine("def " + dependencies + " : List Library := [" +
            string.Join(", ", library.Dependencies.Select(id => "library" + id)) + "]");
        source.AppendLine("def specifications" + index + " : List Relocatable := [" +
            Specifications(library.Dependencies, libraries) + "]");
        source.AppendLine("def library" + index + " : Library := { entry := " + library.ExpectedModule +
            ".Extracted.method0, helpers := " + linked + ".drop 1 }");
        source.AppendLine("theorem libraryProgram" + index + " : library" + index + ".program = " + linked +
            " := rfl");
        source.AppendLine("theorem closed" + index + " : Closed library" + index +
            ".program := Closed.of_check (by decide +kernel)");
        // The kernel checks each conjunct, so the transferred import assumptions need no separate pin.
        source.AppendLine("theorem bridge" + index + " (linked : CIL.Program) (met : Imports " + program + " " +
            "specifications" + index + " linked) : " + library.Module + ".Extracted.ImportsHold linked := by\n" +
            "  exact " + Conjunction(Enumerable.Range(0, library.Dependencies.Length)
                .Select(slot => "met " + slot + " (by decide)").ToArray()));
        source.AppendLine("theorem holds" + index + " : " + holds + " library" + index + ".program 0 := by\n" +
            "  have given := " + certified + "\n  rw [programIdentity" + index + "] at given\n" +
            "  rw [libraryProgram" + index + "]\n  exact composed (given.mono bridge" + index + ") rfl\n" +
            FiniteLibraryProof(dependencies, library.Dependencies, "closed", false) + "\n" +
            FiniteLibraryProof(dependencies, library.Dependencies, "holds", true));
        return source.ToString();
    }

    static string Conjunction(string[] values) => values.Length == 1 ? values[0] :
        "And.intro (" + values[0] + ") (" + Conjunction(values[1..]) + ")";

    // Discharges a goal over every member of list, whose members are the libraries named by ids in order.
    static string FiniteLibraryProof(string list, int[] ids, string theorem, bool specification)
    {
        StringBuilder source = new("    (by\n      intro index bound" + (specification ? " specification" : "") + "\n");
        string selected = Alternatives(Enumerable.Range(0, ids.Length).Select(index => "index = " + index).ToArray());
        source.AppendLine("      have selected : " + selected + " := by\n        simp only [" + list +
            ", List.length_cons, List.length_nil] at bound\n        omega");
        source.AppendLine("      rcases selected with " + string.Join(" | ", Enumerable.Repeat("rfl", ids.Length)));
        source.AppendLine("      all_goals first");
        foreach (int id in ids) source.AppendLine("        | exact " + theorem + id);
        source.Append("    )");
        return source.ToString();
    }

    static string Alternatives(string[] values) => values.Length == 1 ? values[0] :
        "Or (" + values[0] + ") (" + Alternatives(values[1..]) + ")";
}
