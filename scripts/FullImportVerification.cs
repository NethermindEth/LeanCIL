using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Nethermind.LeanCIL;

partial class Program
{
    sealed record FullLibrary(int Slot, string Module, string ExpectedModule, string BundleDigest,
        string Contract, string Kind, string TransferSource, string GeneratedSource);
    sealed record FullSelection(JsonElement Binding, string Sidecar, string SidecarSha256, string Implementation,
        string ImplementationSha256, ContractInterface Contract, string Bundle, string Digest,
        ContractBundleManifest Inventory);
    sealed record FullImport(FullSelection Selection, ContractExport Export, ContractCertification Certification)
    {
        public int Slot => BindingSlot(Selection.Binding);
    }
    sealed record FullSlot(FullImport Import, string Author, string Artifact, string Generated, string GeneratedSha256,
        ContractExportRequest Request);

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
        return new(binding, sidecar, sidecarSha256, implementation, implementationSha256, contract, bundle, digest,
            ContractSourceBundle.Validate(bundle, digest));
    }

    static void RequireUsedOverrides(IReadOnlyDictionary<string, string> overrides, ISet<string> used)
    {
        if (overrides.Keys.Any(name => !used.Contains(name)))
            throw new InvalidDataException(
                "Unused --full-artifact override; supply the imported assembly simple name.");
    }

    void PreflightFullImports(string output, IReadOnlyDictionary<string, string> overrides)
    {
        JsonElement[] imports = ExtractionIdentity.Read(output).Imports;
        if (imports.Length == 0) throw new InvalidDataException(NoFullImports);
        HashSet<string> used = new(StringComparer.Ordinal);
        foreach (JsonElement binding in imports) SelectFullBundle(output, binding, overrides, used);
        RequireUsedOverrides(overrides, used);
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
        List<FullImport> imports = CollectFullImports(output, overrides, bindings, original, bundles);
        List<FullLibrary> libraries = [];
        // One library build per bundle, however many of its methods the caller imports.
        IEnumerable<IGrouping<string, FullImport>> byBundle =
            imports.GroupBy(item => item.Selection.Bundle, StringComparer.Ordinal);
        foreach ((IGrouping<string, FullImport> group, int index) in byBundle.Select((group, index) => (group, index)))
        {
            int implementations = group
                .Select(item => (item.Selection.SidecarSha256, item.Selection.ImplementationSha256))
                .Distinct().Count();
            if (implementations != 1)
                throw new InvalidDataException(
                    "Full-verification source bundle is shared by different implementations: " + group.Key);
            libraries.AddRange(CheckFullBundle(group.ToArray(), Path.Combine(staging, "bundle-" + index)));
            RequireCallerUnchanged();
        }
        libraries.Sort((left, right) => left.Slot.CompareTo(right.Slot));
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
            FullCompositionSource(callerModule, callerTheorem, libraries));
        CheckFullResolution(compositionDirectory, fullLeanPath, FullModulePaths(fullLeanPath));
        Compile(composition, "Checking concrete library relocation and caller composition", untrusted: true);
        Run([checker, composition], callerSession, fullLeanPath,
            progress: "Independent kernel replay of the composed caller theorem");
        AuditRequest certified =
            new(FullCompositionTheorem, type: FullCompositionType(), axioms: ApprovedAxioms, statement: true);
        AuditedOleans audited = AuditOleans(fullLeanPath, [composition], [certified],
            FullCompositionConstants(callerTheorem, libraries));
        RequireAuditedModule(audited, composition, Path.Combine(compositionDirectory, composition + ".olean"));
        RecheckResolution();
        RequireAuditedConstants(audited);
        AuditedAxioms(audited.theorems[0]);
        string audit = AuditText(audited.theorems[0]);
        return new(FullCompositionTheorem, audit, IndependentlyVerifiedImports(output, libraries));
    }

    // The caller's published imports, each now accepted through its checked bundle instead of its sidecar.
    static PublishedImport[] IndependentlyVerifiedImports(string output, List<FullLibrary> libraries)
    {
        string identity = File.ReadAllText(Path.Combine(output, "identity.json"));
        return PublishedImports(JsonSerializer.Deserialize<JsonElement>(identity))
            .Select(import => import with
            {
                acceptedVia = "independently-verified",
                sourceBundleDigest = libraries[import.slot].BundleDigest,
                deploymentObligation = FullDeploymentObligation
            }).ToArray();
    }

    // Pins every binding's sidecar and implementation in original and its bundle identity in bundles.
    static List<FullImport> CollectFullImports(string output, IReadOnlyDictionary<string, string> overrides,
        JsonElement[] bindings, SortedDictionary<string, string> original, Dictionary<string, string> bundles)
    {
        HashSet<string> usedOverrides = new(StringComparer.Ordinal);
        List<FullImport> imports = [];
        foreach (JsonElement binding in bindings)
        {
            string identity = binding.GetProperty("identity").GetString()!;
            FullSelection selection = SelectFullBundle(output, binding, overrides, usedOverrides);
            original[selection.Sidecar] = selection.SidecarSha256;
            original[selection.Implementation] = selection.ImplementationSha256;
            ContractInterface contract = selection.Contract;
            if (contract.Dependencies.Length != 0 || contract.IsReferenceAssembly)
                throw new InvalidDataException(
                    "Full verification version 1 requires closed implementation libraries without transitive imports.");
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
            imports.Add(new(selection, export, certification));
        }
        RequireUsedOverrides(overrides, usedOverrides);
        return imports;
    }

    FullLibrary[] CheckFullBundle(FullImport[] imports, string staging)
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
        ContractSource[] interfaces =
            contract.InterfaceModules.Select(module => StageFullInterface(bundle, consumer, module)).ToArray();
        string implementation = selection.Implementation;
        List<FullSlot> slots = [];
        foreach (FullImport import in imports)
            slots.Add(RegenerateFullSlot(import, metadata, originalManifest, contract, bundle, consumer, staging,
                implementation));
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
                    FullLibraryPrefix + slot.Import.Slot, contract.InterfaceModules, leanPath);
            }, [ExportTheoremRequest(export.ContractConstant, export.Kind),
                ExportTheoremRequest(export.ContractConstant, export.Kind) with { name = slot.Author }]);
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
            int slotIndex = slot.Import.Slot;
            return new FullLibrary(slotIndex, FullLibraryPrefix + slotIndex, FullExpectedPrefix + slotIndex,
                selection.Digest, slot.Import.Export.ContractConstant, slot.Import.Export.Kind, transfers[index]!,
                slot.Generated);
        }).ToArray();
    }

    // The bundled interface must equal the pinned source, and so must any copy already in the consumer.
    static ContractSource StageFullInterface(string bundle, string consumer, InterfaceModule module)
    {
        string bundled = Within(bundle, "interface/" + module.Name.Replace('.', '/') + ".lean");
        if (File.ReadAllText(bundled) != module.Source)
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
        ContractInterface contract, string bundle, string consumer, string staging, string implementation)
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
        string artifact = Path.Combine(staging, "regenerated-" + import.Slot);
        string entry = export.DefinitionSignature ?? export.Signature;
        List<string> extraction =
            ["dotnet", ExtractorPath, "extract", implementation, entry, artifact, certification.Profile];
        foreach (string argument in export.TypeArguments ?? []) extraction.AddRange(["--type-argument", argument]);
        Run(extraction, progress: "Fresh extraction of the current imported library DLL");
        // Composition compiles these exact bytes, which the library run below binds to the DLL.
        byte[] generated = File.ReadAllBytes(Path.Combine(artifact, "Extracted.lean"));
        JsonElement regenerated =
            JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "identity.json")));
        foreach (string property in new[] { "initializedTypes", "staticValues", "staticIdentities" })
            if (regenerated.TryGetProperty(property, out JsonElement assumptions) && assumptions.GetArrayLength() != 0)
                throw new InvalidDataException(
                    "Full verification version 1 rejects static or initialization state: " + property);
        VerificationSettings settings =
            new(1, Path.GetRelativePath(artifact, proof), author, Path.GetRelativePath(artifact, consumer));
        File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(settings, Json));
        return new(import, author, artifact, Encoding.UTF8.GetString(generated), ContractInterface.Hash(generated),
            new(entry, artifact, export.ContractConstant, author, export.TypeArguments));
    }

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
        new(FullModuleArtifactPaths(leanPath).Distinct(StringComparer.Ordinal).ToDictionary(path => path, Sha),
            StringComparer.Ordinal);

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

    static AuditConstantRequest[] FullCompositionConstants(string callerTheorem, IReadOnlyList<FullLibrary> libraries)
    {
        static object App(params object[] parts) => new { app = parts };
        static object ListConstant(string name) => new { @const = "List." + name, levels = new[] { 0 } };
        object libraryType = AuditConstant("CIL.Safety.Library");
        object list = App(ListConstant("nil"), libraryType);
        foreach (FullLibrary library in libraries.Reverse())
            list = App(ListConstant("cons"), libraryType,
                AuditConstant("LeanCILFullComposition.library" + library.Slot), list);
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
            object helpers = App(ListConstant("drop"), AuditConstant("CIL.Method"), new { nat = 1 },
                AuditConstant(library.ExpectedModule + ".Extracted.program"));
            object definition = App(AuditConstant("CIL.Safety.Library.mk"),
                AuditConstant(library.ExpectedModule + ".Extracted.method0"), helpers);
            constants.Add(new("LeanCILFullComposition.library" + library.Slot, definition));
        }
        return [.. constants];
    }

    static string FullClaimSelector(string theorem) =>
        "def selectFullCallerClaim {claim : _root_.CIL.Program -> Prop} " +
        "(_given : _root_.CIL.Safety.HoldsGiven _root_.Extracted.program _root_.Extracted.ImportsHold claim) : " +
        "_root_.CIL.Program -> Prop := claim\n" +
        "def fullCallerClaim : _root_.CIL.Program -> Prop := selectFullCallerClaim _root_." + theorem + "\n";

    static string FullCompositionSource(string callerModule, string callerTheorem, IReadOnlyList<FullLibrary> libraries)
    {
        StringBuilder source = new("import " + callerModule +
            "\nimport CIL.Safety.Linking\nimport CIL.Safety.StaticLinking\nimport CIL.Interface.Closure\n");
        foreach (FullLibrary library in libraries)
            source.AppendLine("import " + library.Module).AppendLine("import " + library.ExpectedModule);
        source.AppendLine("namespace LeanCILFullComposition\nopen CIL.Safety");
        foreach (FullLibrary library in libraries)
        {
            string index = library.Slot.ToString(System.Globalization.CultureInfo.InvariantCulture);
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
            source.AppendLine("def library" + index + " : Library := { entry := " + library.ExpectedModule +
                ".Extracted.method0, helpers := " + program + ".drop 1 }");
            source.AppendLine("theorem libraryProgram" + index + " : library" + index + ".program = " + program +
                " := rfl");
            source.AppendLine("theorem closed" + index + " : Closed library" + index +
                ".program := Closed.of_check (by decide +kernel)");
            source.AppendLine("theorem holds" + index + " : " + holds + " library" + index +
                ".program 0 := by\n  simpa only [libraryProgram" + index + ", programIdentity" + index + "] using " +
                library.Module + ".LeanCILExportAudit.certified");
        }
        source.AppendLine("def libraries : List Library := [" +
            string.Join(", ", libraries.Select(library => "library" + library.Slot)) + "]");
        source.AppendLine("def specifications : List Relocatable := [" + string.Join(", ", libraries.Select(library =>
            "_root_.CIL.Safety." + ContractNamespace(library.Kind) + ".relocatable _root_." + library.Contract)) + "]");
        source.AppendLine("theorem app_prefix : Links Extracted.program (link Extracted.program libraries) := " +
            "link_links _ _");
        // Equal static identities must name equal descriptors across the whole linked program.
        source.AppendLine("theorem staticLink : linkChecked Extracted.program libraries = " +
            ".ok (link Extracted.program libraries) :=\n  linkChecked_of_compatible (by decide +kernel)");
        foreach (FullLibrary library in libraries)
            source.AppendLine("theorem relocation" + library.Slot + " : RelocatesInto library" + library.Slot +
                ".program " + "(link Extracted.program libraries) (linkSlot Extracted.program libraries " +
                library.Slot + ") := link_relocates Extracted.program libraries (j := " + library.Slot +
                ") (by decide)");
        source.AppendLine("theorem bridge (linked : CIL.Program) " +
            "(met : Imports Extracted.program specifications linked) : Extracted.ImportsHold linked := by\n  exact " +
            Conjunction(libraries.Select(library => "met " + library.Slot + " (by decide)").ToArray()));
        source.AppendLine("def discharge {claim : CIL.Program -> Prop} " +
            "(callerProof : HoldsGiven Extracted.program Extracted.ImportsHold claim) :\n" +
            "    claim (link Extracted.program libraries) :=\n  composed (callerProof.mono bridge) rfl");
        source.AppendLine(FiniteLibraryProof(libraries.Count, "closed", false));
        source.AppendLine(FiniteLibraryProof(libraries.Count, "holds", true));
        source.AppendLine(FullClaimSelector(callerTheorem));
        source.AppendLine("theorem certified : linkChecked Extracted.program libraries = " +
            ".ok (link Extracted.program libraries) /\\\n    fullCallerClaim (link Extracted.program libraries) :=\n" +
            "  And.intro staticLink (discharge _root_." + callerTheorem + ")");
        source.AppendLine("#print axioms certified");
        source.AppendLine("end LeanCILFullComposition");
        return source.ToString();
    }

    static string Conjunction(string[] values) => values.Length == 1 ? values[0] :
        "And.intro (" + values[0] + ") (" + Conjunction(values[1..]) + ")";

    static string FiniteLibraryProof(int count, string theorem, bool specification)
    {
        StringBuilder source = new("    (by\n      intro index bound" + (specification ? " specification" : "") + "\n");
        string selected = Alternatives(Enumerable.Range(0, count).Select(index => "index = " + index).ToArray());
        source.AppendLine("      have selected : " + selected +
            " := by\n        simp only [libraries, List.length_cons, List.length_nil] at bound\n        omega");
        source.AppendLine("      rcases selected with " + string.Join(" | ", Enumerable.Repeat("rfl", count)));
        source.AppendLine("      all_goals first");
        for (int index = 0; index < count; index++) source.AppendLine("        | exact " + theorem + index);
        source.Append("    )");
        return source.ToString();
    }

    static string Alternatives(string[] values) => values.Length == 1 ? values[0] :
        "Or (" + values[0] + ") (" + Alternatives(values[1..]) + ")";
}
