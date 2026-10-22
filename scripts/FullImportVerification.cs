using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Nethermind.LeanCIL;

partial class Program
{
    sealed record FullLibrary(int Slot, string Module, string ExpectedModule, string BundleDigest,
        string Contract, string Kind, string TransferSource, string GeneratedSource);

    void PreflightFullImports(string output, IReadOnlyDictionary<string, string> overrides)
    {
        JsonElement[] imports = ImportedBindings(output);
        if (imports.Length == 0) throw new InvalidDataException("Full verification requires at least one contract import.");
        HashSet<string> used = new(StringComparer.Ordinal);
        foreach (JsonElement binding in imports)
        {
            string sidecar = binding.GetProperty("sidecarPath").GetString()!;
            if (Sha(sidecar) != binding.GetProperty("sidecarSha256").GetString() ||
                Sha(binding.GetProperty("implementationPath").GetString()!) != binding.GetProperty("implementationSha256").GetString())
                throw new InvalidDataException("Full-verification imported implementation or sidecar changed.");
            ContractInterface contract = ContractInterface.Read(File.ReadAllBytes(sidecar));
            string locator = contract.FullVerificationLocator ?? throw new InvalidDataException("Full verification source bundle is missing: " + contract.AssemblyIdentity);
            string digest = Path.GetFileName(Path.TrimEndingDirectorySeparator(locator));
            string name = AssemblyNameReference.Parse(contract.AssemblyIdentity).Name;
            string selected = overrides.TryGetValue(name, out string? replacement) ? replacement : locator;
            if (replacement is not null) used.Add(name);
            if (!Directory.Exists(selected)) throw new InvalidDataException("Full verification source bundle is missing: " + selected);
            if (!ContractInterface.Digest(digest) || Path.GetFileName(Path.TrimEndingDirectorySeparator(selected)) != digest)
                throw new InvalidDataException("Full-verification source bundle override has the wrong content identity.");
            ContractSourceBundle.Validate(selected, digest);
        }
        if (overrides.Keys.Any(name => !used.Contains(name))) throw new InvalidDataException("Unused --full-artifact override.");
    }

    FullImportResult VerifyFullImports(string output, string callerSession, string callerModule, string callerTheorem,
        string callerLeanPath, IReadOnlyDictionary<string, string> overrides)
    {
        string originalLeanPath = string.Join(Path.PathSeparator, callerLeanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(path => Path.GetFullPath(path, callerSession)).Append(Path.Combine(Toolchain, "lib/lean"))
            .Distinct(OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal));
        SortedDictionary<string, string> acceptedCaller = FullModuleArtifacts(originalLeanPath);
        SortedDictionary<string, string> originalModules = FullModulePaths(originalLeanPath);
        string originalClaim = CaptureFullCallerClaim(callerSession, callerModule, callerTheorem, originalLeanPath);
        CheckFullResolution(callerSession, originalLeanPath, originalModules);
        RequireFullArtifacts(acceptedCaller);
        JsonElement[] bindings = ImportedBindings(output).OrderBy(binding => binding.GetProperty("slot").GetInt32()).ToArray();
        if (bindings.Length == 0) throw new InvalidDataException("Full verification requires at least one contract import.");
        for (int index = 0; index < bindings.Length; index++)
            if (bindings[index].GetProperty("slot").GetInt32() != index)
                throw new InvalidDataException("Full verification requires contiguous unique import slots.");
        string staging = Path.Combine(callerSession, "full-imports-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(staging);
        SortedDictionary<string, string> original = new(StringComparer.Ordinal);
        Dictionary<string, string> bundles = new(StringComparer.Ordinal);
        List<FullLibrary> libraries = [];
        HashSet<string> usedOverrides = new(StringComparer.Ordinal);
        void Original(string path) => original[path] = Sha(path);
        void RecheckOriginal()
        {
            foreach ((string path, string digest) in original)
                if (!File.Exists(path) || Sha(path) != digest) throw new InvalidDataException("Full-verification input changed: " + path);
            foreach ((string directory, string digest) in bundles) ContractSourceBundle.Validate(directory, digest);
        }
        Original(Path.Combine(output, "identity.json"));
        Original(Path.Combine(output, "Extracted.lean"));
        foreach (JsonElement binding in bindings)
        {
            string identity = binding.GetProperty("identity").GetString()!;
            string sidecarPath = binding.GetProperty("sidecarPath").GetString()!;
            string implementation = binding.GetProperty("implementationPath").GetString()!;
            Original(sidecarPath);
            Original(implementation);
            if (original[sidecarPath] != binding.GetProperty("sidecarSha256").GetString() ||
                original[implementation] != binding.GetProperty("implementationSha256").GetString())
                throw new InvalidDataException("Full-verification imported implementation or sidecar changed: " + identity);
            ContractInterface contract = ContractInterface.Read(File.ReadAllBytes(sidecarPath));
            if (contract.Dependencies.Length != 0 || contract.IsReferenceAssembly)
                throw new InvalidDataException("Full verification version 1 requires closed implementation libraries without transitive imports.");
            string profile = binding.GetProperty("profile").GetString()!;
            ContractExport export = contract.Exports.Single(item => item.Identity == identity);
            ContractCertification certification = contract.Certifications.Single(item => item.Identity == identity && item.Profile == profile);
            if (certification.ImplementationSha256 != original[implementation] || certification.InterfaceDigest != contract.InterfaceDigest ||
                certification.ClosureDigest != export.ClosureDigest || certification.StatementDigest != binding.GetProperty("certificationStatementDigest").GetString())
                throw new InvalidDataException("Full-verification certification binding mismatch: " + identity);
            string locator = contract.FullVerificationLocator ?? throw new InvalidDataException("Full verification source bundle is missing: " + identity);
            string digest = Path.GetFileName(Path.TrimEndingDirectorySeparator(locator));
            if (!ContractInterface.Digest(digest)) throw new InvalidDataException("Full-verification locator must name a content-addressed source bundle.");
            string simple = AssemblyNameReference.Parse(contract.AssemblyIdentity).Name;
            string selected = overrides.TryGetValue(simple, out string? selectedOverride) ? selectedOverride : locator;
            if (selectedOverride is not null) usedOverrides.Add(simple);
            string bundle = Path.GetFullPath(selected);
            if (!Directory.Exists(bundle)) throw new InvalidDataException("Full verification source bundle is missing: " + bundle);
            if (Path.GetFileName(Path.TrimEndingDirectorySeparator(bundle)) != digest)
                throw new InvalidDataException("Full-verification source bundle override has the wrong content identity.");
            ContractBundleManifest inventory = ContractSourceBundle.Validate(bundle, digest);
            if (bundles.TryGetValue(bundle, out string? previousDigest) && previousDigest != digest)
                throw new InvalidDataException("Full-verification source bundle path has conflicting content identities: " + bundle);
            bundles.TryAdd(bundle, digest);
            int slot = binding.GetProperty("slot").GetInt32();
            libraries.Add(CheckFullLibrary(binding, contract, export, certification, inventory, bundle, digest,
                Path.Combine(staging, "library-" + slot), RecheckOriginal));
            RequireFullArtifacts(acceptedCaller);
            RequireFullModuleArtifactSet(originalLeanPath, acceptedCaller);
            RequireFullModulePaths(originalLeanPath, originalModules);
            RequireEmptyProducerModules(staging);
        }
        if (overrides.Keys.Any(name => !usedOverrides.Contains(name)))
            throw new InvalidDataException("Unused --full-artifact override; supply the imported assembly simple name.");
        RecheckOriginal();
        string compositionDirectory = Path.Combine(callerSession, "full-composition-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(compositionDirectory);
        string fullLeanPath = originalLeanPath + Path.PathSeparator + compositionDirectory;
        HashSet<string> generatedModules = new(StringComparer.Ordinal);
        SortedDictionary<string, string> generatedArtifacts = new(StringComparer.Ordinal);
        void RecheckResolution()
        {
            RequireFullArtifacts(acceptedCaller);
            RequireFullModuleArtifactSet(originalLeanPath, acceptedCaller);
            RequireFullModulePaths(originalLeanPath, originalModules);
            RequireEmptyProducerModules(staging);
            RequireFullArtifacts(generatedArtifacts);
            SortedDictionary<string, string> generated = FullModulePaths(compositionDirectory);
            foreach ((string name, string path) in generated)
                if (!generatedModules.Contains(name) || originalModules.ContainsKey(name))
                    throw new InvalidDataException("Unexpected full-verification composition module: " + name + " at " + path);
            foreach (string path in FullModuleArtifactPaths(compositionDirectory))
                if (!generatedModules.Contains(ModuleName(Path.GetRelativePath(compositionDirectory, path).Replace('\\', '/'))))
                    throw new InvalidDataException("Unexpected full-verification composition artifact: " + path);
        }
        foreach (string name in libraries.SelectMany(library => new[] { library.ExpectedModule, library.Module }).Append("LeanCILFullComposition"))
            if (originalModules.ContainsKey(name)) throw new InvalidDataException("Full-verification generated module collides with an existing module: " + name);
        string checker = Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
        foreach (FullLibrary library in libraries)
        {
            string expected = Path.Combine(compositionDirectory, library.ExpectedModule + ".lean");
            File.WriteAllText(expected, NamespacedExtraction(library.GeneratedSource, library.ExpectedModule));
            string transferred = Path.Combine(compositionDirectory, library.Module + ".lean");
            File.WriteAllText(transferred, "import " + callerModule + "\n" + library.TransferSource);
            foreach (string name in new[] { library.ExpectedModule, library.Module })
            {
                RecheckResolution();
                Run([LeanExecutable, "--root=" + compositionDirectory, "-o", Path.Combine(compositionDirectory, name + ".olean"), Path.Combine(compositionDirectory, name + ".lean")],
                    callerSession, fullLeanPath, progress: "Rechecking full-verification program and author kernel terms: " + name);
                generatedModules.Add(name);
                RecheckResolution();
                generatedArtifacts = FullArtifacts(compositionDirectory);
            }
            RecheckOriginal();
            RecheckResolution();
            Run([checker, library.ExpectedModule, library.Module], callerSession, fullLeanPath,
                progress: "Independent kernel replay of transferred library declarations");
            RequireFullArtifacts(acceptedCaller);
        }
        string composition = "LeanCILFullComposition";
        string compositionPath = Path.Combine(compositionDirectory, composition + ".lean");
        File.WriteAllText(compositionPath, FullCompositionSource(callerModule, callerTheorem, originalClaim, libraries));
        RecheckResolution();
        CheckFullResolution(compositionDirectory, fullLeanPath, FullModulePaths(fullLeanPath));
        Run([LeanExecutable, "--root=" + compositionDirectory, "-o", Path.Combine(compositionDirectory, composition + ".olean"), compositionPath],
            callerSession, fullLeanPath, progress: "Checking concrete library relocation and caller composition");
        generatedModules.Add(composition);
        RecheckResolution();
        generatedArtifacts = FullArtifacts(compositionDirectory);
        CheckFullResolution(compositionDirectory, fullLeanPath, FullModulePaths(fullLeanPath));
        RecheckOriginal();
        RequireFullArtifacts(acceptedCaller);
        SortedDictionary<string, string> acceptedFull = new(FullFiles(staging).Concat(FullFiles(compositionDirectory))
            .ToDictionary(pair => pair.Key, pair => pair.Value), StringComparer.Ordinal);
        Run([checker, composition], callerSession, fullLeanPath, progress: "Independent kernel replay of the composed caller theorem");
        RequireFullArtifacts(acceptedFull);
        string auditPath = Path.Combine(compositionDirectory, "CompositionAudit.lean");
        File.WriteAllText(auditPath, "import " + composition + "\n#check LeanCILFullComposition.certified\n#print axioms LeanCILFullComposition.certified\n");
        string audit = Run([LeanExecutable, auditPath], callerSession, fullLeanPath, progress: "Auditing the independently composed theorem");
        AuditedAxioms(audit, "LeanCILFullComposition.certified");
        RequireFullArtifacts(acceptedFull);
        RequireFullArtifacts(acceptedCaller);
        RecheckResolution();
        RecheckOriginal();
        SortedDictionary<string, string> finalFull = new(FullFiles(staging).Concat(FullFiles(compositionDirectory))
            .ToDictionary(pair => pair.Key, pair => pair.Value), StringComparer.Ordinal);
        PublishedImport[] imported = PublishedImports(JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json"))))
            .Select(import => import with
            {
                acceptedVia = "independently-verified", sourceBundleDigest = libraries[import.slot].BundleDigest,
                deploymentObligation = "The composed CIL theorem checks this exact implementation and profile; DLL decoding and runtime/model correspondence remain trusted."
            }).ToArray();
        return new("LeanCILFullComposition.certified", audit, imported, () =>
        {
            RecheckOriginal();
            RequireFullArtifacts(acceptedCaller);
            RequireFullArtifacts(finalFull);
            RecheckResolution();
        });
    }

    FullLibrary CheckFullLibrary(JsonElement binding, ContractInterface contract, ContractExport export,
        ContractCertification certification, ContractBundleManifest inventory, string bundle, string digest,
        string staging, Action recheck)
    {
        Directory.CreateDirectory(staging);
        JsonElement[] metadata = inventory.Exports.EnumerateArray().ToArray();
        int[] matches = Enumerable.Range(0, metadata.Length).Where(index =>
            metadata[index].GetProperty("identity").GetString() == export.Identity &&
            metadata[index].GetProperty("profile").GetString() == certification.Profile).ToArray();
        if (matches.Length != 1) throw new InvalidDataException("Full source bundle has no unique selected export/profile.");
        int selected = matches[0];
        JsonElement record = metadata[selected];
        if (record.GetProperty("contract").GetString() != export.ContractConstant || record.GetProperty("digest").GetString() != export.ClosureDigest ||
            record.GetProperty("statementDigest").GetString() != certification.StatementDigest || record.GetProperty("statement").GetString() != certification.Statement)
            throw new InvalidDataException("Full source bundle export statement or closure binding mismatch.");
        JsonElement originalManifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Within(bundle, "producer/manifest.json")));
        JsonElement request = originalManifest.GetProperty("exports")[selected];
        JsonElement bundledIdentity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Within(bundle, "exports/" + selected + "/identity.json")));
        if (bundledIdentity.GetProperty("assemblySha256").GetString() != contract.ImplementationSha256 ||
            bundledIdentity.GetProperty("assemblyIdentity").GetString() != contract.AssemblyIdentity ||
            bundledIdentity.GetProperty("entry").GetString() != export.Signature ||
            bundledIdentity.GetProperty("profile").Deserialize<FeatureProfile>()?.Name != certification.Profile)
            throw new InvalidDataException("Full source bundle extraction metadata differs from the selected implementation, method or profile.");
        string author = record.GetProperty("theorem").GetString()!;
        if (request.GetProperty("theorem").GetString() != author || !ContractInterface.Constant(author) ||
            request.GetProperty("contract").GetString() != export.ContractConstant)
            throw new InvalidDataException("Full source bundle author theorem binding mismatch.");
        string consumer = Path.Combine(staging, "consumer");
        ConsumerDependency dependency = StageFullConsumer(bundle, inventory, consumer, digest, contract.InterfaceModules);
        JsonElement settings = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Within(bundle, "exports/" + selected + "/verification.json")));
        string logicalArtifact = Path.GetFullPath(request.GetProperty("artifact").GetString()!, Path.Combine(staging, "original-path-base"));
        string savedRoot = settings.TryGetProperty("proofRoot", out JsonElement savedProofRoot) && savedProofRoot.ValueKind == JsonValueKind.String
            ? Path.GetFullPath(savedProofRoot.GetString()!, logicalArtifact)
            : Path.GetFullPath(originalManifest.GetProperty("proofRoot").GetString()!, Path.Combine(staging, "original-path-base"));
        string savedProof = Path.GetFullPath(settings.GetProperty("proof").GetString()!, logicalArtifact);
        string proof = Within(consumer, Path.GetRelativePath(savedRoot, savedProof));
        if (!File.Exists(proof)) throw new InvalidDataException("Full source bundle is missing its rebased author proof.");
        ContractSource[] interfaces = contract.InterfaceModules.Select(module =>
        {
            string bundled = Within(bundle, "interface/" + module.Name.Replace('.', '/') + ".lean");
            if (File.ReadAllText(bundled) != module.Source) throw new InvalidDataException("Full source bundle interface differs from the pinned source: " + module.Name);
            string target = Within(consumer, module.Name.Replace('.', '/') + ".lean");
            if (File.Exists(target) && File.ReadAllText(target) != module.Source)
                throw new InvalidDataException("Bundled author interface source differs from the pinned interface: " + module.Name);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.WriteAllText(target, module.Source);
            return new ContractSource(module.Name, target);
        }).ToArray();
        string artifact = Path.Combine(staging, "regenerated");
        string implementation = binding.GetProperty("implementationPath").GetString()!;
        Run(["dotnet", ExtractorPath, "extract", implementation, export.Signature, artifact, certification.Profile],
            progress: "Fresh extraction of the current imported library DLL");
        JsonElement regenerated = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "identity.json")));
        foreach (string property in new[] { "initializedTypes", "staticValues", "staticIdentities" })
            if (regenerated.TryGetProperty(property, out JsonElement assumptions) && assumptions.GetArrayLength() != 0)
                throw new InvalidDataException("Full verification version 1 rejects static or initialization state: " + property);
        File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new VerificationSettings(1,
            Path.GetRelativePath(artifact, proof), author, Path.GetRelativePath(artifact, consumer)), Json));
        ContractExportRequest exportRequest = new(export.Signature, artifact, export.ContractConstant, author);
        ContractExportManifest manifest = new(1, implementation, consumer, interfaces, [exportRequest]);
        using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(implementation)));
        PreparedContractExport prepared = PrepareContractExport(manifest, module, exportRequest);
        int slot = binding.GetProperty("slot").GetInt32();
        string destination = "LeanCILFullLibrary" + slot;
        string? transfer = null;
        using Program independent = new() { freshLibrary = true, forceFullVerification = true,
            fullBundleDependencies = [dependency], fullInputRecheck = recheck };
        ExportClosure published = independent.CheckPublishedContractInterfaces(manifest, contract.InterfaceModules, [prepared], staging)[export.ContractConstant];
        if (published.Digest != export.ClosureDigest || published.Kind != export.Kind)
            throw new InvalidDataException("Independent published interface closure mismatch.");
        ConsumerExportAudit audit = new(ExportAuditSource(prepared, export.Kind), (session, proofModule, leanPath) =>
        {
            recheck();
            ExportClosure actual = independent.CheckExportClosure(session, proofModule, export.ContractConstant, leanPath);
            (string statementDigest, string _) = independent.CheckExportStatement(session, proofModule, leanPath);
            if (actual.Digest != export.ClosureDigest || actual.Canonical != published.Canonical || actual.Kind != export.Kind ||
                statementDigest != certification.StatementDigest)
                throw new InvalidDataException("Independent library export closure or canonical statement mismatch.");
            SortedDictionary<string, string> artifacts = FullArtifacts(leanPath);
            transfer = independent.CaptureFullTerms(session, proofModule, destination, contract.InterfaceModules, leanPath);
            RequireFullArtifacts(artifacts);
            recheck();
        });
        ConsumerOutcome outcome = independent.VerifyConsumerRequests(consumer,
            [new(implementation, artifact, proof, ExportTheorem, null, ExportAudit: audit)], null, batch: false)[0];
        if (outcome.Error is not null) System.Runtime.ExceptionServices.ExceptionDispatchInfo.Throw(outcome.Error);
        if (outcome.Report is null || transfer is null) throw new InvalidDataException("Independent library verification did not complete its exact export audit.");
        recheck();
        return new(slot, destination, "LeanCILFullExpected" + slot, digest, export.ContractConstant, export.Kind,
            transfer, File.ReadAllText(Path.Combine(artifact, "Extracted.lean")));
    }

    ConsumerDependency StageFullConsumer(string bundle, ContractBundleManifest inventory, string consumer, string digest,
        InterfaceModule[] interfaces)
    {
        JsonElement originalLock = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Within(bundle, "consumer/lake-manifest.json")));
        JsonElement[] packages = originalLock.GetProperty("packages").EnumerateArray().ToArray();
        if (packages.Length != 1 || packages[0].GetProperty("name").GetString() != "leancil" ||
            packages[0].GetProperty("type").GetString() != "git" ||
            (packages[0].TryGetProperty("subDir", out JsonElement subdirectory) && subdirectory.ValueKind == JsonValueKind.String && subdirectory.GetString() is not ("" or ".")))
            throw new InvalidDataException("Full source bundle version 1 supports the leancil source dependency only.");
        Directory.CreateDirectory(consumer);
        foreach (string relative in inventory.Files.Keys.Where(path => path.StartsWith("consumer/", StringComparison.Ordinal)))
        {
            string local = relative["consumer/".Length..];
            if (local.StartsWith(".lake/", StringComparison.Ordinal) || local is "lakefile.lean" or "lakefile.toml" or "lake-manifest.json") continue;
            string target = Within(consumer, local);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Within(bundle, relative), target);
        }
        string framework = Within(consumer, ".lake/packages/leancil");
        foreach (string path in Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories)
            .Append(At("CIL.lean")).Append(At("lean-toolchain")).Append(At("lakefile.toml")).Append(At("lake-manifest.json")))
        {
            string relative = Path.GetRelativePath(Root, path).Replace('\\', '/');
            string source = Within(bundle, "framework/" + relative);
            if (File.ReadAllBytes(source).AsSpan().SequenceEqual(File.ReadAllBytes(path)) is false)
                throw new InvalidDataException("Full source bundle framework/toolchain differs from the verifier: " + relative);
            string target = Within(framework, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(source, target);
        }
        string[] modules = Directory.EnumerateFiles(consumer, "*.lean", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(consumer, path).Replace('\\', '/')).Where(path => !path.StartsWith(".lake/", StringComparison.Ordinal))
            .Select(path => path[..^5].Replace('/', '.')).Concat(interfaces.Select(module => module.Name))
            .Distinct(StringComparer.Ordinal).ToArray();
        if (modules.Any(module => !ContractInterface.Constant(module) || module == "CIL" || module.StartsWith("CIL.", StringComparison.Ordinal)))
            throw new InvalidDataException("Unsupported full source bundle module layout.");
        File.WriteAllText(Path.Combine(consumer, "lakefile.toml"), "name = \"leancil_full_source\"\n[[require]]\nname = \"leancil\"\npath = \".lake/packages/leancil\"\n" +
            string.Join("", modules.Select(module => "[[lean_lib]]\nname = \"" + module + "\"\n")));
        File.WriteAllText(Path.Combine(consumer, "lake-manifest.json"), JsonSerializer.Serialize(new
        {
            version = "1.2.0", packagesDir = ".lake/packages", lakeDir = ".lake", name = "leancil_full_source", fixedToolchain = false,
            packages = new[] { new { type = "path", name = "leancil", inherited = false, dir = ".lake/packages/leancil" } }
        }));
        return new("leancil", framework, framework, packages[0].GetProperty("rev").GetString()!, "bundle:" + digest);
    }

    string CaptureFullTerms(string session, string proofModule, string destination, InterfaceModule[] interfaces, string leanPath)
    {
        string[] shared = Directory.EnumerateFiles(Path.Combine(Toolchain, "lib/lean"), "*.olean", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(Path.Combine(Toolchain, "lib/lean"), path).Replace('\\', '/')[..^6].Replace('/', '.'))
            .Concat(Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(Root, path).Replace('\\', '/')[..^5].Replace('/', '.')))
            .Concat(["CIL"]).Concat(interfaces.Select(module => module.Name)).Distinct(StringComparer.Ordinal).ToArray();
        string captured = Path.Combine(session, "FullTransfer.source");
        string probe = Path.Combine(session, "LeanCILCaptureFullTerms.lean");
        File.WriteAllText(probe, $$"""
import {{proofModule}}
import ExtractionAudit
import CIL.Interface.FullTransfer
private theorem LeanCILFullCapture.noStaticSites :
    _root_.Extracted.program.all (fun body => body.staticSites.isEmpty) = true := by decide +kernel
run_cmd do
  let shared : Array Lean.Name := ({{JsonSerializer.Serialize(shared)}} : List String).toArray.map String.toName
  let roots : Array Lean.Name := #[`LeanCILExportAudit.certified, `LeanCILExportAudit.closed,
    `LeanCILExportAudit.noImports, ``LeanCILFullCapture.noStaticSites, `ExtractionAudit.valid]
  let source <- match CIL.Interface.FullTransfer.capture (<- Lean.getEnv) shared `{{destination}} roots with
    | .ok source => pure source
    | .error message => throwError "{message}"
  IO.FS.writeFile {{JsonSerializer.Serialize(captured)}} source
""");
        Run([LeanExecutable, probe], session, leanPath, progress: "Capturing actual checked author and extraction kernel terms");
        return File.ReadAllText(captured);
    }

    static string NamespacedExtraction(string source, string name)
    {
        int start = source.IndexOf("\nnamespace Extracted\n", StringComparison.Ordinal);
        if (start < 0 || source.Contains("_root_.Extracted", StringComparison.Ordinal))
            throw new InvalidDataException("Unsupported generated extraction namespace layout for full verification.");
        string header = source[..start];
        if (header.Split('\n').Any(line => line.Length != 0 && !line.StartsWith("import CIL.", StringComparison.Ordinal)))
            throw new InvalidDataException("Unsupported generated extraction import layout for full verification.");
        return header + "\nnamespace " + name + "\n" + source[(start + 1)..] + "\nend " + name + "\n";
    }

    static SortedDictionary<string, string> FullFiles(string directory) => new(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
        .ToDictionary(path => path, Sha), StringComparer.Ordinal);

    static SortedDictionary<string, string> FullArtifacts(string leanPath)
    {
        SortedDictionary<string, string> files = new(StringComparer.Ordinal);
        foreach (string directory in leanPath.Split(Path.PathSeparator).Where(Directory.Exists).Distinct(StringComparer.Ordinal))
            foreach (string path in Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
                .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))) files[path] = Sha(path);
        return files;
    }

    static void RequireFullArtifacts(SortedDictionary<string, string> accepted)
    {
        foreach ((string path, string digest) in accepted)
            if (!File.Exists(path) || Sha(path) != digest) throw new InvalidDataException("Full-verification source or compiled artifact changed: " + path);
    }

    static SortedDictionary<string, string> FullModulePaths(string leanPath)
    {
        SortedDictionary<string, string> modules = new(StringComparer.Ordinal);
        foreach (string root in leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries).Distinct(StringComparer.Ordinal))
        {
            if (!Directory.Exists(root)) continue;
            foreach (string path in Directory.EnumerateFiles(root, "*.olean", SearchOption.AllDirectories))
            {
                string name = ModuleName(Path.GetRelativePath(root, path).Replace('\\', '/'));
                if (!ContractInterface.Constant(name)) continue;
                string absolute = Path.GetFullPath(path);
                if (modules.TryGetValue(name, out string? previous) && previous != absolute)
                    throw new InvalidDataException("Ambiguous full-verification module: " + name);
                modules[name] = absolute;
            }
        }
        return modules;
    }

    static IEnumerable<string> FullModuleArtifactPaths(string leanPath)
    {
        foreach (string root in leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries).Distinct(StringComparer.Ordinal))
            if (Directory.Exists(root))
                foreach (string path in Directory.EnumerateFiles(root, "*", SearchOption.AllDirectories)
                    .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal)))
                    if (ContractInterface.Constant(ModuleName(Path.GetRelativePath(root, path).Replace('\\', '/'))))
                        yield return Path.GetFullPath(path);
    }

    static SortedDictionary<string, string> FullModuleArtifacts(string leanPath) =>
        new(FullModuleArtifactPaths(leanPath).Distinct(StringComparer.Ordinal).ToDictionary(path => path, Sha), StringComparer.Ordinal);

    static void RequireFullModuleArtifactSet(string leanPath, SortedDictionary<string, string> expected)
    {
        foreach (string path in FullModuleArtifactPaths(leanPath))
            if (!expected.ContainsKey(path)) throw new InvalidDataException("Unexpected full-verification caller artifact: " + path);
    }

    static void RequireFullModulePaths(string leanPath, SortedDictionary<string, string> expected)
    {
        SortedDictionary<string, string> current = FullModulePaths(leanPath);
        foreach ((string name, string path) in current)
            if (!expected.TryGetValue(name, out string? previous) || previous != path)
                throw new InvalidDataException("Full-verification module resolution changed: " + name);
        if (current.Count != expected.Count) throw new InvalidDataException("Full-verification module resolution lost a checked module.");
    }

    static void RequireEmptyProducerModules(string staging)
    {
        string? path = FullModuleArtifactPaths(staging).FirstOrDefault();
        if (path is not null)
            throw new InvalidDataException("Unexpected producer staging module: " + ModuleName(Path.GetRelativePath(staging, path).Replace('\\', '/')));
    }

    void CheckFullResolution(string directory, string leanPath, SortedDictionary<string, string> modules)
    {
        string manifest = Path.Combine(directory, "full-module-resolution.json");
        File.WriteAllText(manifest, JsonSerializer.Serialize(modules.Select(pair => new { name = pair.Key, path = pair.Value })));
        string probe = Path.Combine(directory, "FullModuleResolution.lean");
        File.WriteAllText(probe, $$"""
import Lean
private structure ExpectedResolution where
  name : String
  path : String
  deriving Lean.FromJson
run_cmd do
  let expected : Array ExpectedResolution <- IO.ofExcept <|
    (Lean.Json.parse (<- IO.FS.readFile {{JsonSerializer.Serialize(manifest)}})).bind Lean.fromJson?
  for item in expected do
    let path <- Lean.findOLean item.name.toName
    unless path.toString == item.path do throwError "Full-verification resolved module path changed: {item.name}"
""");
        Run([LeanExecutable, probe], directory, leanPath, environment: LeanEnvironment,
            progress: "Checking actual full-verification module resolution");
    }

    string CaptureFullCallerClaim(string session, string module, string theorem, string leanPath)
    {
        string probe = Path.Combine(session, "FullOriginalCallerClaim.lean");
        File.WriteAllText(probe, "import " + module + "\nimport CIL.Interface.Closure\n" + FullClaimSelector(theorem) + """
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let expression <- Lean.Elab.Term.elabTerm (<- `(fullCallerClaim)) none
  let reduced <- withTransparency .all (whnf (<- instantiateMVars expression))
  let canonical <- match _root_.CIL.Interface.canonicalExpression reduced with
    | .ok value => pure value
    | .error message => throwError "{message}"
  IO.println (Json.mkObj [("kind", toJson "full-caller-claim"), ("canonical", toJson canonical)]).compress
""");
        string output = Run([LeanExecutable, probe], session, leanPath, environment: LeanEnvironment,
            progress: "Binding the original checked caller claim");
        return OneExportRecord(output, "kind", "full-caller-claim").GetProperty("canonical").GetString()!;
    }

    static string FullClaimSelector(string theorem) =>
        "private def selectFullCallerClaim {claim : _root_.CIL.Program -> Prop} " +
        "(_given : _root_.CIL.Safety.HoldsGiven _root_.Extracted.program _root_.Extracted.ImportsHold claim) : _root_.CIL.Program -> Prop := claim\n" +
        "private def fullCallerClaim : _root_.CIL.Program -> Prop := selectFullCallerClaim _root_." + theorem + "\n";

    static string FullCompositionSource(string callerModule, string callerTheorem, string originalClaim, IReadOnlyList<FullLibrary> libraries)
    {
        StringBuilder source = new("import " + callerModule + "\nimport CIL.Safety.Linking\nimport CIL.Interface.Closure\n");
        foreach (FullLibrary library in libraries) source.AppendLine("import " + library.Module).AppendLine("import " + library.ExpectedModule);
        source.AppendLine("namespace LeanCILFullComposition\nopen CIL.Safety");
        foreach (FullLibrary library in libraries)
        {
            string index = library.Slot.ToString(System.Globalization.CultureInfo.InvariantCulture);
            string program = library.ExpectedModule + ".Extracted.program";
            string holds = "_root_.CIL.Safety." + (library.Kind == "method" ? "MethodContract" : "OutcomeContract") + ".Holds _root_." + library.Contract;
            source.AppendLine("theorem programIdentity" + index + " : " + library.Module + ".Extracted.program = " + program + " := rfl");
            source.AppendLine("theorem extraction" + index + " : CIL.Extraction.TranslationValid " + library.ExpectedModule + ".Extracted.rawLayouts " +
                library.ExpectedModule + ".Extracted.computedLayouts " + library.ExpectedModule + ".Extracted.methodEvidence " +
                library.ExpectedModule + ".Extracted.imports " + program + " := " + library.ExpectedModule + ".Extracted.translation_valid");
            source.AppendLine("def library" + index + " : Library := { entry := " + library.ExpectedModule + ".Extracted.method0, helpers := " + program + ".drop 1 }");
            source.AppendLine("theorem libraryProgram" + index + " : library" + index + ".program = " + program + " := rfl");
            source.AppendLine("theorem closed" + index + " : Closed library" + index + ".program := Closed.of_check (by decide +kernel)");
            source.AppendLine("theorem holds" + index + " : " + holds + " library" + index + ".program 0 := by\n  simpa only [libraryProgram" + index + ", programIdentity" + index + "] using " + library.Module + ".LeanCILExportAudit.certified");
        }
        source.AppendLine("def libraries : List Library := [" + string.Join(", ", libraries.Select(library => "library" + library.Slot)) + "]");
        source.AppendLine("def specifications : List Relocatable := [" + string.Join(", ", libraries.Select(library =>
            "_root_.CIL.Safety." + (library.Kind == "method" ? "MethodContract" : "OutcomeContract") + ".relocatable _root_." + library.Contract)) + "]");
        source.AppendLine("theorem app_prefix : Links Extracted.program (link Extracted.program libraries) := link_links _ _");
        foreach (FullLibrary library in libraries)
            source.AppendLine("theorem relocation" + library.Slot + " : RelocatesInto library" + library.Slot + ".program " +
                "(link Extracted.program libraries) (linkSlot Extracted.program libraries " + library.Slot + ") := link_relocates Extracted.program libraries (j := " + library.Slot + ") (by decide)");
        source.AppendLine("theorem bridge (linked : CIL.Program) (met : Imports Extracted.program specifications linked) : Extracted.ImportsHold linked := by\n  exact " +
            Conjunction(libraries.Select(library => "met " + library.Slot + " (by decide)").ToArray()));
        source.AppendLine("def discharge {claim : CIL.Program -> Prop} (callerProof : HoldsGiven Extracted.program Extracted.ImportsHold claim) :\n    claim (link Extracted.program libraries) :=\n  composed (callerProof.mono bridge) rfl");
        source.AppendLine(FiniteLibraryProof(libraries.Count, "closed", false));
        source.AppendLine(FiniteLibraryProof(libraries.Count, "holds", true));
        source.AppendLine(FullClaimSelector(callerTheorem));
        source.AppendLine($$"""
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let expression <- Lean.Elab.Term.elabTerm (<- `(fullCallerClaim)) none
  let reduced <- withTransparency .all (whnf (<- instantiateMVars expression))
  let canonical <- match _root_.CIL.Interface.canonicalExpression reduced with
    | .ok value => pure value
    | .error message => throwError "{message}"
  unless canonical == {{JsonSerializer.Serialize(originalClaim)}} do throwError "Full-verification caller claim changed during composition"
""");
        source.AppendLine("theorem certified : fullCallerClaim (link Extracted.program libraries) := discharge _root_." + callerTheorem);
        source.AppendLine("end LeanCILFullComposition");
        return source.ToString();
    }

    static string Conjunction(string[] values) => values.Length == 1 ? values[0] :
        "And.intro (" + values[0] + ") (" + Conjunction(values[1..]) + ")";

    static string FiniteLibraryProof(int count, string theorem, bool specification)
    {
        StringBuilder source = new("    (by\n      intro index bound" + (specification ? " specification" : "") + "\n");
        source.AppendLine("      have selected : " + Alternatives(Enumerable.Range(0, count).Select(index => "index = " + index).ToArray()) +
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
