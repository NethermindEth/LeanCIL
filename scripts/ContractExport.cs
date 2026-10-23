using System.Text.Json;
using Mono.Cecil;
using Nethermind.LeanCIL;

partial class Program
{
    sealed record PreparedContractExport(ContractExportRequest Request, string Proof, string Profile,
        string Identity, string Signature, int ParameterCount, bool ReturnsValue, string Visibility,
        bool Conditional, ContractDependency[] Dependencies, InterfaceModule[] ImportedInterfaces,
        StaticIdentityRecord[] StaticIdentities);
    sealed record ExportClosure(string Contract, string Kind, string Digest, string Canonical);
    sealed record CheckedContractExport(PreparedContractExport Export, ExportClosure Closure,
        string StatementDigest, string Statement, string AuditSource, string AuthorModule);

    const string ExportTheorem = "LeanCILExportAudit.certified";
    const string ContractExportUsage = "Usage: leancil export-contracts manifest.json [--output Lib.leancil.contracts] [--bundle directory]";

    internal static void ExportContracts(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal)) throw new ArgumentException(ContractExportUsage);
        string manifestPath = Path.GetFullPath(args[0]);
        string? output = null;
        string? bundle = null;
        for (int index = 1; index < args.Length; index++)
        {
            string option = args[index];
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException("Missing value for " + option);
            if (option == "--output" && output is null) output = Path.GetFullPath(args[index]);
            else if (option == "--bundle" && bundle is null) bundle = Path.GetFullPath(args[index]);
            else throw new ArgumentException("Unknown or duplicate export option: " + option);
        }
        ContractExportManifest manifest = ContractExportManifest.Read(manifestPath);
        byte[] implementation = File.ReadAllBytes(manifest.Assembly);
        using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(implementation));
        output ??= Path.Combine(Path.GetDirectoryName(manifest.Assembly)!, module.Assembly.Name.Name + ".leancil.contracts");
        if (!output.EndsWith(".leancil.contracts", StringComparison.Ordinal))
            throw new ArgumentException("Contract sidecar output must end in .leancil.contracts.");
        using Program verification = new() { freshLibrary = true };
        verification.ProduceContracts(manifestPath, manifest, module, implementation, output, bundle);
    }

    void ProduceContracts(string manifestPath, ContractExportManifest manifest, ModuleDefinition module,
        byte[] implementation, string output, string? bundle)
    {
        SortedDictionary<string, string> before = ExportInputs(manifestPath, manifest);
        if (before["manifest:" + manifestPath] != manifest.SourceSha256 ||
            before["assembly:" + manifest.Assembly] != ContractInterface.Hash(implementation))
            throw new InvalidDataException("Contract export manifest or implementation changed before its input snapshot.");
        if (before.ContainsKey("consumer:" + output) || output == manifestPath || output == manifest.Assembly ||
            manifest.Interface.Any(source => source.Source == output))
            throw new InvalidDataException("Contract sidecar output overlaps an export input.");
        if (bundle is not null) RequireBundleOutput(manifest, bundle);
        if (module.Assembly.CustomAttributes.Any(attribute => attribute.AttributeType.FullName == "System.Runtime.CompilerServices.ReferenceAssemblyAttribute"))
            throw new InvalidDataException("Cannot certify exports from a reference assembly.");
        PreparedContractExport[] prepared = manifest.Exports.Select(export => PrepareContractExport(manifest, module, export)).ToArray();
        if (prepared.Select(export => (export.Identity, export.Profile)).Distinct().Count() != prepared.Length)
            throw new InvalidDataException("Duplicate contract export method/profile pair.");
        if (prepared.GroupBy(export => export.Identity).Any(group => group.Select(export => export.Request.Contract).Distinct(StringComparer.Ordinal).Count() != 1))
            throw new InvalidDataException("One exported method must name one contract across its profiles.");
        InterfaceModule[] interfaces = manifest.Interface.Select(source => new InterfaceModule(source.Module, ProofRootInterface(manifest, source, before))).ToArray();
        InterfaceModule[] closureInterfaces = MergeContractInterfaces(interfaces, prepared.SelectMany(export => export.ImportedInterfaces));
        ContractDependency[] dependencies = prepared.SelectMany(export => export.Dependencies)
            .GroupBy(dependency => dependency.AssemblyIdentity, StringComparer.Ordinal)
            .OrderBy(group => group.Key, StringComparer.Ordinal).Select(group =>
            {
                if (group.Distinct().Count() != 1)
                    throw new InvalidDataException("Conflicting export dependency requirements: " + group.Key);
                return group.First();
            }).ToArray();
        ContractInterface[] dependencyInterfaces = prepared.SelectMany(export => ImportGraph(export.Request.Artifact)
                .Select(node => ExtractionIdentity.Resolve(export.Request.Artifact, node.GetProperty("sidecarPath").GetString()!)))
            .Distinct(StringComparer.Ordinal).Select(path => ContractInterface.Read(File.ReadAllBytes(path))).ToArray();

        string staging = Path.Combine(Path.GetTempPath(), "leancil-contract-export-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(staging);
        try
        {
            Dictionary<string, ExportClosure> publishedClosures = CheckPublishedContractInterfaces(manifest, closureInterfaces, prepared, staging);
            List<CheckedContractExport> verified = [];
            for (int index = 0; index < prepared.Length; index++)
            {
                PreparedContractExport export = prepared[index];
                ExportClosure published = publishedClosures[export.Request.Contract];
                string audit = ExportAuditSource(export, published.Kind);
                CheckedContractExport? checkedExport = null;
                ConsumerExportAudit specification = new(audit, (session, proofModule, leanPath) =>
                {
                    ExportClosure actual = CheckExportClosure(session, proofModule, export.Request.Contract, leanPath);
                    if (actual.Digest != published.Digest || actual.Kind != published.Kind || actual.Canonical != published.Canonical)
                        throw new InvalidDataException("Export contract differs from its published interface closure: " + export.Request.Contract);
                    (string digest, string statement) = CheckExportStatement(session, proofModule, leanPath);
                    checkedExport = new(export, actual, digest, statement, audit, proofModule + "Author");
                });
                ConsumerRequest request = new(manifest.Assembly, export.Request.Artifact, export.Proof, ExportTheorem, null,
                    ExportAudit: specification);
                ConsumerOutcome outcome = VerifyConsumerRequests(manifest.ProofRoot, [request], null, batch: false)[0];
                if (outcome.Error is not null) System.Runtime.ExceptionServices.ExceptionDispatchInfo.Throw(outcome.Error);
                if (outcome.Report is null || checkedExport is null)
                    throw new InvalidDataException("Contract export did not finish its exact theorem audit and replay.");
                verified.Add(checkedExport);
            }
            if (!Same(before, ExportInputs(manifestPath, manifest))) throw new InvalidDataException("Contract export inputs changed during verification.");
            string implementationHash = ContractInterface.Hash(implementation);
            ContractExport[] exports = verified.GroupBy(result => result.Export.Identity).OrderBy(group => group.Key, StringComparer.Ordinal)
                .Select(group => new ContractExport(group.Key, group.First().Export.Signature, group.First().Export.ParameterCount,
                    false, group.First().Export.ReturnsValue, group.First().Export.Visibility, group.First().Export.Request.Contract,
                    group.First().Closure.Digest, group.Select(result => result.Export.Profile).Order(StringComparer.Ordinal).ToArray(),
                    group.First().Closure.Kind)).ToArray();
            string target = module.Assembly.CustomAttributes.Single(attribute => attribute.AttributeType.FullName ==
                "System.Runtime.Versioning.TargetFrameworkAttribute").ConstructorArguments.Single().Value as string
                ?? throw new InvalidDataException("Missing target framework.");
            ContractInterface sidecar = new(1, 1, 1, ContractInterface.CurrentFrameworkKey(), module.Assembly.Name.FullName,
                module.Mvid, target, implementationHash, false, interfaces, "", exports, [], dependencies);
            sidecar = sidecar with { InterfaceDigest = sidecar.ComputeInterfaceDigest() };
            sidecar = AddExportCertifications(sidecar, verified);
            ContractDependencyGraph.Validate(dependencyInterfaces.Where(contract => contract.AssemblyIdentity != sidecar.AssemblyIdentity).Append(sidecar));
            if (!Same(before, ExportInputs(manifestPath, manifest))) throw new InvalidDataException("Contract export inputs changed before publication.");

            if (bundle is not null)
            {
                string digest = PublishContractSources(bundle, staging, manifestPath, manifest, before, verified);
                sidecar = sidecar with { FullVerificationLocator = Path.Combine(Path.GetFullPath(bundle), digest).Replace('\\', '/') };
            }
            if (!Same(before, ExportInputs(manifestPath, manifest))) throw new InvalidDataException("Contract export inputs changed before publication.");
            byte[] sidecarBytes = JsonSerializer.SerializeToUtf8Bytes(sidecar, ContractInterface.Json);
            ContractInterface.Read(sidecarBytes);
            PublishContractSidecar(output, sidecarBytes);
            Console.WriteLine("Exported verified contracts: " + CliPaths.Display(output));
            Console.WriteLine("  Implementation SHA-256: " + implementationHash);
            Console.WriteLine("  Interface digest: " + sidecar.InterfaceDigest);
            Console.WriteLine("  Exports: " + exports.Length);
        }
        finally
        {
            try { Directory.Delete(staging, true); }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException)
            {
                Console.Error.WriteLine("warning: contract export staging cleanup failed: " + error.Message);
            }
        }
    }

    static SortedDictionary<string, string> ExportInputs(string manifestPath, ContractExportManifest manifest)
    {
        SortedDictionary<string, string> inputs = ConsumerSnapshot(manifest.ProofRoot, null);
        inputs["manifest:" + manifestPath] = Sha(manifestPath);
        inputs["assembly:" + manifest.Assembly] = Sha(manifest.Assembly);
        inputs["extractor"] = Sha(ExtractorPath);
        string pdb = Path.ChangeExtension(manifest.Assembly, ".pdb");
        inputs["pdb:" + pdb] = File.Exists(pdb) ? Sha(pdb) : "absent";
        foreach (ContractSource source in manifest.Interface) inputs["interface:" + source.Source] = Sha(source.Source);
        HashSet<string> dependencyPaths = new(StringComparer.Ordinal);
        foreach (string path in FrameworkBundleSources()) inputs["framework:" + path] = Sha(path);

        foreach (ContractExportRequest export in manifest.Exports)
        {
            foreach (string file in new[] { "identity.json", "verification.json", "Extracted.lean" })
                inputs["artifact:" + Path.Combine(export.Artifact, file)] = Sha(Path.Combine(export.Artifact, file));
            JsonElement extraction = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(export.Artifact, "identity.json")));
            if (extraction.TryGetProperty("importGraph", out JsonElement graph))
                foreach (JsonElement node in graph.EnumerateArray())
                    foreach (string field in new[] { "sidecarPath", "implementationPath" })
                    {
                        string path = node.GetProperty(field).GetString()!;
                        dependencyPaths.Add(ExtractionIdentity.Resolve(export.Artifact, path));
                    }
        }
        foreach (string path in dependencyPaths) inputs["dependency:" + path] = Sha(path);
        return inputs;
    }

    static IEnumerable<string> FrameworkBundleSources() => Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories)
        .Append(At("CIL.lean")).Append(At("lean-toolchain")).Append(At("lakefile.toml")).Append(At("lake-manifest.json"));

    static string? SnapshotSource(SortedDictionary<string, string> snapshot, string path)
    {
        StringComparison comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        path = Path.GetFullPath(path);
        return snapshot.Where(pair => pair.Key.StartsWith("consumer:", StringComparison.Ordinal) &&
            Path.GetFullPath(pair.Key["consumer:".Length..]).Equals(path, comparison)).Select(pair => pair.Value).FirstOrDefault();
    }

    // The published text is the proofRoot module the export proof compiled against, byte for byte.
    static string ProofRootInterface(ContractExportManifest manifest, ContractSource source, SortedDictionary<string, string> before)
    {
        string module = Path.Combine(manifest.ProofRoot, source.Module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
        byte[] bytes = File.ReadAllBytes(source.Source);
        string published = ContractInterface.Hash(bytes);
        if (published != before["interface:" + source.Source] || SnapshotSource(before, module) != published)
            throw new InvalidDataException("Published contract interface source must be byte-identical to its proofRoot module: " + source.Module);
        using StreamReader reader = new(new MemoryStream(bytes));
        return reader.ReadToEnd();
    }

    static PreparedContractExport PrepareContractExport(ContractExportManifest manifest, ModuleDefinition module, ContractExportRequest request)
    {
        Run(["dotnet", ExtractorPath, "check", request.Artifact, "--assembly-path", manifest.Assembly]);
        ExtractionIdentity extraction = ExtractionIdentity.Read(request.Artifact);
        JsonElement identity = extraction.Root;
        MethodDefinition method = MethodSelector.Resolve(module, request.Method);
        FeatureProfile profile = identity.GetProperty("profile").Deserialize<FeatureProfile>() ?? throw new InvalidDataException("Missing export profile.");
        if (FeatureProfile.Select(profile.Name) != profile) throw new InvalidDataException("Contract exports require an exact built-in profile.");
        if (identity.GetProperty("entry").GetString() != method.FullName || identity.GetProperty("assemblyIdentity").GetString() != module.Assembly.Name.FullName ||
            identity.GetProperty("assemblySha256").GetString() != Sha(manifest.Assembly))
            throw new InvalidDataException("Contract export method/entry or implementation differs from its selected artifact.");
        foreach (string property in new[] { "initializedTypes", "staticValues" })
            if (identity.TryGetProperty(property, out JsonElement assumptions) && assumptions.GetArrayLength() != 0)
                throw new InvalidDataException("Contract export rejects static/initialization assumptions: " + property);
        if (!method.IsStatic || method.IsVirtual || method.IsPInvokeImpl || method.IsConstructor || method.HasGenericParameters || method.DeclaringType.HasGenericParameters ||
            !(method.IsPublic || method.IsFamily || method.IsFamilyOrAssembly))
            throw new InvalidDataException("Contract exports require a public or protected static, non-virtual, non-generic method.");
        VerificationSettings settings = JsonSerializer.Deserialize<VerificationSettings>(File.ReadAllText(Path.Combine(request.Artifact, "verification.json")),
            new JsonSerializerOptions { UnmappedMemberHandling = System.Text.Json.Serialization.JsonUnmappedMemberHandling.Disallow })
            ?? throw new InvalidDataException("Missing export verification settings.");
        if (settings.schema != 1 || string.IsNullOrWhiteSpace(settings.proof)) throw new InvalidDataException("Invalid export verification settings.");
        if (settings.proofRoot is not null && Path.GetFullPath(settings.proofRoot, request.Artifact) != manifest.ProofRoot)
            throw new InvalidDataException("Export artifact proofRoot differs from the producer manifest.");
        string proof = Path.GetFullPath(settings.proof, request.Artifact);
        Within(manifest.ProofRoot, Path.GetRelativePath(manifest.ProofRoot, proof));
        StaticIdentityRecord[] statics = identity.GetProperty("staticIdentities").Deserialize<StaticIdentityRecord[]>(ContractInterface.Json)
            ?? throw new InvalidDataException("Missing export static identities.");
        StaticIdentity.Validate(statics);
        StaticIdentity.ValidateFields(statics, module);
        JsonElement[] imports = identity.TryGetProperty("imports", out JsonElement imported) ? imported.EnumerateArray().ToArray() : [];
        ContractDependency[] dependencies = imports.Select(binding => new ContractDependency(
            binding.GetProperty("identity").GetString()!.Split("::", 2)[0],
            binding.GetProperty("implementationSha256").GetString()!, binding.GetProperty("interfaceDigest").GetString()!))
            .Distinct().OrderBy(dependency => dependency.AssemblyIdentity, StringComparer.Ordinal).ToArray();
        InterfaceModule[] importedInterfaces = extraction.Sources.Where(pair => pair.Key != "ExtractedImports")
            .Select(pair => new InterfaceModule(pair.Key, pair.Value)).ToArray();
        return new(request, proof, profile.Name, module.Assembly.Name.FullName + "::" + method.FullName, method.FullName,
            method.Parameters.Count, method.ReturnType.MetadataType != MetadataType.Void, method.IsPublic ? "public" : "protected",
            imports.Length != 0, dependencies, importedInterfaces, statics);
    }

    static InterfaceModule[] MergeContractInterfaces(InterfaceModule[] own, IEnumerable<InterfaceModule> imported)
    {
        SortedDictionary<string, string> modules = new(StringComparer.Ordinal);
        foreach (InterfaceModule module in own.Concat(imported))
        {
            if (modules.TryGetValue(module.Name, out string? previous) && previous != module.Source)
                throw new InvalidDataException("Conflicting published dependency interface module: " + module.Name);
            modules[module.Name] = module.Source;
        }
        return modules.Select(pair => new InterfaceModule(pair.Key, pair.Value)).ToArray();
    }

    static string ExportAuditSource(PreparedContractExport export, string kind)
    {
        string holds = kind switch
        {
            "method" => "_root_.CIL.Safety.MethodContract.Holds",
            "outcome" => "_root_.CIL.Safety.OutcomeContract.Holds",
            _ => throw new InvalidDataException("Export constant is not a MethodContract or OutcomeContract.")
        };
        string statement = export.Conditional
            ? "_root_.CIL.Safety.HoldsGiven _root_.Extracted.program _root_.Extracted.ImportsHold " +
                "(fun linked => " + holds + " _root_." + export.Request.Contract + " linked 0)"
            : holds + " _root_." + export.Request.Contract + " _root_.Extracted.program 0";
        string closure = export.Conditional ? $$"""
theorem LeanCILExportAudit.relocated {completion target : _root_.CIL.Program} {f : Nat -> Nat}
    (linkedPrefix : _root_.CIL.Safety.Links _root_.Extracted.program completion)
    (met : _root_.Extracted.ImportsHold completion) (closed : _root_.CIL.Safety.Closed completion)
    (relocates : _root_.CIL.Safety.RelocatesInto completion target f) :
    {{holds}} _root_.{{export.Request.Contract}} target (f 0) :=
  _root_.CIL.Safety.{{(kind == "method" ? "MethodContract" : "OutcomeContract")}}.relocateGiven
    LeanCILExportAudit.certified linkedPrefix met closed relocates
""" : """
theorem LeanCILExportAudit.closed : _root_.CIL.Safety.Closed _root_.Extracted.program :=
  _root_.CIL.Safety.Closed.of_check (by decide +kernel)
theorem LeanCILExportAudit.noImports : _root_.Extracted.imports = [] := rfl
""";
        string statics = "[" + string.Join(", ", export.StaticIdentities.Select(identity =>
            $"({identity.Identity}, {JsonSerializer.Serialize(identity.AssemblyIdentity)}, {JsonSerializer.Serialize(identity.FieldName)})")) + "]";
        return $$"""
import Lean
import CIL.Safety.Linking
import CIL.Safety.OutcomeContract
import CIL.Interface.Closure
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let contract <- getConstInfo `{{export.Request.Contract}}
  unless contract.levelParams.isEmpty do throwError "Export contracts must be closed constants"
  let contractType <- whnf contract.type
  unless contractType.getAppFn.isConstOf ``CIL.Safety.{{(kind == "method" ? "MethodContract" : "OutcomeContract")}} do
    throwError "Export must have the canonical contract type"
  let .thmInfo author <- getConstInfo `{{export.Request.Theorem}} | throwError "Expected an export theorem"
  unless author.levelParams.isEmpty do throwError "Export theorem must have a closed statement"
  let expected <- Lean.Elab.Term.elabType (<- `({{statement}}))
  unless <- isDefEq author.type expected do throwError "Export theorem does not have the exact canonical Holds statement"
theorem LeanCILExportAudit.certified : {{statement}} :=
  _root_.{{export.Request.Theorem}}
{{closure}}
theorem LeanCILExportAudit.staticIdentities :
    let actual : List (Nat × String × String) := _root_.Extracted.program.flatMap fun body =>
      body.staticSites.map fun site => (site.2.identity, site.2.assemblyIdentity, site.2.fieldName)
    let expected : List (Nat × String × String) := {{statics}}
    actual.all (fun identity => expected.contains identity) && expected.all (fun identity => actual.contains identity) = true := by decide +kernel
""";
    }

    Dictionary<string, ExportClosure> CheckPublishedContractInterfaces(ContractExportManifest manifest,
        InterfaceModule[] interfaces, PreparedContractExport[] exports, string staging)
    {
        string certified = Library(Inputs(exports[0].Proof));
        string isolated = Path.Combine(staging, "interface");
        Directory.CreateDirectory(isolated);
        CopyTree(Path.Combine(certified, "CIL"), Path.Combine(isolated, "CIL"));
        foreach (string file in new[] { "CIL.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain" })
            File.Copy(Path.Combine(certified, file), Path.Combine(isolated, file));
        string baseBuild = Path.Combine(certified, ".lake", "build");
        foreach (string path in Directory.EnumerateFiles(baseBuild, "*", SearchOption.AllDirectories))
        {
            string relative = Path.GetRelativePath(baseBuild, path).Replace('\\', '/');
            if (!new[] { "lib/lean/CIL/", "lib/lean/CIL.", "ir/CIL/", "ir/CIL." }
                .Any(prefix => relative.StartsWith(prefix, StringComparison.Ordinal))) continue;
            string target = Path.Combine(isolated, ".lake", "build", relative);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(path, target);
        }
        SortedDictionary<string, string> baseModules = ModuleArtifacts(isolated);
        foreach (InterfaceModule source in interfaces)
        {
            string path = Path.Combine(isolated, source.Name.Replace('.', Path.DirectorySeparatorChar) + ".lean");
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, source.Source);
            AddConsumerLibrary(isolated, source.Name);
        }
        Run(["lake", "build", .. interfaces.Select(source => "+" + source.Name + ":olean")], isolated,
            progress: "Checking published contract interface sources without implementation proofs");
        (string[] _, string leanPath) = ConsumerImportDirectories(isolated);
        SortedDictionary<string, string> built = ModuleArtifacts(isolated);
        foreach ((string path, string hash) in baseModules)
            if (!built.TryGetValue(path, out string? current) || current != hash)
                throw new InvalidDataException("Contract interface changed a certified framework artifact: " + path);
        if (built.Keys.Any(path => (ModuleName(path) == "CIL" || ModuleName(path).StartsWith("CIL.", StringComparison.Ordinal)) &&
            !baseModules.ContainsKey(path)))
            throw new InvalidDataException("Contract interface produced an unrecorded framework artifact.");
        string[] modules = built.Keys.Select(ModuleName).Distinct(StringComparer.Ordinal)
            .Where(name => name != "CIL" && !name.StartsWith("CIL.", StringComparison.Ordinal)).ToArray();
        if (modules.Any(name => !interfaces.Any(source => source.Name == name)))
            throw new InvalidDataException("Contract interface produced an undeclared module.");
        Dictionary<string, string> failures = ReplayConsumerModules(isolated, modules, leanPath);
        if (failures.Count != 0) throw new InvalidDataException("Kernel replay rejected the published interface: " + string.Join(", ", failures.Keys));
        CheckPublishedInterfaceDeclarations(isolated, interfaces.Select(source => source.Name).ToArray(), leanPath);
        Dictionary<string, ExportClosure> closures = new(StringComparer.Ordinal);
        string imports = string.Join("\n", interfaces.Select(source => "import " + source.Name));
        foreach (string contract in exports.Select(export => export.Request.Contract).Distinct(StringComparer.Ordinal))
            closures[contract] = CheckExportClosure(isolated, imports, contract, leanPath, importsAreSource: true);
        return closures;
    }

    void CheckPublishedInterfaceDeclarations(string session, string[] modules, string leanPath)
    {
        string path = Path.Combine(session, "LeanCILExportInterfaceProbe.lean");
        File.WriteAllText(path, string.Join("\n", modules.Select(module => "import " + module)) + $$"""

import CIL.Interface.Closure
open Lean Elab Command in
run_cmd do
  match CIL.Interface.validateInterfaceDeclarations (<- getEnv) #[{{string.Join(", ", modules.Select(module => "`" + module))}}] with
  | .ok () => pure ()
  | .error error => throwError "{error}"
""");
        Run([LeanExecutable, path], session, leanPath, environment: LeanEnvironment,
            progress: "Rejecting unpublished assumptions in contract interface modules");
    }

    ExportClosure CheckExportClosure(string session, string import, string contract, string leanPath, bool importsAreSource = false)
    {
        string path = Path.Combine(session, "LeanCILExportClosureProbe.lean");
        string imports = importsAreSource ? import : "import " + import;
        File.WriteAllText(path, imports + "\nimport CIL.Interface.Closure\n#leancil_contract_closure " + contract + "\n");
        string output = Run([LeanExecutable, path], session, leanPath, environment: LeanEnvironment,
            progress: "Auditing export contract closure: " + contract);
        JsonElement record = OneExportRecord(output, "constant", contract);
        string kind = record.GetProperty("kind").GetString() ?? "";
        string canonical = record.GetProperty("canonical").GetString() ?? throw new InvalidDataException("Missing canonical contract closure.");
        if (kind is not ("method" or "outcome") || canonical.Length == 0)
            throw new InvalidDataException("Invalid canonical export contract closure.");
        return new(contract, kind, ContentKey(canonical), canonical);
    }

    (string Digest, string Statement) CheckExportStatement(string session, string proofModule, string leanPath)
    {
        string path = Path.Combine(session, "LeanCILExportStatementProbe.lean");
        File.WriteAllText(path, $$"""
import {{proofModule}}
import CIL.Interface.Closure
set_option pp.fullNames true
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let .thmInfo info <- getConstInfo `{{ExportTheorem}} | throwError "Expected a checked export theorem"
  let canonical <- match CIL.Interface.canonicalExpression info.type with
    | .ok value => pure value
    | .error error => throwError "{error}"
  let statement := toString (<- ppExpr info.type)
  IO.println (Json.mkObj [("theorem", toJson "{{ExportTheorem}}"),
    ("canonical", toJson canonical), ("statement", toJson statement)]).compress
""");
        string output = Run([LeanExecutable, path], session, leanPath, environment: LeanEnvironment,
            progress: "Auditing the exact export statement");
        JsonElement record = OneExportRecord(output, "theorem", ExportTheorem);
        string canonical = record.GetProperty("canonical").GetString() ?? throw new InvalidDataException("Missing canonical export statement.");
        string statement = record.GetProperty("statement").GetString() ?? throw new InvalidDataException("Missing checked export statement.");
        if (canonical.Length == 0 || statement.Length == 0) throw new InvalidDataException("Empty export statement audit.");
        return (ContentKey(canonical), statement);
    }

    static JsonElement OneExportRecord(string output, string field, string expected)
    {
        List<JsonElement> records = [];
        foreach (string line in output.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
        {
            if (!line.StartsWith('{')) continue;
            JsonElement record = JsonSerializer.Deserialize<JsonElement>(line);
            if (record.TryGetProperty(field, out JsonElement value) && value.GetString() == expected) records.Add(record);
        }
        return records.Count == 1 ? records[0] : throw new InvalidDataException("Missing or ambiguous export audit JSON for " + expected);
    }

    static ContractInterface AddExportCertifications(ContractInterface sidecar, IReadOnlyList<CheckedContractExport> exports) =>
        sidecar with
        {
            Certifications = exports.OrderBy(result => result.Export.Identity, StringComparer.Ordinal)
                .ThenBy(result => result.Export.Profile, StringComparer.Ordinal)
                .Select(result => new ContractCertification(result.Export.Identity, result.Export.Profile, sidecar.ImplementationSha256,
                    sidecar.InterfaceDigest, result.Closure.Digest, ExportTheorem, result.Statement, result.StatementDigest,
                    result.Export.StaticIdentities)).ToArray()
        };

    static void PublishContractSidecar(string output, byte[] bytes)
    {
        Directory.CreateDirectory(Path.GetDirectoryName(output)!);
        string staging = output + ".staging-" + Guid.NewGuid().ToString("N");
        try
        {
            File.WriteAllBytes(staging, bytes);
            File.Move(staging, output, true);
        }
        finally { File.Delete(staging); }
    }

    static void RequireBundleOutput(ContractExportManifest manifest, string bundle)
    {
        foreach (string source in new[] { manifest.ProofRoot }.Concat(manifest.Exports.Select(export => export.Artifact)))
        {
            string relative = Path.GetRelativePath(source, bundle);
            if (!Path.IsPathRooted(relative) && relative != ".." && !relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                throw new InvalidDataException("Contract bundle output must be outside proof sources and extraction artifacts.");
        }
    }

    static string PublishContractSources(string bundle, string staging, string manifestPath, ContractExportManifest manifest,
        SortedDictionary<string, string> snapshot, IReadOnlyList<CheckedContractExport> verified)
    {
        // Every bundled file must still hash to the bytes the export audited.
        SortedDictionary<string, string> sources = new(StringComparer.Ordinal) { ["producer/manifest.json"] = manifestPath };
        SortedDictionary<string, string> expected = new(StringComparer.Ordinal) { ["producer/manifest.json"] = snapshot["manifest:" + manifestPath] };
        foreach (string key in snapshot.Keys.Where(key => key.StartsWith("consumer:", StringComparison.Ordinal)))
        {
            string path = key["consumer:".Length..];
            string relative = Path.GetRelativePath(manifest.ProofRoot, path).Replace('\\', '/');
            // The framework package duplicates framework/, which the bundle already pins.
            if (relative.StartsWith(".lake/packages/leancil/", StringComparison.Ordinal)) continue;
            sources["consumer/" + relative] = path;
            expected["consumer/" + relative] = snapshot[key];
        }
        foreach (ContractSource source in manifest.Interface)
        {
            sources["interface/" + source.Module.Replace('.', '/') + ".lean"] = source.Source;
            expected["interface/" + source.Module.Replace('.', '/') + ".lean"] = snapshot["interface:" + source.Source];
        }
        foreach (string path in FrameworkBundleSources())
        {
            sources["framework/" + Path.GetRelativePath(Root, path).Replace('\\', '/')] = path;
            expected["framework/" + Path.GetRelativePath(Root, path).Replace('\\', '/')] = snapshot["framework:" + path];
        }
        for (int index = 0; index < verified.Count; index++)
        {
            CheckedContractExport result = verified[index];
            string prefix = "exports/" + index + "/";
            foreach (string file in new[] { "Extracted.lean", "identity.json", "verification.json" })
            {
                sources[prefix + file] = Path.Combine(result.Export.Request.Artifact, file);
                expected[prefix + file] = snapshot["artifact:" + Path.Combine(result.Export.Request.Artifact, file)];
            }
            string auditPath = Path.Combine(staging, "ExportAudit" + index + ".lean");
            File.WriteAllText(auditPath, "import " + result.AuthorModule + "\n" + result.AuditSource);
            sources[prefix + "ExportAudit.lean"] = auditPath;
            expected[prefix + "ExportAudit.lean"] = Sha(auditPath);
            sources[prefix + result.AuthorModule + ".lean"] = result.Export.Proof;
            expected[prefix + result.AuthorModule + ".lean"] = SnapshotSource(snapshot, result.Export.Proof)
                ?? throw new InvalidDataException("Export proof is outside the proof snapshot: " + result.Export.Proof);
        }
        string revision = snapshot.TryGetValue("revision:leancil", out string? pinned) ? pinned.ToLowerInvariant()
            : throw new InvalidDataException("Contract bundles require a proofRoot pinned to a leancil revision.");
        JsonElement bindings = JsonSerializer.SerializeToElement(verified.Select(result => new
        {
            result.Export.Identity, result.Export.Profile, result.Export.Request.Contract, result.Export.Request.Theorem,
            result.Closure.Digest, result.StatementDigest, result.Statement
        }).ToArray(), ContractExportManifest.Json);
        return ContractSourceBundle.Publish(bundle, sources, expected, bindings, ContractInterface.CurrentFrameworkKey(), revision);
    }
}
