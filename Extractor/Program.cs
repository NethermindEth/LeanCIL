using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static partial class Program
{
    const string Usage = "Usage: leancil list assembly.dll\n       leancil templates output-directory extraction-directory...\n       leancil lint-exceptions output-directory --documentation assembly.xml\n       leancil extract assembly.dll '[return-type ]Type::Method(parameter-types)' output-directory [profile|@profile.json] [--assembly 'assembly name or full identity'] [--type-argument System.UInt64]... [--assume-initialized Namespace.Type]... [--import Lib.leancil.contracts] [--import-implementation Lib=path] [--import-sha256 Lib=hex] [--import-interface-sha256 Lib=hex]\n       leancil export-contracts manifest.json [--output Lib.leancil.contracts] [--bundle directory]\n       leancil workspace assembly.dll method --profile profile --proof proof.lean [--proof-root package-directory] [--output workspace-directory]\n       leancil blockers assembly.dll --manifest manifest.json [--output blockers.json] [--assembly 'assembly name or full identity']\n       leancil check output-directory [--assembly-path assembly.dll] [--assembly 'assembly name or full identity']\n       leancil verify output-directory [--proof proof.lean] [--theorem name] [--fresh] [--rebuild-library] [--proof-root package-directory] [--force-full-verify] [--full-artifact Lib=directory]...\n       leancil verify-batch requests.json [--fresh] [--rebuild-library] [--parallel count] [--results results.json]\n       leancil audit-library --project package-directory --module M... --prefix P... [--axioms a,b,c] [--results results.json]";

    internal static int CheckExtraction(string output) => Main(["check", output]);

    /// <summary>Runs <c>extract</c> or <c>check</c> in this process without printing its report;
    /// a rejection throws instead of returning an exit code.</summary>
    internal static void RunQuietly(string[] args)
    {
        if (args is not ["extract" or "check", ..]) throw new ArgumentException(Usage);
        Run(args, report: TextWriter.Null, rethrow: true);
    }

    static int Main(string[] args) => Run(args);

    static int Run(string[] args, ExtractionBatch? batch = null,
        Action<TemplateEmitter.Variant>? checkedTemplate = null, TextWriter? report = null, bool rethrow = false)
    {
        report ??= Console.Out;
        if (args.Length == 0 || args is ["--help"] or ["-h"])
        {
            Console.WriteLine(Usage + "\n       " + ImportResolver.Usage["Usage: ".Length..]);
            return 0;
        }

        // Extraction is deterministic and never loads or executes the input assembly.
        var stage = "arguments";
        try
        {
            if (args[0] == "generated-extraction-batch")
            {
                stage = "extraction batch";
                return RunExtractionBatch(args[1..]);
            }
            if (args[0] == "resolve-imports")
            {
                stage = "import resolution";
                return ImportResolver.Run(args[1..]);
            }
            if (args[0] == "workspace")
            {
                stage = "editor workspace";
                global::Program.CreateProofWorkspace(args[1..]);
                return 0;
            }
            if (args[0] == "templates")
            {
                stage = "template generation";
                TemplateEmitter.Run(args[1..], ReadTemplate);
                return 0;
            }
            if (args[0] == "list")
            {
                if (args.Length != 2)
                    throw new ArgumentException("Usage: leancil list assembly.dll");
                stage = "assembly loading";
                using var listing = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(args[1])));
                var signatures = listing.GetTypes().SelectMany(type => type.Methods)
                    .Select(method => method.FullName).Order(StringComparer.Ordinal).ToArray();
                Console.WriteLine($"Methods in {listing.Assembly?.Name.FullName ?? listing.Name} ({signatures.Length}):");
                foreach (var signature in signatures)
                    Console.WriteLine(signature);
                Console.WriteLine("Discovery only: listing does not establish support. Use extract to validate the method and its reachable dependencies.");
                return 0;
            }
            if (args[0] == "lint-exceptions")
            {
                stage = "exception documentation lint";
                return ExceptionLint.Run(args[1..]);
            }
            if (args[0] == "blockers")
            {
                stage = "admission report";
                return Blockers.Run(args[1..]);
            }
            if (args[0] == "export-contracts")
            {
                stage = "contract export";
                global::Program.ExportContracts(args[1..]);
                return 0;
            }
            if (args[0] == "verify-batch")
            {
                stage = "proof selection";
                return global::Program.VerifyBatch(args[1..]);
            }
            if (args[0] == "audit-library")
            {
                stage = "library audit";
                return global::Program.AuditLibrary(args[1..]);
            }
            if (args[0] == "verify")
            {
                global::Program.VerifyArtifacts(args[1..]);
                return 0;
            }
            if (args[0] is not ("extract" or "check"))
                throw new ArgumentException(Usage);
            var positional = new List<string>();
            string? expectedAssembly = null;
            string? assemblyOverride = null;
            List<string> importPaths = [];
            List<string> entryTypeArguments = [];
            Dictionary<string, string> implementationPaths = new(StringComparer.Ordinal);
            Dictionary<string, string> importHashes = new(StringComparer.Ordinal);
            Dictionary<string, string> interfaceHashes = new(StringComparer.Ordinal);
            var initializedTypes = new SortedSet<string>(StringComparer.Ordinal);
            for (var index = 1; index < args.Length; index++)
            {
                if (args[index] is "--import" or "--import-implementation" or "--import-sha256" or "--import-interface-sha256")
                {
                    string option = args[index];
                    if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
                        throw new ArgumentException(option + " requires a value.");
                    if (option == "--import") importPaths.Add(Path.GetFullPath(args[index]));
                    else
                    {
                        int separator = args[index].IndexOf('=');
                        if (separator < 1 || separator == args[index].Length - 1)
                            throw new ArgumentException(option + " requires Lib=<value>.");
                        Dictionary<string, string> selected = option == "--import-sha256" ? importHashes :
                            option == "--import-interface-sha256" ? interfaceHashes : implementationPaths;
                        string value = args[index][(separator + 1)..];
                        if (!selected.TryAdd(args[index][..separator], selected == implementationPaths ? value : value.ToLowerInvariant()))
                            throw new ArgumentException("Duplicate " + option + " assembly.");
                    }
                }
                else if (args[index] == "--type-argument")
                {
                    if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
                        throw new ArgumentException("--type-argument requires a closed primitive full type name.");
                    entryTypeArguments.Add(args[index]);
                }
                else if (args[index] == "--assume-initialized")
                {
                    if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
                        throw new ArgumentException("--assume-initialized requires a fully qualified type name.");
                    if (!initializedTypes.Add(args[index]))
                        throw new ArgumentException("Duplicate initialization assumption: " + args[index]);
                }
                else if (args[index] == "--assembly")
                {
                    if (expectedAssembly is not null)
                        throw new ArgumentException("Duplicate --assembly option.");
                    if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
                        throw new ArgumentException("--assembly requires an assembly name or full identity.");
                    expectedAssembly = args[index];
                }
                else if (args[index] == "--assembly-path")
                {
                    if (assemblyOverride is not null)
                        throw new ArgumentException("Duplicate --assembly-path option.");
                    if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
                        throw new ArgumentException("--assembly-path requires a DLL path.");
                    assemblyOverride = args[index];
                }
                else if (args[index].StartsWith("--", StringComparison.Ordinal))
                    throw new ArgumentException($"Unknown option: {args[index]}\n{Usage}");
                else
                    positional.Add(args[index]);
            }
            var recordedCheck = args[0] == "check" && positional.Count == 1;
            if ((!recordedCheck && positional.Count is < 3 or > 4) || (assemblyOverride is not null && !recordedCheck))
                throw new ArgumentException(Usage);

            var output = Path.GetFullPath(recordedCheck ? positional[0] : positional[2]);
            var identityPath = Path.Combine(output, "identity.json");
            stage = "extraction integrity";
            JsonElement? recorded = args[0] == "check"
                ? JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(identityPath)) : null;
            if (recorded is { } assumptions && assumptions.TryGetProperty("initializedTypes", out var recordedTypes))
            {
                var names = recordedTypes.Deserialize<string[]>() ?? throw new InvalidDataException("Missing initialization assumptions.");
                if (initializedTypes.Count > 0 && !initializedTypes.SetEquals(names))
                    throw new InvalidDataException("Initialization assumptions differ from the recorded extraction.");
                initializedTypes.UnionWith(names);
            }
            if (recorded is { } existing && existing.GetProperty("schema").GetInt32() != 3)
                throw new InvalidDataException("Unsupported extraction manifest schema; run leancil extract again.");
            var assemblyPath = recordedCheck
                ? assemblyOverride ?? Path.GetFullPath(recorded!.Value.GetProperty("assemblyPath").GetString()!, output)
                : positional[0];
            string entry = recordedCheck ? (recorded!.Value.TryGetProperty("entryDefinition", out JsonElement definition) ?
                definition.GetString()! : recorded.Value.GetProperty("entry").GetString()!) : positional[1];
            if (recorded is { } priorSelection && priorSelection.TryGetProperty("entryTypeArguments", out JsonElement savedArguments))
            {
                string[] saved = savedArguments.Deserialize<string[]>() ?? throw new InvalidDataException("Missing closed entry arguments.");
                if (entryTypeArguments.Count > 0 && !entryTypeArguments.SequenceEqual(saved, StringComparer.Ordinal))
                    throw new InvalidDataException("Closed entry arguments differ from the recorded extraction.");
                entryTypeArguments = saved.ToList();
            }
            FeatureProfile profile = recordedCheck
                ? recorded!.Value.GetProperty("profile").Deserialize<FeatureProfile>() ?? throw new InvalidDataException("Missing execution profile")
                : FeatureProfile.Select(positional.Count == 4 ? positional[3] : "scalar");
            stage = "assembly loading";
            var assemblySnapshot = batch?.ReadAssembly(assemblyPath);
            byte[] assembly = assemblySnapshot?.Bytes ?? File.ReadAllBytes(assemblyPath);
            stage = "metadata and CIL validation";
            if (assemblySnapshot is null) VectorSignatures.Validate(assembly);
            else assemblySnapshot.ValidateSignatures();
            using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(assembly, writable: false));
            var symbols = Symbols.Read(module, assemblyPath, out var symbolNotice);
            var assemblyIdentity = module.Assembly?.Name.FullName ?? throw new InvalidDataException("Input must contain assembly metadata.");
            stage = "contract import validation";
            List<ImportResolution.Source> importSources = [];
            if (recorded is { } recordedGraph && recordedGraph.TryGetProperty("importGraph", out JsonElement graphNodes))
                foreach (JsonElement node in graphNodes.EnumerateArray())
                {
                    string name = AssemblyNameReference.Parse(node.GetProperty("assemblyIdentity").GetString()!).Name;
                    string sidecar = global::Program.ExtractionIdentity.Resolve(output, node.GetProperty("sidecarPath").GetString()!);
                    string implementation = implementationPaths.GetValueOrDefault(name) ??
                        global::Program.ExtractionIdentity.Resolve(output, node.GetProperty("implementationPath").GetString()!);
                    string expected = importHashes.GetValueOrDefault(name) ?? node.GetProperty("implementationSha256").GetString()!;
                    string expectedInterface = interfaceHashes.GetValueOrDefault(name) ??
                        (node.TryGetProperty("expectedInterfaceDigest", out JsonElement pinnedInterface) ? pinnedInterface.GetString()! :
                            throw new InvalidDataException("Import graph has no independent interface digest; extract again with --import-interface-sha256."));
                    importSources.Add(new(sidecar, Path.GetFullPath(implementation), expected, expectedInterface));
                }
            if (recorded is { } recordedImports && recordedImports.TryGetProperty("imports", out JsonElement importRecords))
                foreach (JsonElement binding in importRecords.EnumerateArray())
                {
                    string sidecar = global::Program.ExtractionIdentity.Resolve(output, binding.GetProperty("sidecarPath").GetString()!);
                    if (importSources.Any(source => source.SidecarPath == sidecar)) continue;
                    string name = AssemblyNameReference.Parse(binding.GetProperty("identity").GetString()!.Split("::", 2)[0]).Name;
                    string implementation = implementationPaths.GetValueOrDefault(name) ??
                        global::Program.ExtractionIdentity.Resolve(output, binding.GetProperty("implementationPath").GetString()!);
                    string expected = importHashes.GetValueOrDefault(name) ?? binding.GetProperty("implementationSha256").GetString()!;
                    string expectedInterface = interfaceHashes.GetValueOrDefault(name) ??
                        (binding.TryGetProperty("interfaceDigest", out JsonElement pinnedInterface) ? pinnedInterface.GetString()! :
                            throw new InvalidDataException("Import extraction has no independent interface digest; extract again with --import-interface-sha256."));
                    importSources.Add(new(sidecar, Path.GetFullPath(implementation), expected, expectedInterface));
                }
            foreach (string sidecar in importPaths.Distinct(StringComparer.Ordinal))
            {
                if (importSources.Any(source => source.SidecarPath == sidecar)) continue;
                ContractInterface contract = ContractInterface.Read(File.ReadAllBytes(sidecar));
                string name = AssemblyNameReference.Parse(contract.AssemblyIdentity).Name;
                string adjacent = Path.Combine(Path.GetDirectoryName(sidecar)!, name + ".dll");
                string implementation = implementationPaths.GetValueOrDefault(name) ?? (File.Exists(adjacent) ? adjacent :
                    Path.Combine(Path.GetDirectoryName(Path.GetFullPath(assemblyPath))!, name + ".dll"));
                importSources.Add(new(sidecar, Path.GetFullPath(implementation), importHashes.GetValueOrDefault(name) ?? "", interfaceHashes.GetValueOrDefault(name) ?? ""));
            }
            // check replays only the recorded import graph; sidecars appearing after extraction are outside it.
            foreach (AssemblyNameReference reference in recorded is null ? module.AssemblyReferences : [])
            {
                string discovered = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(assemblyPath))!, reference.Name + ".leancil.contracts");
                if (File.Exists(discovered) && !importSources.Any(source => source.SidecarPath == discovered))
                    importSources.Add(new(discovered, Path.GetFullPath(implementationPaths.GetValueOrDefault(reference.Name) ??
                        Path.Combine(Path.GetDirectoryName(discovered)!, reference.Name + ".dll")),
                        importHashes.GetValueOrDefault(reference.Name) ?? "", interfaceHashes.GetValueOrDefault(reference.Name) ?? "", Discovered: true));
            }
            using ImportResolution imports = new(importSources);
            using var enumMetadata = EnumTypes.BeginScope();
            stage = "metadata and CIL validation";
            MethodDefinition[] methods = MetadataValidation.Validate(module, expectedAssembly ?? assemblyIdentity, entry, profile, initializedTypes, imports: imports,
                typeArguments: entryTypeArguments.ToArray(), importedByref: type => imports.ValidateByref(type, profile));
            StaticIdentityRecord[] staticIdentities = LeanEmitter.StaticIdentities(methods, profile);
            imports.ValidateStatics(staticIdentities);
            string Hash(byte[] bytes) => Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();
            var assemblyHash = assemblySnapshot?.Hash ?? Hash(assembly);
            var extractorHash = batch?.ExtractorHash ?? Hash(File.ReadAllBytes(typeof(LeanEmitter).Assembly.Location));
            if (recorded is { } prior)
            {
                stage = "extraction integrity";
                if (prior.GetProperty("assemblySha256").GetString() != assemblyHash)
                    throw new InvalidDataException($"Stale or mismatched verification artifact: assembly has changed since extraction.\n  Assembly: {CliPaths.Display(assemblyPath)}");
                if (prior.GetProperty("extractorSha256").GetString() != extractorHash)
                    throw new InvalidDataException("Stale or mismatched verification artifact: extractor has changed since extraction.");
            }
            stage = "metadata and CIL validation";
            using var originalModule = ModuleDefinition.ReadModule(new MemoryStream(assembly, writable: false));
            LeanEmitter.Emission emitted = LeanEmitter.Emit(methods, profile, originalModule, imports,
                staticIdentities, collectTemplates: checkedTemplate is not null);
            string source = emitted.Source;
            var staticValues = new SortedSet<string>(methods.SelectMany(m => Reachability.Analyze(m, profile))
                .Where(i => i.OpCode.Code == Code.Ldsfld)
                .Select(i => StaticValues.Resolve((FieldReference)i.Operand, module, profile.Architecture).Field.FullName), StringComparer.Ordinal);
            if (initializedTypes.Count > 0)
                source += "\n-- Caller assumption: these types completed initialization successfully before invocation.\n" +
                    "def Extracted.initializedTypes : List String := " + JsonSerializer.Serialize(initializedTypes) + "\n";
            var initializationAssumptions = InitializationAssumption.Normalize(initializedTypes.Select(type =>
                new InitializationAssumption(assemblyIdentity, type)).Concat(imports.InitializationAssumptions()));
            if (initializationAssumptions.Length > 0)
                source += "\n-- Named runtime premises inherited from this assembly and its contract imports.\n" +
                    "def Extracted.initializationAssumptions : List (String × String) := " +
                    InitializationAssumption.Lean(initializationAssumptions) + "\n";
            if (staticValues.Count > 0)
                source += "-- Caller assumption: these fields keep the values their static constructors stored.\n" +
                    "def Extracted.staticValues : List String := " + JsonSerializer.Serialize(staticValues) + "\n";
            SortedDictionary<string, string> importModules = imports.InterfaceModules();
            if (imports.Bindings.Count > 0) importModules.Add("ExtractedImports", imports.EmitImports(methods.Length));
            SortedDictionary<string, string> importModuleHashes = new(importModules.ToDictionary(pair => pair.Key,
                pair => Hash(Encoding.UTF8.GetBytes(pair.Value))), StringComparer.Ordinal);
            string manifest = JsonSerializer.Serialize(new
            {
                schema = 3,
                imports = imports.Bindings.Select(binding => JsonSerializer.SerializeToElement(binding with
                {
                    ImplementationPath = Path.GetRelativePath(output, binding.ImplementationPath).Replace('\\', '/'),
                    SidecarPath = Path.GetRelativePath(output, binding.SidecarPath).Replace('\\', '/')
                }, ContractInterface.Json)),
                importGraph = imports.Nodes.Select(node => JsonSerializer.SerializeToElement(node with
                {
                    SidecarPath = Path.GetRelativePath(output, node.SidecarPath).Replace('\\', '/'),
                    ImplementationPath = Path.GetRelativePath(output, node.ImplementationPath).Replace('\\', '/')
                }, ContractInterface.Json)),
                importModules = importModuleHashes,
                assemblyPath = recorded?.GetProperty("assemblyPath").GetString()
                    ?? Path.GetRelativePath(output, Path.GetFullPath(assemblyPath)).Replace('\\', '/'),
                assemblyIdentity = module.Assembly.Name.FullName, mvid = module.Mvid,
                assemblySha256 = assemblyHash, entry = methods[0].FullName,
                entryDefinition = MethodSpecialization.Definition(methods[0]).FullName, entryTypeArguments,
                layoutIdentities = emitted.LayoutIdentities, profile, initializedTypes,
                initializationAssumptions = JsonSerializer.SerializeToElement(initializationAssumptions, ContractInterface.Json),
                staticValues,
                staticIdentities = staticIdentities.Select(identity => JsonSerializer.SerializeToElement(identity, ContractInterface.Json)),
                generatedSha256 = Hash(Encoding.UTF8.GetBytes(source)),
                extractorSha256 = extractorHash,
                methods = methods.Select(m => new { signature = m.FullName, token = m.MetadataToken.ToInt32(),
                    specialization = MethodSpecialization.Source(m),
                    locals = m.Body.Variables.Select(v => v.VariableType.FullName),
                    instructions = m.Body.Instructions.Select(i => i.ToString()) }),
                layouts = module.GetTypes().Where(t => t.IsValueType && t.IsExplicitLayout && t.Fields.Any(f => !f.IsStatic))
                    .Select(t => new { name = t.FullName, size = t.ClassSize,
                        fields = t.Fields.Where(f => !f.IsStatic).Select(f => new { name = f.Name, offset = f.Offset, type = f.FieldType.FullName }) })
            }, new JsonSerializerOptions { WriteIndented = true });
            string leanPath = Path.Combine(output, "Extracted.lean");
            string symbolPath = Path.Combine(output, "Symbols.lean");
            string? symbolSource = symbols is null ? null : Symbols.Emit(methods, symbols);
            if (args[0] == "check")
            {
                stage = "extraction integrity";
                if (File.ReadAllText(leanPath) != source)
                    throw new InvalidDataException($"Stale or mismatched verification artifact: {CliPaths.Display(leanPath)} differs from regenerated CIL.");
                foreach ((string name, string content) in importModules)
                    if (File.ReadAllText(Path.Combine(output, name.Replace('.', Path.DirectorySeparatorChar) + ".lean")) != content)
                        throw new InvalidDataException("Stale or mismatched contract interface source: " + name);
                if (File.ReadAllText(identityPath) != manifest)
                    throw new InvalidDataException($"Stale or mismatched verification artifact: {CliPaths.Display(identityPath)} differs from regenerated assembly, extractor or configuration metadata.");
                if (symbolSource is not null && File.Exists(symbolPath) && File.ReadAllText(symbolPath) != symbolSource)
                    throw new InvalidDataException($"Stale or mismatched verification artifact: {CliPaths.Display(symbolPath)} differs from the regenerated PDB names and locations.\n  Assembly: {CliPaths.Display(assemblyPath)}\n  Method: {methods[0].FullName}");
                report.WriteLine("Valid: extraction artifacts match the assembly and recorded settings.");
                report.WriteLine($"  Assembly: {assemblyIdentity}");
                report.WriteLine($"  DLL: {CliPaths.Display(assemblyPath)}");
                report.WriteLine($"  Entry: {methods[0].FullName}");
                report.WriteLine($"  Profile: {profile.Name} ({profile.Architecture}, {profile.NativeWidth}-bit, {(profile.LittleEndian ? "little" : "big")}-endian)");
                report.WriteLine($"  Reachable methods: {methods.Length}");
                report.WriteLine($"  CIL: {CliPaths.Display(leanPath)}");
                report.WriteLine($"  Manifest: {CliPaths.Display(identityPath)}");
                report.WriteLine("  Matched: assembly identity and SHA-256, extractor SHA-256, configuration, metadata and regenerated CIL.");
                if (File.Exists(symbolPath))
                    report.WriteLine(symbolSource is null ? "  Symbols: not checked (no matching PDB)" : "  Symbols: matched the PDB");
            }
            else
            {
                Directory.CreateDirectory(output);
                File.WriteAllText(leanPath, source, new UTF8Encoding(false));
                File.WriteAllText(identityPath, manifest, new UTF8Encoding(false));
                foreach ((string name, string content) in importModules)
                {
                    string path = Path.Combine(output, name.Replace('.', Path.DirectorySeparatorChar) + ".lean");
                    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                    File.WriteAllText(path, content, new UTF8Encoding(false));
                }
                // Symbols from an earlier build must not outlive its PDB.
                if (symbolSource is null) File.Delete(symbolPath);
                else File.WriteAllText(symbolPath, symbolSource, new UTF8Encoding(false));
                report.WriteLine($"Extracted {methods.Length} reachable method{(methods.Length == 1 ? "" : "s")} into {CliPaths.Display(leanPath)}");
            }
            if (symbolNotice is not null) report.WriteLine("  " + symbolNotice);
            foreach (var name in initializedTypes)
                report.WriteLine($"  Caller assumption: {name} initialization completed successfully before invocation.");
            foreach (var assumption in initializationAssumptions.Where(item => item.AssemblyIdentity != assemblyIdentity))
                report.WriteLine($"  Imported caller assumption: {assumption.AssemblyIdentity}::{assumption.TypeName} " +
                    "initialization completed successfully before invocation.");
            foreach (var name in staticValues)
                report.WriteLine($"  Caller assumption: {name} keeps the value its static constructor stored.");
            checkedTemplate?.Invoke(new(output, assemblyHash, profile, emitted.Templates));
        }
        catch (Exception exception)
        {
            if (rethrow) throw;
            CliDiagnostics.Write(exception, stage, args[0] is "check" or "verify" or "audit-library");
            return 1;
        }
        return 0;
    }

    // Capture only after the ordinary check has matched every extraction artifact.
    static TemplateEmitter.Variant ReadTemplate(string directory)
    {
        TemplateEmitter.Variant? variant = null;
        if (Run(["check", directory], checkedTemplate: value => variant = value) != 0 || variant is null)
            throw new InvalidDataException("Template input failed exact extraction checking: " + directory);
        return variant;
    }
}
