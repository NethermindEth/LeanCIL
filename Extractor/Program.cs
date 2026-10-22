using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class Program
{
    const string Usage = "Usage: leancil list assembly.dll\n       leancil lint-exceptions output-directory --documentation assembly.xml\n       leancil extract assembly.dll '[return-type ]Type::Method(parameter-types)' output-directory [profile|@profile.json] [--assembly 'assembly name or full identity'] [--assume-initialized Namespace.Type]... [--import Lib.leancil.contracts] [--import-implementation Lib=path] [--import-sha256 Lib=hex] [--import-interface-sha256 Lib=hex]\n       leancil export-contracts manifest.json [--output Lib.leancil.contracts] [--bundle directory]\n       leancil blockers assembly.dll --manifest manifest.json [--output blockers.json] [--assembly 'assembly name or full identity']\n       leancil check output-directory [--assembly-path assembly.dll] [--assembly 'assembly name or full identity']\n       leancil verify output-directory [--proof proof.lean] [--theorem name] [--fresh] [--proof-root package-directory]\n       leancil verify-batch requests.json [--fresh] [--parallel count] [--results results.json]";

    internal static int CheckExtraction(string output) => Main(["check", output]);

    static int Main(string[] args)
    {
        if (args.Length == 0 || args is ["--help"] or ["-h"])
        {
            Console.WriteLine(Usage);
            return 0;
        }

        // Extraction is deterministic and never loads or executes the input assembly.
        var stage = "arguments";
        try
        {
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
                        if (!selected.TryAdd(args[index][..separator], args[index][(separator + 1)..]))
                            throw new ArgumentException("Duplicate " + option + " assembly.");
                    }
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
            if (recorded is { } existing && existing.GetProperty("schema").GetInt32() is not (2 or 3))
                throw new InvalidDataException("Unsupported extraction manifest schema; run leancil extract again.");
            var assemblyPath = recordedCheck
                ? assemblyOverride ?? Path.GetFullPath(recorded!.Value.GetProperty("assemblyPath").GetString()!, output)
                : positional[0];
            var entry = recordedCheck ? recorded!.Value.GetProperty("entry").GetString()! : positional[1];
            FeatureProfile profile = recordedCheck
                ? recorded!.Value.GetProperty("profile").Deserialize<FeatureProfile>() ?? throw new InvalidDataException("Missing execution profile")
                : FeatureProfile.Select(positional.Count == 4 ? positional[3] : "scalar");
            stage = "assembly loading";
            byte[] assembly = File.ReadAllBytes(assemblyPath);
            stage = "metadata and CIL validation";
            VectorSignatures.Validate(assembly);
            using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(assembly));
            var symbols = Symbols.Read(module, assemblyPath, out var symbolNotice);
            var assemblyIdentity = module.Assembly?.Name.FullName ?? throw new InvalidDataException("Input must contain assembly metadata.");
            stage = "contract import validation";
            List<ImportResolution.Source> importSources = [];
            if (recorded is { } recordedImports && recordedImports.TryGetProperty("imports", out JsonElement importRecords))
                foreach (JsonElement binding in importRecords.EnumerateArray())
                {
                    string sidecar = binding.GetProperty("sidecarPath").GetString()!;
                    if (importSources.Any(source => source.SidecarPath == sidecar)) continue;
                    string name = AssemblyNameReference.Parse(binding.GetProperty("identity").GetString()!.Split("::", 2)[0]).Name;
                    string implementation = implementationPaths.GetValueOrDefault(name) ?? binding.GetProperty("implementationPath").GetString()!;
                    string expected = importHashes.GetValueOrDefault(name) ?? binding.GetProperty("implementationSha256").GetString()!;
                    string expectedInterface = interfaceHashes.GetValueOrDefault(name) ??
                        (binding.TryGetProperty("expectedInterfaceDigest", out JsonElement pinnedInterface) ? pinnedInterface.GetString()! :
                            throw new InvalidDataException("Import extraction has no independent interface digest; extract again with --import-interface-sha256."));
                    importSources.Add(new(sidecar, Path.GetFullPath(implementation), expected, expectedInterface));
                }
            foreach (AssemblyNameReference reference in module.AssemblyReferences)
            {
                string discovered = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(assemblyPath))!, reference.Name + ".leancil.contracts");
                if (File.Exists(discovered) && !importPaths.Contains(discovered) && !importSources.Any(source => source.SidecarPath == discovered))
                    importPaths.Add(discovered);
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
            using ImportResolution imports = new(importSources);
            stage = "metadata and CIL validation";
            MethodDefinition[] methods = MetadataValidation.Validate(module, expectedAssembly ?? assemblyIdentity, entry, profile, initializedTypes, imports: imports);
            StaticIdentityRecord[] staticIdentities = LeanEmitter.StaticIdentities(methods, profile);
            imports.ValidateStatics(staticIdentities);
            string Hash(byte[] bytes) => Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();
            if (recorded is { } prior)
            {
                stage = "extraction integrity";
                if (prior.GetProperty("assemblySha256").GetString() != Hash(assembly))
                    throw new InvalidDataException($"Stale or mismatched verification artifact: assembly has changed since extraction.\n  Assembly: {CliPaths.Display(assemblyPath)}");
                if (prior.GetProperty("extractorSha256").GetString() != Hash(File.ReadAllBytes(typeof(LeanEmitter).Assembly.Location)))
                    throw new InvalidDataException("Stale or mismatched verification artifact: extractor has changed since extraction.");
            }
            stage = "metadata and CIL validation";
            using var originalModule = ModuleDefinition.ReadModule(new MemoryStream(assembly));
            string source = LeanEmitter.Emit(methods, profile, originalModule, imports);
            var staticValues = new SortedSet<string>(methods.SelectMany(m => Reachability.Analyze(m, profile))
                .Where(i => i.OpCode.Code == Code.Ldsfld)
                .Select(i => StaticValues.Resolve((FieldReference)i.Operand, module, profile.Architecture).Field.FullName), StringComparer.Ordinal);
            if (initializedTypes.Count > 0)
                source += "\n-- Caller assumption: these types completed initialization successfully before invocation.\n" +
                    "def Extracted.initializedTypes : List String := " + JsonSerializer.Serialize(initializedTypes) + "\n";
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
                imports = imports.Bindings.Select(binding => JsonSerializer.SerializeToElement(binding, ContractInterface.Json)),
                importModules = importModuleHashes,
                assemblyPath = recorded?.GetProperty("assemblyPath").GetString()
                    ?? Path.GetRelativePath(output, Path.GetFullPath(assemblyPath)),
                assemblyIdentity = module.Assembly.Name.FullName, mvid = module.Mvid,
                assemblySha256 = Hash(assembly), entry = methods[0].FullName, profile, initializedTypes, staticValues,
                staticIdentities = staticIdentities.Select(identity => JsonSerializer.SerializeToElement(identity, ContractInterface.Json)),
                generatedSha256 = Hash(Encoding.UTF8.GetBytes(source)),
                extractorSha256 = Hash(File.ReadAllBytes(typeof(LeanEmitter).Assembly.Location)),
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
                Console.WriteLine("Valid: extraction artifacts match the assembly and recorded settings.");
                Console.WriteLine($"  Assembly: {assemblyIdentity}");
                Console.WriteLine($"  DLL: {CliPaths.Display(assemblyPath)}");
                Console.WriteLine($"  Entry: {methods[0].FullName}");
                Console.WriteLine($"  Profile: {profile.Name} ({profile.Architecture}, {profile.NativeWidth}-bit, {(profile.LittleEndian ? "little" : "big")}-endian)");
                Console.WriteLine($"  Reachable methods: {methods.Length}");
                Console.WriteLine($"  CIL: {CliPaths.Display(leanPath)}");
                Console.WriteLine($"  Manifest: {CliPaths.Display(identityPath)}");
                Console.WriteLine("  Matched: assembly identity and SHA-256, extractor SHA-256, configuration, metadata and regenerated CIL.");
                if (File.Exists(symbolPath))
                    Console.WriteLine(symbolSource is null ? "  Symbols: not checked (no matching PDB)" : "  Symbols: matched the PDB");
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
                Console.WriteLine($"Extracted {methods.Length} reachable method{(methods.Length == 1 ? "" : "s")} into {CliPaths.Display(leanPath)}");
            }
            if (symbolNotice is not null) Console.WriteLine("  " + symbolNotice);
            foreach (var name in initializedTypes)
                Console.WriteLine($"  Caller assumption: {name} initialization completed successfully before invocation.");
            foreach (var name in staticValues)
                Console.WriteLine($"  Caller assumption: {name} keeps the value its static constructor stored.");
        }
        catch (Exception exception)
        {
            CliDiagnostics.Write(exception, stage, args[0] is "check" or "verify");
            return 1;
        }
        return 0;
    }
}
