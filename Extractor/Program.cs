using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class Program
{
    const string Usage = "Usage: leancil list assembly.dll\n       leancil extract assembly.dll '[return-type ]Type::Method(parameter-types)' output-directory [profile|@profile.json] [--assembly 'assembly name or full identity'] [--assume-initialized Namespace.Type]...\n       leancil check output-directory [--assembly-path assembly.dll] [--assembly 'assembly name or full identity']\n       leancil verify output-directory [--proof proof.lean] [--theorem name] [--fresh]";

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
            var initializedTypes = new SortedSet<string>(StringComparer.Ordinal);
            for (var index = 1; index < args.Length; index++)
            {
                if (args[index] == "--assume-initialized")
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
            if (recorded is { } existing && existing.GetProperty("schema").GetInt32() != 2)
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
            using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(assembly));
            var assemblyIdentity = module.Assembly?.Name.FullName ?? throw new InvalidDataException("Input must contain assembly metadata.");
            stage = "metadata and CIL validation";
            MethodDefinition[] methods = MetadataValidation.Validate(module, expectedAssembly ?? assemblyIdentity, entry, profile, initializedTypes);
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
            string source = LeanEmitter.Emit(methods, profile, Hash(assembly));
            if (initializedTypes.Count > 0)
                source += "\n-- Caller assumption: these types completed initialization successfully before invocation.\n" +
                    "def Extracted.initializedTypes : List String := " + JsonSerializer.Serialize(initializedTypes) + "\n";
            string manifest = JsonSerializer.Serialize(new
            {
                schema = 2,
                assemblyPath = recorded?.GetProperty("assemblyPath").GetString()
                    ?? Path.GetRelativePath(output, Path.GetFullPath(assemblyPath)),
                assemblyIdentity = module.Assembly.Name.FullName, mvid = module.Mvid,
                assemblySha256 = Hash(assembly), entry = methods[0].FullName, profile, initializedTypes,
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
            if (args[0] == "check")
            {
                stage = "extraction integrity";
                if (File.ReadAllText(leanPath) != source)
                    throw new InvalidDataException($"Stale or mismatched verification artifact: {CliPaths.Display(leanPath)} differs from regenerated CIL.");
                if (File.ReadAllText(identityPath) != manifest)
                    throw new InvalidDataException($"Stale or mismatched verification artifact: {CliPaths.Display(identityPath)} differs from regenerated assembly, extractor or configuration metadata.");
                Console.WriteLine("Valid: extraction artifacts match the assembly and recorded settings.");
                Console.WriteLine($"  Assembly: {assemblyIdentity}");
                Console.WriteLine($"  DLL: {CliPaths.Display(assemblyPath)}");
                Console.WriteLine($"  Entry: {methods[0].FullName}");
                Console.WriteLine($"  Profile: {profile.Name} ({profile.Architecture}, {profile.NativeWidth}-bit, {(profile.LittleEndian ? "little" : "big")}-endian)");
                Console.WriteLine($"  Reachable methods: {methods.Length}");
                Console.WriteLine($"  CIL: {CliPaths.Display(leanPath)}");
                Console.WriteLine($"  Manifest: {CliPaths.Display(identityPath)}");
                Console.WriteLine("  Matched: assembly identity and SHA-256, extractor SHA-256, configuration, metadata and regenerated CIL.");
            }
            else
            {
                Directory.CreateDirectory(output);
                File.WriteAllText(leanPath, source, new UTF8Encoding(false));
                File.WriteAllText(identityPath, manifest, new UTF8Encoding(false));
                Console.WriteLine($"Extracted {methods.Length} reachable method{(methods.Length == 1 ? "" : "s")} into {CliPaths.Display(leanPath)}");
            }
            foreach (var name in initializedTypes)
                Console.WriteLine($"  Caller assumption: {name} initialization completed successfully before invocation.");
        }
        catch (Exception exception)
        {
            CliDiagnostics.Write(exception, stage, args[0] is "check" or "verify");
            return 1;
        }
        return 0;
    }
}
