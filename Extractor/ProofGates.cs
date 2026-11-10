using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Nethermind.LeanCIL;

partial class Program
{
    sealed record GateVariant(string name, string assembly, string expect);
    sealed record ProofGateEntry(string name, string assembly, string method, string[] profiles,
        string proof, string theorem, GateVariant[]? variants = null,
        string[]? initializedTypes = null, string[]? typeArguments = null);
    sealed record GateManifest(int schema, string proofRoot, string outputRoot, ProofGateEntry[] gates);
    sealed record SelectedGate(GeneratedExtraction Extraction, string Proof, string Theorem, string Expect);

    const string GatesUsage = "Usage: leancil gates manifest.json [--method name] [--profile name] " +
        "[--changed path]... [--check] [--parallel count] [--results results.json] [--format text|json]";

    /// <summary>Extracts an explicit catalog and delegates checking and certification to verify-batch.</summary>
    internal static int RunGates(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException(GatesUsage);
        var manifestPath = Path.GetFullPath(args[0]);
        var directory = Path.GetDirectoryName(manifestPath)!;
        var manifest = JsonSerializer.Deserialize<GateManifest>(File.ReadAllText(manifestPath),
            new JsonSerializerOptions { UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow })
            ?? throw new InvalidDataException("Missing gate manifest.");
        if (manifest.schema != 1 || string.IsNullOrWhiteSpace(manifest.proofRoot) ||
            string.IsNullOrWhiteSpace(manifest.outputRoot) || manifest.gates is not { Length: > 0 })
            throw new InvalidDataException("Expected schema 1, proofRoot, outputRoot and nonempty gates.");
        string? methodFilter = null;
        string? profileFilter = null;
        var changed = new HashSet<string>(OperatingSystem.IsWindows()
            ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal);
        var verification = new List<string>();
        for (var index = 1; index < args.Length; index++)
        {
            var option = args[index];
            if (option is "--check" or "--fresh" or "--rebuild-library" or "--trace")
            {
                verification.Add(option);
                continue;
            }
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException("Missing value for " + option);
            switch (option)
            {
                case "--method" when methodFilter is null: methodFilter = args[index]; break;
                case "--profile" when profileFilter is null: profileFilter = args[index]; break;
                case "--changed": changed.Add(Path.GetFullPath(args[index])); break;
                case "--parallel" or "--results" or "--format":
                    verification.AddRange([option, args[index]]);
                    break;
                default: throw new ArgumentException("Unknown or duplicate option: " + option);
            }
        }
        var proofRoot = Path.GetFullPath(manifest.proofRoot, directory);
        var outputRoot = Path.GetFullPath(manifest.outputRoot, directory);
        var selected = new List<SelectedGate>();
        var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var gate in manifest.gates)
        {
            if (gate is null || !SafeGateName(gate.name) || !names.Add(gate.name) ||
                string.IsNullOrWhiteSpace(gate.assembly) || string.IsNullOrWhiteSpace(gate.method) ||
                string.IsNullOrWhiteSpace(gate.proof) || string.IsNullOrWhiteSpace(gate.theorem) ||
                gate.profiles is not { Length: > 0 } || gate.profiles.Any(string.IsNullOrWhiteSpace) ||
                gate.profiles.Distinct(StringComparer.Ordinal).Count() != gate.profiles.Length)
                throw new InvalidDataException("Invalid or duplicate gate entry.");
            var variants = new HashSet<string>(StringComparer.OrdinalIgnoreCase) { "production" };
            foreach (var variant in gate.variants ?? [])
                if (variant is null || !SafeGateName(variant.name) || !variants.Add(variant.name) ||
                    string.IsNullOrWhiteSpace(variant.assembly) || variant.expect is not ("certifies" or "rejected"))
                    throw new InvalidDataException("Invalid or duplicate variant for " + gate.name);
            if (methodFilter is not null && !gate.method.Contains(methodFilter, StringComparison.Ordinal)) continue;
            var proof = Within(proofRoot, gate.proof);
            foreach (var profile in gate.profiles.Where(profile => profileFilter is null || profile == profileFilter))
            {
                Add("production", gate.assembly, "verified");
                foreach (var variant in gate.variants ?? [])
                    Add(variant.name, variant.assembly, variant.expect == "rejected" ? "rejected" : "verified");

                void Add(string variant, string assembly, string expect)
                {
                    var output = Path.Combine(outputRoot, gate.name, ContentKey(profile)[..12], variant);
                    var selectedProfile = profile.StartsWith('@')
                        ? "@" + Path.GetFullPath(profile[1..], directory) : profile;
                    selected.Add(new(new(Path.GetFullPath(assembly, directory), gate.method, output,
                        selectedProfile, gate.initializedTypes, gate.typeArguments), proof, gate.theorem, expect));
                }
            }
        }
        // Proof-only changes need no extraction of unrelated gates. Other source changes use method metadata.
        bool ProofAffected(SelectedGate gate) => ProofSources(proofRoot, gate.Proof).Keys
            .Any(path => changed.Contains(Path.GetFullPath(path, proofRoot)));
        if (changed.Count > 0 && changed.All(path => Path.GetExtension(path) == ".lean"))
            selected = selected.Where(ProofAffected).ToList();
        if (selected.Count == 0) throw new ArgumentException("No gates match the requested selection.");
        ExtractBatch("extract", null, selected.Select(gate => gate.Extraction));
        if (changed.Count > 0)
            selected = selected.Where(gate => ProofAffected(gate) || GateMethodAffected(gate, changed)).ToList();
        if (selected.Count == 0) throw new ArgumentException("No gates depend on the changed paths.");
        if (verification.Contains("--check") && selected.Any(gate => gate.Expect == "rejected"))
            throw new ArgumentException("--check cannot evaluate mutation rejection expectations.");
        Directory.CreateDirectory(outputRoot);
        var requestsPath = Path.Combine(outputRoot, "requests.json");
        File.WriteAllText(requestsPath, JsonSerializer.Serialize(new BatchManifest(1, proofRoot,
            selected.Select(gate => new BatchRequest(gate.Extraction.Output, gate.Proof, gate.Theorem,
                gate.Expect)).ToArray()), Json) + "\n");
        return VerifyBatch([requestsPath, .. verification]);
    }

    static bool SafeGateName(string? name) => name is not (null or "" or "." or "..") &&
        Regex.IsMatch(name, @"\A[A-Za-z0-9_.-]+\z");

    // PDBs only select work. Missing source information conservatively selects the method.
    static bool GateMethodAffected(SelectedGate gate, HashSet<string> changed)
    {
        if (changed.Contains(gate.Extraction.Assembly)) return true;
        if (changed.Any(path => Path.GetExtension(path) is ".csproj" or ".props" or ".targets")) return true;
        if (!changed.Any(path => Path.GetExtension(path) == ".cs")) return false;
        using var module = ModuleDefinition.ReadModule(gate.Extraction.Assembly);
        if (Symbols.Read(module, gate.Extraction.Assembly, out _) is null) return true;
        var identityPath = Path.Combine(gate.Extraction.Output, "identity.json");
        using var identity = JsonDocument.Parse(File.ReadAllText(identityPath));
        if (identity.RootElement.GetProperty("references").GetArrayLength() > 0) return true;
        foreach (var method in identity.RootElement.GetProperty("methods").EnumerateArray())
        {
            if (module.LookupToken(method.GetProperty("token").GetInt32()) is not MethodDefinition definition ||
                !definition.DebugInformation.HasSequencePoints) return true;
            if (definition.DebugInformation.SequencePoints.Where(point => !point.IsHidden).Any(point =>
                changed.Contains(Path.GetFullPath(point.Document.Url)))) return true;
        }
        return false;
    }
}
