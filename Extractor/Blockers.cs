using System.Security.Cryptography;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Runs extraction and its validators over explicit method/profile pairs; it never checks a proof.
internal static class Blockers
{
    const string Usage = "Usage: leancil blockers assembly.dll --manifest manifest.json [--output blockers.json] [--assembly 'assembly name or full identity']";
    const string Disclaimer = "Admission only: admitted entries are extractable under their profile; nothing here is proved.";

    sealed record Site(string Method, int? IlOffset, string? Instruction, string? Source, string Message);

    sealed class ChainComparer : IEqualityComparer<string[]>
    {
        internal static readonly ChainComparer Instance = new();
        public bool Equals(string[]? left, string[]? right) => ReferenceEquals(left, right) ||
            left is not null && right is not null && left.SequenceEqual(right, StringComparer.Ordinal);
        public int GetHashCode(string[] chain)
        {
            var hash = new HashCode();
            foreach (var method in chain) hash.Add(method, StringComparer.Ordinal);
            return hash.ToHashCode();
        }
    }

    sealed class Reach(string signature, string profile)
    {
        readonly HashSet<string[]> knownChains = new(ChainComparer.Instance);
        internal string Signature { get; } = signature;
        internal string Profile { get; } = profile;
        internal List<string[]> Chains { get; } = [];
        internal void AddChain(string[] chain)
        {
            if (knownChains.Add(chain)) Chains.Add(chain);
        }
    }

    // Lists retain discovery order; indexes only decide whether an occurrence is new.
    sealed class Finding(string construct)
    {
        readonly HashSet<Site> knownSites = [];
        readonly Dictionary<(string Signature, string Profile), Reach> knownEntries = [];
        internal string Construct { get; } = construct;
        internal List<Site> Sites { get; } = [];
        internal List<Reach> Entries { get; } = [];
        internal string Id { get; set; } = "";

        internal void Add(Site site, string signature, string profile, string[] chain)
        {
            if (knownSites.Add(site)) Sites.Add(site);
            if (!knownEntries.TryGetValue((signature, profile), out var reach))
            {
                reach = new(signature, profile);
                knownEntries.Add((signature, profile), reach);
                Entries.Add(reach);
            }
            reach.AddChain(chain);
        }
    }
    sealed record Outcome(string? Signature, string? Profile, string Status, string? Method, string? Reason, int? ReachableMethods, List<Finding> Findings);

    static string Hash(byte[] bytes) => Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();

    static string Option(string[] args, ref int index)
    {
        var name = args[index];
        if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException($"{name} requires a value.\n{Usage}");
        return args[index];
    }

    static string? Text(JsonElement entry, string name) =>
        entry.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String && !string.IsNullOrWhiteSpace(value.GetString())
            ? value.GetString() : null;

    internal static int Run(string[] args)
    {
        string? assemblyPath = null, manifestPath = null, outputPath = null, expectedAssembly = null;
        for (var index = 0; index < args.Length; index++)
        {
            switch (args[index])
            {
                case "--manifest" when manifestPath is null: manifestPath = Option(args, ref index); break;
                case "--output" when outputPath is null: outputPath = Option(args, ref index); break;
                case "--assembly" when expectedAssembly is null: expectedAssembly = Option(args, ref index); break;
                case var option when option.StartsWith("--", StringComparison.Ordinal):
                    throw new ArgumentException($"Unknown or duplicate option: {option}\n{Usage}");
                default:
                    if (assemblyPath is not null) throw new ArgumentException(Usage);
                    assemblyPath = args[index];
                    break;
            }
        }
        if (assemblyPath is null || manifestPath is null) throw new ArgumentException(Usage);
        manifestPath = Path.GetFullPath(manifestPath);
        var manifestDirectory = Path.GetDirectoryName(manifestPath)!;
        outputPath = Path.GetFullPath(outputPath ?? Path.Combine(manifestDirectory, "blockers.json"));

        using var manifest = JsonDocument.Parse(File.ReadAllText(manifestPath));
        var root = manifest.RootElement;
        if (root.ValueKind != JsonValueKind.Object || !root.TryGetProperty("entries", out var entries) || entries.ValueKind != JsonValueKind.Array ||
            root.EnumerateObject().Any(p => p.Name is not ("entries" or "initializedTypes")))
            throw new InvalidDataException("Blocker manifest must be an object with an `entries` array and optional `initializedTypes`.");
        var initializedTypes = root.TryGetProperty("initializedTypes", out var types)
            ? new SortedSet<string>(types.Deserialize<string[]>() ?? [], StringComparer.Ordinal) : new SortedSet<string>(StringComparer.Ordinal);

        var assembly = File.ReadAllBytes(assemblyPath);
        VectorSignatures.Validate(assembly);
        string identity, symbols;
        Guid mvid;
        using (var probe = ModuleDefinition.ReadModule(new MemoryStream(assembly)))
        {
            identity = probe.Assembly?.Name.FullName ?? throw new InvalidDataException("Input must contain assembly metadata.");
            mvid = probe.Mvid;
            symbols = Symbols.Read(probe, assemblyPath, out _) is { } origin ? origin == "embedded" ? "embedded portable PDB" : "portable PDB " + origin : "none";
        }

        var findings = new Dictionary<string, Finding>(StringComparer.Ordinal);
        var outcomes = new List<Outcome>();
        foreach (var entry in entries.EnumerateArray())
        {
            var signature = entry.ValueKind == JsonValueKind.Object ? Text(entry, "signature") : null;
            var profileName = entry.ValueKind == JsonValueKind.Object ? Text(entry, "profile") : null;
            Outcome NotChecked(string reason) => new(signature, profileName, "notChecked", null, reason, null, []);
            if (entry.ValueKind != JsonValueKind.Object || entry.EnumerateObject().Any(p => p.Name is not ("signature" or "profile")))
            {
                outcomes.Add(NotChecked("Entry must be an object with only `signature` and `profile`."));
                continue;
            }
            if (signature is null || profileName is null)
            {
                outcomes.Add(NotChecked(signature is null ? "Missing method signature." : "Missing profile."));
                continue;
            }
            FeatureProfile profile;
            try
            {
                // A file profile is relative to the manifest, so the manifest checks the same pairs from any directory.
                profile = FeatureProfile.Select(profileName.StartsWith('@') ? "@" + Path.GetFullPath(profileName[1..], manifestDirectory) : profileName);
            }
            catch (Exception error)
            {
                outcomes.Add(NotChecked("Profile: " + error.Message));
                continue;
            }

            // Validation rewrites generic call operands, so every entry gets its own module.
            using var module = StaticData.ReadModule(assembly);
            Symbols.Read(module, assemblyPath, out _);
            var blocked = new List<MetadataValidation.Blocked>();
            MethodDefinition[] methods;
            try { methods = MetadataValidation.Validate(module, expectedAssembly ?? identity, signature, profile, initializedTypes, blocked); }
            catch (Exception error)
            {
                // Only selection, profile, assumption and assembly checks throw once blockers are collected.
                outcomes.Add(NotChecked(error.Message));
                continue;
            }
            if (blocked.Count == 0)
            {
                try
                {
                    using var original = StaticData.ReadModule(assembly);
                    LeanEmitter.Emit(methods, profile, original);
                }
                catch (Exception error) { blocked.Add(new(methods[0], null, error, [methods[0]])); }
            }
            if (blocked.Count == 0)
            {
                outcomes.Add(new(signature, profileName, "admitted", methods[0].FullName, null, methods.Length, []));
                continue;
            }
            var entryFindings = new List<Finding>();
            var knownFindings = new HashSet<Finding>();
            foreach (var failure in blocked)
            {
                var message = failure.Error.Message;
                int? offset = failure.At?.Offset ?? (Regex.Match(message, @"\bIL_([0-9a-f]{4,})\b") is { Success: true } label
                    ? Convert.ToInt32(label.Groups[1].Value, 16) : null);
                // The construct is the diagnostic without its site, so every occurrence shares one blocker.
                var construct = Regex.Replace(message.Split('\n')[0], @"\bIL_[0-9a-f]{4,}: ", "");
                if (!findings.TryGetValue(construct, out var finding)) findings[construct] = finding = new(construct);
                var site = new Site(failure.Method.FullName, offset, failure.At?.ToString(),
                    offset is int at ? Symbols.Location(failure.Method, at, Path.GetFileName) : null, message);
                var chain = failure.Chain.Select(method => method.FullName).ToArray();
                finding.Add(site, chain[0], profileName, chain);
                if (knownFindings.Add(finding)) entryFindings.Add(finding);
            }
            outcomes.Add(new(signature, profileName, "blocked", blocked[0].Chain[0].FullName, null, null, entryFindings));
        }

        // The most widely reached blockers lead; identifiers follow that order.
        var ordered = findings.Values.OrderByDescending(f => f.Entries.Count).ThenByDescending(f => f.Sites.Count)
            .ThenBy(f => f.Construct, StringComparer.Ordinal).ToArray();
        for (var i = 0; i < ordered.Length; i++) ordered[i].Id = $"B{i + 1}";
        var ranks = ordered.Select((finding, index) => (finding, index))
            .ToDictionary(pair => pair.finding, pair => pair.index);
        foreach (var outcome in outcomes) outcome.Findings.Sort((left, right) => ranks[left].CompareTo(ranks[right]));

        var report = JsonSerializer.Serialize(new
        {
            schema = 1,
            note = Disclaimer,
            assemblyPath = Path.GetFullPath(assemblyPath),
            assemblyIdentity = identity,
            mvid,
            assemblySha256 = Hash(assembly),
            extractorSha256 = Hash(File.ReadAllBytes(typeof(LeanEmitter).Assembly.Location)),
            symbols,
            initializedTypes,
            counts = new
            {
                admitted = outcomes.Count(o => o.Status == "admitted"),
                blocked = outcomes.Count(o => o.Status == "blocked"),
                notChecked = outcomes.Count(o => o.Status == "notChecked")
            },
            entries = outcomes.Select(o => new
            {
                signature = o.Signature, profile = o.Profile, status = o.Status, method = o.Method, reason = o.Reason,
                reachableMethods = o.ReachableMethods, blockers = o.Findings.Select(f => f.Id)
            }),
            blockers = ordered.Select(f => new
            {
                id = f.Id, construct = f.Construct,
                sites = f.Sites.Select(s => new { method = s.Method, ilOffset = s.IlOffset, instruction = s.Instruction, source = s.Source, message = s.Message }),
                entries = f.Entries.Select(r => new { signature = r.Signature, profile = r.Profile, chains = r.Chains })
            })
        }, new JsonSerializerOptions { WriteIndented = true, Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping });
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, report + "\n", new UTF8Encoding(false));
        Console.Write(Summary(identity, outcomes, ordered, outputPath));
        return 0;
    }

    static string Summary(string identity, List<Outcome> outcomes, Finding[] findings, string outputPath)
    {
        static string Line(string text) => text.Split('\n')[0];
        static string Profile(string? profile) => profile is null ? "no profile" : profile.StartsWith('@') ? "@" + Path.GetFileName(profile[1..]) : profile;
        static string Count(int count, string one, string many) => $"{count} {(count == 1 ? one : many)}";
        var text = new StringBuilder();
        text.AppendLine($"Admission of {Count(outcomes.Count, "entry", "entries")} in {identity}: " +
            $"{outcomes.Count(o => o.Status == "admitted")} admitted, {outcomes.Count(o => o.Status == "blocked")} blocked, " +
            $"{outcomes.Count(o => o.Status == "notChecked")} not checked");
        foreach (var outcome in outcomes)
            text.AppendLine($"  {outcome.Status switch { "admitted" => "admitted   ", "blocked" => "blocked    ", _ => "not checked" }} " +
                $"{(outcome.Method is { } method ? Short(method) : outcome.Signature ?? "(no signature)")} [{Profile(outcome.Profile)}]" +
                (outcome.Status == "admitted" ? $" ({Count(outcome.ReachableMethods!.Value, "reachable method", "reachable methods")})" :
                 outcome.Status == "blocked" ? ": " + string.Join(", ", outcome.Findings.Select(f => f.Id)) :
                 ": " + Line(outcome.Reason!)));
        if (findings.Length > 0) text.AppendLine($"Blockers ({findings.Length} distinct):");
        foreach (var finding in findings)
        {
            text.AppendLine($"  {finding.Id} {finding.Construct}");
            text.AppendLine($"     {Count(finding.Entries.Count, "entry", "entries")}, {Count(finding.Sites.Count, "site", "sites")}; profiles: " +
                string.Join(", ", finding.Entries.Select(r => Profile(r.Profile)).Distinct()));
            foreach (var site in finding.Sites.Take(3))
                text.AppendLine($"     at {Short(site.Method)}" + (site.IlOffset is int offset ? $" IL_{offset:x4}" : "") +
                    (site.Source is null ? "" : $" ({site.Source})"));
            if (finding.Sites.Count > 3) text.AppendLine($"     and {Count(finding.Sites.Count - 3, "more site", "more sites")}");
            var chains = finding.Entries.SelectMany(r => r.Chains).Select(c => string.Join(" -> ", c.Select(Short))).Distinct().ToArray();
            foreach (var chain in chains.Take(3)) text.AppendLine("     via " + chain);
            if (chains.Length > 3) text.AppendLine($"     and {Count(chains.Length - 3, "more call chain", "more call chains")}");
        }
        text.AppendLine("Report: " + CliPaths.Display(outputPath));
        text.AppendLine(Disclaimer);
        return text.ToString();
    }

    // `Type::Method(parameters)` without the return type or namespaces, for readable chains.
    static string Short(string signature) =>
        Regex.Replace(signature[(signature.IndexOf(' ') + 1)..], @"\b(?:[A-Za-z_]\w*\.)+(?=[A-Za-z_])", "");
}
