using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Runs extraction and its validators over explicit method/profile pairs; it never checks a proof.
internal static class Blockers
{
    const string Usage = "Usage: leancil blockers assembly.dll --manifest manifest.json [--output blockers.json] [--assembly 'assembly name or full identity']";
    const string Disclaimer = "Admission only: admitted entries are extractable under their profile; nothing here is proved.";

    sealed record Site(string Signature, string Profile, string[] Chain);

    sealed record Finding(string Method, int? IlOffset, string? Instruction, string? Source, string Message)
    {
        internal List<Site> Sites { get; } = [];
        internal string Id { get; set; } = "";
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
            using var module = ModuleDefinition.ReadModule(new MemoryStream(assembly));
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
                    using var original = ModuleDefinition.ReadModule(new MemoryStream(assembly));
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
            foreach (var failure in blocked)
            {
                int? offset = failure.At?.Offset ?? (Regex.Match(failure.Error.Message, @"\bIL_([0-9a-f]{4,})\b") is { Success: true } label
                    ? Convert.ToInt32(label.Groups[1].Value, 16) : null);
                var key = $"{failure.Method.FullName}\n{offset}\n{failure.Error.Message}";
                if (!findings.TryGetValue(key, out var finding))
                    findings[key] = finding = new(failure.Method.FullName, offset, failure.At?.ToString(),
                        offset is int at ? Symbols.Location(failure.Method, at, Path.GetFileName) : null, failure.Error.Message);
                if (!finding.Sites.Any(s => s.Signature == failure.Chain[0].FullName && s.Profile == profileName))
                    finding.Sites.Add(new(failure.Chain[0].FullName, profileName, failure.Chain.Select(m => m.FullName).ToArray()));
                if (!entryFindings.Contains(finding)) entryFindings.Add(finding);
            }
            outcomes.Add(new(signature, profileName, "blocked", blocked[0].Chain[0].FullName, null, null, entryFindings));
        }

        // The most widely shared blockers lead; identifiers follow that order.
        var ordered = findings.Values.OrderByDescending(f => f.Sites.Count).ThenBy(f => f.Method, StringComparer.Ordinal)
            .ThenBy(f => f.IlOffset ?? -1).ThenBy(f => f.Message, StringComparer.Ordinal).ToArray();
        for (var i = 0; i < ordered.Length; i++) ordered[i].Id = $"B{i + 1}";

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
                id = f.Id, method = f.Method, ilOffset = f.IlOffset, instruction = f.Instruction, source = f.Source, message = f.Message,
                entries = f.Sites.Select(s => new { signature = s.Signature, profile = s.Profile, chain = s.Chain })
            })
        }, new JsonSerializerOptions { WriteIndented = true });
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, report + "\n", new UTF8Encoding(false));
        Console.Write(Summary(identity, outcomes, ordered, outputPath));
        return 0;
    }

    static string Summary(string identity, List<Outcome> outcomes, Finding[] findings, string outputPath)
    {
        static string Line(string text) => text.Split('\n')[0];
        var text = new StringBuilder();
        text.AppendLine($"Admission of {outcomes.Count} entr{(outcomes.Count == 1 ? "y" : "ies")} in {identity}: " +
            $"{outcomes.Count(o => o.Status == "admitted")} admitted, {outcomes.Count(o => o.Status == "blocked")} blocked, " +
            $"{outcomes.Count(o => o.Status == "notChecked")} not checked");
        foreach (var outcome in outcomes)
            text.AppendLine($"  {outcome.Status switch { "admitted" => "admitted   ", "blocked" => "blocked    ", _ => "not checked" }} " +
                $"{outcome.Method ?? outcome.Signature ?? "(no signature)"} [{outcome.Profile ?? "no profile"}]" +
                (outcome.Status == "admitted" ? $" ({outcome.ReachableMethods} reachable method{(outcome.ReachableMethods == 1 ? "" : "s")})" :
                 outcome.Status == "blocked" ? ": " + string.Join(", ", outcome.Findings.Select(f => f.Id)) : ": " + Line(outcome.Reason!)));
        if (findings.Length > 0) text.AppendLine($"Blockers ({findings.Length} distinct):");
        foreach (var finding in findings)
        {
            text.AppendLine($"  {finding.Id} {Line(finding.Message)}");
            text.AppendLine($"     in {finding.Method}" + (finding.IlOffset is int offset ? $" at IL_{offset:x4}" : "") +
                (finding.Source is null ? "" : $" ({finding.Source})"));
            var profiles = finding.Sites.Select(s => s.Profile).Distinct().ToArray();
            var chains = finding.Sites.Select(s => string.Join(" -> ", s.Chain.Select(Short))).Distinct().ToArray();
            text.AppendLine($"     {finding.Sites.Count} entr{(finding.Sites.Count == 1 ? "y" : "ies")}; profiles: {string.Join(", ", profiles)}");
            foreach (var chain in chains.Take(3)) text.AppendLine("     via " + chain);
            if (chains.Length > 3) text.AppendLine($"     and {chains.Length - 3} more call chains");
        }
        text.AppendLine("Report: " + CliPaths.Display(outputPath));
        text.AppendLine(Disclaimer);
        return text.ToString();
    }

    // `Type::Method(parameters)` without the return type or namespace, for readable chains.
    static string Short(string signature)
    {
        var name = signature[(signature.IndexOf(' ') + 1)..];
        var separator = name.IndexOf("::", StringComparison.Ordinal);
        var type = name[..separator];
        return type[(type.LastIndexOf('.') + 1)..] + name[separator..];
    }
}
