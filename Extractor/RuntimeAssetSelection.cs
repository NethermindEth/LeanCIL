using System.Text.Json;

namespace Nethermind.LeanCIL;

internal sealed record RuntimeAsset(string Name, string Library, string PackagePath, string AssetPath,
    string Target, string? Rid, string Type, string[] ReferenceAssets);

internal static class RuntimeAssetSelection
{
    internal static JsonDocument Parse(byte[] bytes)
    {
        JsonDocument document = JsonDocument.Parse(bytes, new JsonDocumentOptions { MaxDepth = 64 });
        try { Unique(document.RootElement); return document; }
        catch { document.Dispose(); throw; }
    }

    static void Unique(JsonElement element)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            HashSet<string> names = new(StringComparer.Ordinal);
            foreach (JsonProperty property in element.EnumerateObject())
            {
                if (!names.Add(property.Name)) throw new InvalidDataException("Duplicate discovery JSON property: " + property.Name);
                Unique(property.Value);
            }
        }
        else if (element.ValueKind == JsonValueKind.Array)
            foreach (JsonElement child in element.EnumerateArray()) Unique(child);
    }

    internal static string? RuntimeIdentifier(JsonElement deps)
    {
        string target = deps.GetProperty("runtimeTarget").GetProperty("name").GetString()
            ?? throw new InvalidDataException("Missing deps runtime target.");
        string[] parts = target.Split('/');
        if (parts.Length > 2 || !Framework(parts[0])) throw new InvalidDataException("Contract discovery requires net10.0: " + target);
        return parts.Length == 2 ? parts[1] : null;
    }

    static bool Framework(string target) => target is "net10.0" or ".NETCoreApp,Version=v10.0";

    internal static void ValidateRid(string? rid, FeatureProfile profile)
    {
        if (rid is null) return;
        if (rid.Length > 128 || rid.Any(character => !(char.IsAsciiLetterOrDigit(character) || character is '-' or '.')))
            throw new InvalidDataException("Invalid discovery runtime identifier: " + rid);
        string architecture = rid.EndsWith("-x64", StringComparison.Ordinal) ? "x64" :
            rid.EndsWith("-arm64", StringComparison.Ordinal) ? "arm64" : "";
        if (architecture.Length == 0 || (profile.Architecture != "scalar" && profile.Architecture != architecture))
            throw new InvalidDataException("Runtime identifier does not match the execution profile: " + rid);
    }

    static string[] RidOrder(JsonElement root, string? rid)
    {
        if (rid is null) return [];
        List<string> order = [];
        HashSet<string> active = new(StringComparer.Ordinal);
        HashSet<string> done = new(StringComparer.Ordinal);
        void Visit(string current)
        {
            if (active.Contains(current)) throw new InvalidDataException("Discovery RID fallback cycle: " + current);
            if (!done.Add(current)) return;
            active.Add(current);
            order.Add(current);
            if (order.Count > 128) throw new InvalidDataException("Discovery RID fallback graph is too large.");
            if (root.TryGetProperty("runtimes", out JsonElement graph) && graph.TryGetProperty(current, out JsonElement entry))
            {
                JsonElement imports = entry.ValueKind == JsonValueKind.Object ? entry.GetProperty("#import") : entry;
                foreach (JsonElement parent in imports.EnumerateArray())
                {
                    string next = parent.GetString() ?? throw new InvalidDataException("Invalid RID fallback.");
                    if ((next.EndsWith("-x64", StringComparison.Ordinal) && !rid.EndsWith("-x64", StringComparison.Ordinal)) ||
                        (next.EndsWith("-arm64", StringComparison.Ordinal) && !rid.EndsWith("-arm64", StringComparison.Ordinal)))
                        throw new InvalidDataException("Cross-architecture RID fallback: " + next);
                    Visit(next);
                }
            }
            active.Remove(current);
        }
        Visit(rid);
        return order.ToArray();
    }

    internal static Dictionary<string, RuntimeAsset> Select(JsonElement root, bool deps, string? rid, IReadOnlySet<string> requested)
    {
        JsonElement targets = root.GetProperty("targets");
        string target;
        if (deps)
        {
            target = root.GetProperty("runtimeTarget").GetProperty("name").GetString()!;
            string? declared = RuntimeIdentifier(root);
            if (declared is not null && declared != rid) throw new InvalidDataException("Conflicting deps runtime identifier.");
        }
        else
        {
            string[] choices = targets.EnumerateObject().Where(property =>
                Framework(property.Name.Split('/')[0]) && property.Name.Split('/').Length <= 2 &&
                (property.Name.Split('/').Length == 1 || property.Name.Split('/')[1] == rid)).Select(property => property.Name).ToArray();
            string[] exact = choices.Where(name => rid is not null && name.EndsWith("/" + rid, StringComparison.Ordinal)).ToArray();
            string[] selected = exact.Length > 0 ? exact : choices.Where(name => !name.Contains('/')).ToArray();
            if (selected.Length != 1) throw new InvalidDataException("Missing or ambiguous net10.0 discovery target for RID " + (rid ?? "portable"));
            target = selected[0];
        }
        JsonElement selectedTarget = targets.GetProperty(target);
        JsonElement libraries = root.GetProperty("libraries");
        string[] ridOrder = RidOrder(root, rid);
        Dictionary<string, RuntimeAsset> result = new(StringComparer.Ordinal);
        foreach (JsonProperty library in selectedTarget.EnumerateObject())
        {
            JsonElement metadata = libraries.GetProperty(library.Name);
            string type = metadata.GetProperty("type").GetString()!;
            string packagePath = metadata.TryGetProperty("path", out JsonElement path) ? path.GetString()! : "";
            List<(string Path, int Rank)> candidates = [];
            if (library.Value.TryGetProperty("runtime", out JsonElement runtime))
                candidates.AddRange(runtime.EnumerateObject().Where(asset => Managed(asset.Name) && requested.Contains(Path.GetFileNameWithoutExtension(asset.Name)))
                    .Select(asset => (asset.Name, int.MaxValue)));
            if (library.Value.TryGetProperty("runtimeTargets", out JsonElement runtimeTargets))
                foreach (JsonProperty asset in runtimeTargets.EnumerateObject())
                {
                    if (!Managed(asset.Name) || !requested.Contains(Path.GetFileNameWithoutExtension(asset.Name)) ||
                        asset.Value.GetProperty("assetType").GetString() != "runtime") continue;
                    string selectedRid = asset.Value.GetProperty("rid").GetString()!;
                    int rank = Array.IndexOf(ridOrder, selectedRid);
                    if (rank >= 0) candidates.Add((asset.Name, rank));
                    else if (rid is null) throw new InvalidDataException("Runtime identifier is required for runtime-specific assets: " + library.Name);
                }
            string[] references = library.Value.TryGetProperty("compile", out JsonElement compile)
                ? compile.EnumerateObject().Where(asset => Managed(asset.Name) && requested.Contains(Path.GetFileNameWithoutExtension(asset.Name))).Select(asset => asset.Name).ToArray() : [];
            foreach (IGrouping<string, (string Path, int Rank)> group in candidates.GroupBy(candidate => Path.GetFileNameWithoutExtension(candidate.Path), StringComparer.Ordinal))
            {
                int best = group.Min(candidate => candidate.Rank);
                string[] paths = group.Where(candidate => candidate.Rank == best).Select(candidate => candidate.Path).Distinct(StringComparer.Ordinal).ToArray();
                if (paths.Length != 1) throw new InvalidDataException("Ambiguous runtime assets: " + library.Name + " / " + group.Key);
                if (paths[0].Split('/').Contains("ref", StringComparer.Ordinal))
                    throw new InvalidDataException("Reference asset cannot be a runtime implementation: " + paths[0]);
                RuntimeAsset asset = new(group.Key, library.Name, packagePath, paths[0], target, rid, type,
                    references.Where(reference => Path.GetFileNameWithoutExtension(reference) == group.Key).ToArray());
                if (!result.TryAdd(group.Key, asset)) throw new InvalidDataException("Ambiguous runtime assembly name: " + group.Key);
            }
            foreach (IGrouping<string, string> reference in references.GroupBy(path => Path.GetFileNameWithoutExtension(path)!, StringComparer.Ordinal))
                if (!result.ContainsKey(reference.Key))
                    result.Add(reference.Key, new(reference.Key, library.Name, packagePath, "", target, rid, type, reference.ToArray()));
        }
        return result;
    }

    static bool Managed(string path) => path.EndsWith(".dll", StringComparison.OrdinalIgnoreCase);
}
