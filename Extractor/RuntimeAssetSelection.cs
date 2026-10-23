using System.Text.Json;

namespace Nethermind.LeanCIL;

// AppLocal assets come from deps.json and are probed in the application directory like the host does.
internal sealed record RuntimeAsset(string Name, string Library, string Type, string PackagePath, string AssetPath,
    bool AppLocal, string? LocalPath, string? AssetRid, string[] ReferenceAssets);

internal static class RuntimeAssetSelection
{
    // Architecture segments of .NET RIDs; a fallback RID ending in another one is cross-architecture.
    static readonly HashSet<string> Architectures = new(StringComparer.Ordinal)
        { "x64", "x86", "arm", "arm64", "armel", "armv6", "loongarch64", "mips64", "ppc64le", "riscv64", "s390x", "wasm" };

    internal static JsonDocument Parse(byte[] bytes)
    {
        JsonDocument document;
        try { document = JsonDocument.Parse(bytes, new JsonDocumentOptions { MaxDepth = 64 }); }
        catch (JsonException error) { throw new InvalidDataException("Invalid discovery JSON: " + error.Message); }
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

    static JsonElement Object(JsonElement parent, string name) =>
        parent.ValueKind == JsonValueKind.Object && parent.TryGetProperty(name, out JsonElement value) && value.ValueKind == JsonValueKind.Object
            ? value : throw new InvalidDataException("Discovery JSON requires object: " + name);

    static JsonElement? OptionalObject(JsonElement parent, string name) =>
        !parent.TryGetProperty(name, out JsonElement value) ? null :
            value.ValueKind == JsonValueKind.Object ? value : throw new InvalidDataException("Discovery JSON requires object: " + name);

    static string Text(JsonElement parent, string name) =>
        parent.ValueKind == JsonValueKind.Object && parent.TryGetProperty(name, out JsonElement value) && value.ValueKind == JsonValueKind.String
            ? value.GetString()! : throw new InvalidDataException("Discovery JSON requires string: " + name);

    static string? OptionalText(JsonElement parent, string name) =>
        !parent.TryGetProperty(name, out JsonElement value) ? null :
            value.ValueKind == JsonValueKind.String ? value.GetString()! : throw new InvalidDataException("Discovery JSON requires string: " + name);

    internal static string? RuntimeIdentifier(JsonElement deps)
    {
        string target = Text(Object(deps, "runtimeTarget"), "name");
        string[] parts = target.Split('/');
        if (parts.Length > 2 || !Framework(parts[0])) throw new InvalidDataException("Contract discovery requires net10.0: " + target);
        return parts.Length == 2 ? parts[1] : null;
    }

    static bool Framework(string target) => target is "net10.0" or ".NETCoreApp,Version=v10.0";

    internal static string Architecture(string rid)
    {
        if (rid.Length > 128 || rid.Length == 0 || rid.Any(character => !(char.IsAsciiLetterOrDigit(character) || character is '-' or '.')))
            throw new InvalidDataException("Invalid discovery runtime identifier: " + rid);
        string architecture = rid[(rid.LastIndexOf('-') + 1)..];
        if (architecture is not ("x64" or "arm64"))
            throw new InvalidDataException("Discovery requires an x64 or arm64 runtime identifier: " + rid);
        return architecture;
    }

    // NuGet's RuntimeGraph.ExpandRuntime order: the RID, then its imports breadth-first.
    // The graph is the SDK's PortableRuntimeIdentifierGraph.json, never a manifest section.
    internal static string[] Expand(JsonElement graph, string rid)
    {
        string architecture = Architecture(rid);
        JsonElement runtimes = Object(graph, "runtimes");
        List<string> order = [rid];
        HashSet<string> seen = new(StringComparer.Ordinal) { rid };
        Queue<string> pending = new(Imports(runtimes, rid));
        while (pending.TryDequeue(out string? next))
        {
            if (!seen.Add(next)) continue;
            string segment = next[(next.LastIndexOf('-') + 1)..];
            if (next.Contains('-') && Architectures.Contains(segment) && segment != architecture)
                throw new InvalidDataException("Cross-architecture RID fallback: " + rid + " -> " + next);
            order.Add(next);
            if (order.Count > 1024) throw new InvalidDataException("Discovery RID fallback graph is too large.");
            foreach (string parent in Imports(runtimes, next)) pending.Enqueue(parent);
        }
        return order.ToArray();
    }

    static IEnumerable<string> Imports(JsonElement runtimes, string rid)
    {
        if (!runtimes.TryGetProperty(rid, out JsonElement entry)) return [];
        if (entry.ValueKind != JsonValueKind.Object || !entry.TryGetProperty("#import", out JsonElement imports) ||
            imports.ValueKind != JsonValueKind.Array || imports.EnumerateArray().Any(item => item.ValueKind != JsonValueKind.String))
            throw new InvalidDataException("Invalid RID graph entry: " + rid);
        return imports.EnumerateArray().Select(item => item.GetString()!).ToArray();
    }

    // Host and NuGet replace a library's whole runtime asset group with its best RID group.
    internal static Dictionary<string, RuntimeAsset> Select(JsonElement root, bool deps, string? rid, Func<string[]> fallback,
        IReadOnlySet<string> requested)
    {
        JsonElement targets = Object(root, "targets");
        string target;
        if (deps)
        {
            target = Text(Object(root, "runtimeTarget"), "name");
            if (RuntimeIdentifier(root) is { } declared && declared != rid)
                throw new InvalidDataException("Explicit runtime identifier conflicts with deps runtime target.");
        }
        else
        {
            string[] choices = targets.EnumerateObject().Select(property => property.Name)
                .Where(name => name.Split('/') is [string framework] && Framework(framework) ||
                    name.Split('/') is [string ridFramework, string targetRid] && Framework(ridFramework) && targetRid == rid).ToArray();
            string[] exact = choices.Where(name => name.Contains('/')).ToArray();
            string[] selected = exact.Length > 0 ? exact : choices;
            if (selected.Length != 1) throw new InvalidDataException("Missing or ambiguous net10.0 discovery target for RID " + (rid ?? "portable"));
            target = selected[0];
        }
        JsonElement selectedTarget = Object(targets, target);
        JsonElement libraries = Object(root, "libraries");
        Dictionary<string, RuntimeAsset> result = new(StringComparer.Ordinal);
        bool Requested(string path) => Managed(path) && requested.Contains(Path.GetFileNameWithoutExtension(path));
        foreach (JsonProperty library in selectedTarget.EnumerateObject())
        {
            JsonElement metadata = Object(libraries, library.Name);
            string type = Text(metadata, "type");
            string packagePath = OptionalText(metadata, "path") ?? "";
            JsonElement? runtime = OptionalObject(library.Value, "runtime");
            JsonElement? runtimeTargets = OptionalObject(library.Value, "runtimeTargets");
            JsonElement? compile = OptionalObject(library.Value, "compile");
            JsonProperty[] portable = runtime?.EnumerateObject().ToArray() ?? [];
            (JsonProperty Asset, string Rid)[] specific = runtimeTargets?.EnumerateObject()
                .Where(asset => Text(asset.Value, "assetType") == "runtime")
                .Select(asset => (asset, Text(asset.Value, "rid"))).ToArray() ?? [];
            string[] references = compile?.EnumerateObject().Select(asset => asset.Name).Where(Requested).ToArray() ?? [];
            if (!portable.Any(asset => Requested(asset.Name)) && !specific.Any(asset => Requested(asset.Asset.Name)) && references.Length == 0)
                continue;
            JsonProperty[] group = portable;
            string? groupRid = null;
            if (specific.Length > 0)
            {
                if (rid is null) throw new InvalidDataException("Runtime identifier is required for runtime-specific assets: " + library.Name);
                string[] order = fallback();
                groupRid = order.FirstOrDefault(candidate => specific.Any(asset => asset.Rid == candidate));
                if (groupRid is not null) group = specific.Where(asset => asset.Rid == groupRid).Select(asset => asset.Asset).ToArray();
            }
            foreach (IGrouping<string, JsonProperty> named in group.Where(asset => Requested(asset.Name))
                .GroupBy(asset => Path.GetFileNameWithoutExtension(asset.Name), StringComparer.Ordinal))
            {
                if (named.Count() != 1) throw new InvalidDataException("Ambiguous runtime assets: " + library.Name + " / " + named.Key);
                JsonProperty asset = named.Single();
                if (asset.Name.Split('/').Contains("ref", StringComparer.Ordinal))
                    throw new InvalidDataException("Reference asset cannot be a runtime implementation: " + asset.Name);
                RuntimeAsset selected = new(named.Key, library.Name, type, packagePath, asset.Name, deps,
                    deps ? OptionalText(asset.Value, "localPath") : null, groupRid,
                    references.Where(reference => Path.GetFileNameWithoutExtension(reference) == named.Key).ToArray());
                if (!result.TryAdd(named.Key, selected)) throw new InvalidDataException("Ambiguous runtime assembly name: " + named.Key);
            }
            foreach (IGrouping<string, string> reference in references.GroupBy(path => Path.GetFileNameWithoutExtension(path), StringComparer.Ordinal))
                if (!result.ContainsKey(reference.Key))
                    result.Add(reference.Key, new(reference.Key, library.Name, type, packagePath, "", deps, null, null, reference.ToArray()));
        }
        return result;
    }

    static bool Managed(string path) => path.EndsWith(".dll", StringComparison.OrdinalIgnoreCase);
}
