using Mono.Cecil;
using System.Text.Json;

namespace Nethermind.LeanCIL;

// Turns SDK deps/NuGet asset selection into explicit --import arguments. It only
// locates files: extraction still requires independent implementation and interface pins.
internal static class ImportResolver
{
    internal const string Usage = "Usage: leancil resolve-imports App.dll --library Lib... [--deps App.deps.json] [--assets obj/project.assets.json] " +
        "[--runtime-identifier RID] [--rid-graph PortableRuntimeIdentifierGraph.json] [--package-root directory]... [--profile name|@profile.json] [--output resolved.json]";
    internal const string AttributeName = "Nethermind.LeanCIL.LeanCilContractsAttribute";

    internal sealed record Resolved(string Assembly, string Library, string AssetPath, string? AssetRuntimeIdentifier,
        string Implementation, string Sidecar, string? AdvertisedInterfaceDigest);

    static StringComparer PathComparer => OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;

    internal static int Run(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal)) throw new ArgumentException(Usage);
        string application = Path.GetFullPath(args[0]);
        SortedSet<string> libraries = new(StringComparer.Ordinal);
        List<string> roots = [];
        Dictionary<string, string> single = new(StringComparer.Ordinal);
        for (int index = 1; index < args.Length; index++)
        {
            string option = args[index];
            if (option is not ("--library" or "--deps" or "--assets" or "--runtime-identifier" or "--rid-graph" or "--package-root" or "--profile" or "--output"))
                throw new ArgumentException("Unknown option: " + option + "\n" + Usage);
            if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException(option + " requires a value.");
            if (option == "--library") { if (!libraries.Add(args[index])) throw new ArgumentException("Duplicate --library: " + args[index]); }
            else if (option == "--package-root") roots.Add(Path.GetFullPath(args[index]));
            else if (!single.TryAdd(option, args[index])) throw new ArgumentException("Duplicate " + option + " option.");
        }
        if (libraries.Count == 0) throw new ArgumentException("resolve-imports requires at least one --library.\n" + Usage);
        string? Option(string name) => single.GetValueOrDefault(name);
        FeatureProfile? profile = Option("--profile") is { } name ? FeatureProfile.Select(name) : null;
        (string? rid, string[] fallback, Resolved[] imports) = Resolve(application, libraries, Option("--deps") is { } deps ? Path.GetFullPath(deps) : null,
            Option("--assets") is { } assets ? Path.GetFullPath(assets) : null, Option("--runtime-identifier"),
            Option("--rid-graph") is { } graph ? Path.GetFullPath(graph) : null, roots, profile);
        string[] arguments = imports.SelectMany(import => new[]
            { "--import", import.Sidecar, "--import-implementation", import.Assembly + "=" + import.Implementation }).ToArray();
        string json = JsonSerializer.Serialize(new
        {
            schema = 1, runtimeIdentifier = rid, ridFallback = fallback,
            imports = imports.Select(import => JsonSerializer.SerializeToElement(import, ContractInterface.Json)),
            arguments,
            notice = "Locations only. Pin each implementation with --import-sha256 and its interface with --import-interface-sha256 from an independent source."
        }, new JsonSerializerOptions { WriteIndented = true }) + "\n";
        if (Option("--output") is { } output)
        {
            string destination = Path.GetFullPath(output);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, json);
            Console.WriteLine("Resolved " + imports.Length + " import(s): " + destination);
        }
        else Console.Write(json);
        return 0;
    }

    internal static (string? Rid, string[] Fallback, Resolved[] Imports) Resolve(string application, IReadOnlySet<string> requested,
        string? depsPath, string? assetsPath, string? explicitRid, string? graphPath, IEnumerable<string> packageRoots, FeatureProfile? profile)
    {
        string applicationDirectory = Path.GetDirectoryName(application)!;
        string adjacent = Path.ChangeExtension(application, ".deps.json");
        depsPath ??= File.Exists(adjacent) ? adjacent : null;
        if (depsPath is null && assetsPath is null) throw new ArgumentException("resolve-imports requires --deps or --assets (or an adjacent App.deps.json).");
        using JsonDocument? deps = depsPath is null ? null : RuntimeAssetSelection.Parse(File.ReadAllBytes(depsPath));
        using JsonDocument? nuget = assetsPath is null ? null : RuntimeAssetSelection.Parse(File.ReadAllBytes(assetsPath));
        string? declared = deps is null ? null : RuntimeAssetSelection.RuntimeIdentifier(deps.RootElement);
        if (explicitRid is not null && declared is not null && explicitRid != declared)
            throw new InvalidDataException("Explicit runtime identifier conflicts with deps runtime target.");
        string? rid = explicitRid ?? declared;
        string? architecture = rid is null ? null : RuntimeAssetSelection.Architecture(rid);
        if (architecture is not null && profile is not null && profile.Architecture != "scalar" && profile.Architecture != architecture)
            throw new InvalidDataException("Runtime identifier does not match the execution profile: " + rid);
        string[]? fallback = null;
        string[] Fallback()
        {
            if (fallback is not null) return fallback;
            if (graphPath is null) throw new InvalidDataException("RID fallback for runtime-specific assets requires --rid-graph (the SDK's PortableRuntimeIdentifierGraph.json).");
            using JsonDocument graph = RuntimeAssetSelection.Parse(File.ReadAllBytes(graphPath));
            return fallback = RuntimeAssetSelection.Expand(graph.RootElement, rid!);
        }
        Dictionary<string, RuntimeAsset> selected = deps is null ? new(StringComparer.Ordinal)
            : RuntimeAssetSelection.Select(deps.RootElement, true, rid, Fallback, requested);
        if (nuget is not null)
            foreach ((string name, RuntimeAsset asset) in RuntimeAssetSelection.Select(nuget.RootElement, false, rid, Fallback, requested))
            {
                if (!selected.TryGetValue(name, out RuntimeAsset? prior)) selected.Add(name, asset);
                else if (prior.Library != asset.Library || prior.AssetPath != asset.AssetPath)
                    throw new InvalidDataException("Conflicting deps/NuGet runtime asset: " + name);
            }
        string[] roots = packageRoots.Concat(nuget is not null && nuget.RootElement.TryGetProperty("packageFolders", out JsonElement folders) &&
                folders.ValueKind == JsonValueKind.Object ? folders.EnumerateObject().Select(folder => folder.Name) : [])
            .Select(root => Path.GetFullPath(root)).Distinct(PathComparer).ToArray();
        Dictionary<string, byte[]> buffers = new(PathComparer);
        byte[] Read(string path) => buffers.TryGetValue(path, out byte[]? bytes) ? bytes : buffers[path] = File.ReadAllBytes(path);
        List<Resolved> resolved = [];
        foreach (string name in requested)
        {
            if (!selected.TryGetValue(name, out RuntimeAsset? asset))
                throw new InvalidDataException("Requested import is not a net10.0 asset in the supplied manifests: " + name);
            string[] packageDirectories = asset.Type == "package" ? roots.Select(root => Contained(root, asset.PackagePath)).ToArray() : [];
            IEnumerable<string> Candidates(string relative, string? local)
            {
                // hostpolicy probe_deps_entry: localPath, else a RID asset's relative path, else the bare file name.
                if (asset.AppLocal) yield return Contained(applicationDirectory, local ?? (asset.AssetRid is null ? Path.GetFileName(relative) : relative));
                foreach (string directory in packageDirectories) yield return Contained(directory, relative);
            }
            (string Path, byte[] Bytes)? Single(IEnumerable<string> paths, string label)
            {
                (string Path, byte[] Bytes)? found = null;
                foreach (string path in paths.Distinct(PathComparer).Where(File.Exists))
                {
                    byte[] bytes = Read(path);
                    if (found is { } prior && !prior.Bytes.AsSpan().SequenceEqual(bytes))
                        throw new InvalidDataException("Ambiguous discovery files for " + label + ": " + prior.Path + ", " + path);
                    found ??= (path, bytes);
                }
                return found;
            }
            string? advertised = null;
            foreach (string reference in asset.ReferenceAssets)
                if (Single(packageDirectories.Select(directory => Contained(directory, reference)), name + " reference") is { } file)
                    advertised = Agree(advertised, AttributeDigest(file.Bytes), name);
            if (asset.AssetPath.Length == 0)
                throw new InvalidDataException("Reference-only discovery located the interface but no runtime implementation: " + name);
            (string implementation, byte[] implementationBytes) = Single(Candidates(asset.AssetPath, asset.LocalPath), name + " / " + asset.AssetPath)
                ?? throw new InvalidDataException("Selected runtime asset is missing: " + name + " / " + asset.AssetPath);
            advertised = Agree(advertised, AttributeDigest(implementationBytes), name);
            List<string> sidecars = [];
            foreach (string directory in new[] { applicationDirectory, Path.GetDirectoryName(implementation)! }.Concat(packageDirectories).Distinct(PathComparer))
            {
                sidecars.Add(Contained(directory, name + ".leancil.contracts"));
                if (advertised is not null) sidecars.Add(Contained(directory, "contracts/" + advertised + ".leancil.contracts"));
            }
            (string sidecar, byte[] sidecarBytes) = Single(sidecars, name + " contract sidecar")
                ?? throw new InvalidDataException("No contract sidecar located for " + name + ".");
            ContractInterface contract = ContractInterface.Read(sidecarBytes);
            if (AssemblyNameReference.Parse(contract.AssemblyIdentity).Name != name)
                throw new InvalidDataException("Located contract sidecar names another assembly: " + sidecar);
            if (advertised is not null && contract.InterfaceDigest != advertised)
                throw new InvalidDataException("Contract attribute differs from the located sidecar interface digest: " + name);
            resolved.Add(new(name, asset.Library, asset.AssetPath, asset.AssetRid, implementation, sidecar, advertised));
        }
        return (rid, fallback ?? [], resolved.ToArray());
    }

    static string? Agree(string? prior, string? digest, string name) =>
        prior is not null && digest is not null && prior != digest
            ? throw new InvalidDataException("Reference/runtime contract attribute mismatch: " + name) : prior ?? digest;

    // Lexical containment only: located bytes are untrusted until extraction checks the pins.
    internal static string Contained(string root, string relative)
    {
        if (string.IsNullOrWhiteSpace(relative) || relative.Contains('\\') || relative.Contains(':') || relative.StartsWith('/') ||
            relative.Split('/').Any(part => part is "" or "." or ".."))
            throw new InvalidDataException("Unsafe discovery asset path: " + relative);
        return Path.GetFullPath(relative.Replace('/', Path.DirectorySeparatorChar), Path.GetFullPath(root));
    }

    internal static string? AttributeDigest(byte[] assembly)
    {
        using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(assembly));
        CustomAttribute[] attributes = module.Assembly.CustomAttributes.Where(attribute => attribute.AttributeType.FullName == AttributeName).ToArray();
        if (attributes.Length == 0) return null;
        if (attributes.Length != 1 || attributes[0].ConstructorArguments.Count != 1 ||
            attributes[0].ConstructorArguments[0].Type.FullName != "System.String" ||
            attributes[0].ConstructorArguments[0].Value is not string digest || !ContractInterface.Digest(digest))
            throw new InvalidDataException("Invalid or duplicate LeanCilContracts attribute.");
        return digest;
    }
}
