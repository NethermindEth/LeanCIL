using Mono.Cecil;
using System.Text.Json;

namespace Nethermind.LeanCIL;

internal sealed class ContractDiscovery
{
    internal const string AttributeName = "Nethermind.LeanCIL.LeanCilContractsAttribute";
    internal const string ResourceName = "LeanCIL.Contracts.Interface";
    readonly string applicationDirectory;
    readonly string? rid;
    readonly Dictionary<string, RuntimeAsset> assets;
    readonly string[] packageRoots;
    readonly List<DiscoveryFile> manifestInputs = [];
    readonly Dictionary<string, byte[]> buffers = new(PathComparer);
    readonly Dictionary<string, ContractInterface> interfaces = new(PathComparer);

    internal ContractDiscovery(string application, FeatureProfile profile, string? depsPath, string? assetsPath,
        string? runtimeIdentifier, IEnumerable<string> packageRoots, IReadOnlySet<string> requested)
    {
        applicationDirectory = Path.GetDirectoryName(Path.GetFullPath(application))!;
        string adjacent = Path.ChangeExtension(Path.GetFullPath(application), ".deps.json");
        depsPath ??= File.Exists(adjacent) ? adjacent : null;
        using JsonDocument? deps = depsPath is null ? null : RuntimeAssetSelection.Parse(ReadManifest(depsPath));
        using JsonDocument? nuget = assetsPath is null ? null : RuntimeAssetSelection.Parse(ReadManifest(assetsPath));
        string? declaredRid = deps is null ? null : RuntimeAssetSelection.RuntimeIdentifier(deps.RootElement);
        if (runtimeIdentifier is not null && declaredRid is not null && runtimeIdentifier != declaredRid)
            throw new InvalidDataException("Explicit runtime identifier conflicts with deps runtime target.");
        rid = runtimeIdentifier ?? declaredRid;
        RuntimeAssetSelection.ValidateRid(rid, profile);
        Dictionary<string, RuntimeAsset> dependencies = deps is null || requested.Count == 0 ? new(StringComparer.Ordinal) : RuntimeAssetSelection.Select(deps.RootElement, true, rid, requested);
        Dictionary<string, RuntimeAsset> packages = nuget is null || requested.Count == 0 ? new(StringComparer.Ordinal) : RuntimeAssetSelection.Select(nuget.RootElement, false, rid, requested);
        foreach ((string name, RuntimeAsset selected) in packages)
            if (dependencies.TryGetValue(name, out RuntimeAsset? prior) &&
                (prior.Library != selected.Library || prior.AssetPath != selected.AssetPath))
                throw new InvalidDataException("Conflicting deps/NuGet runtime asset: " + name);
        assets = dependencies;
        foreach ((string name, RuntimeAsset selected) in packages) assets[name] = selected;
        this.packageRoots = packageRoots.Select(Path.GetFullPath).Concat(nuget is null ||
            !nuget.RootElement.TryGetProperty("packageFolders", out JsonElement folders) ? [] :
                folders.EnumerateObject().Select(property => Path.GetFullPath(property.Name)))
            .Distinct(PathComparer).ToArray();
    }

    static StringComparer PathComparer => OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;

    byte[] ReadManifest(string path)
    {
        string full = Path.GetFullPath(path);
        byte[] bytes = ReadFile(full);
        manifestInputs.Add(new(full, ContractInterface.Hash(bytes)));
        return bytes;
    }

    byte[] ReadFile(string path)
    {
        string full = Path.GetFullPath(path);
        if (!buffers.TryGetValue(full, out byte[]? bytes)) buffers.Add(full, bytes = File.ReadAllBytes(full));
        return bytes;
    }

    internal ContractInterface Sidecar(string path)
    {
        string full = Path.GetFullPath(path);
        if (!interfaces.TryGetValue(full, out ContractInterface? contract))
            interfaces.Add(full, contract = ContractInterface.Read(ReadFile(full)));
        return contract;
    }

    internal static string Contained(string root, string relative)
    {
        if (string.IsNullOrWhiteSpace(relative) || relative.Contains('\\') || relative.Contains(':') || relative.StartsWith('/') ||
            relative.Split('/').Any(part => part is "" or "." or ".."))
            throw new InvalidDataException("Unsafe discovery asset path: " + relative);
        string fullRoot = Canonical(Path.GetFullPath(root));
        string selected = Path.GetFullPath(relative.Replace('/', Path.DirectorySeparatorChar), fullRoot);
        string current = fullRoot;
        foreach (string part in relative.Split('/'))
        {
            current = Path.Combine(current, part);
            if (File.Exists(current) || Directory.Exists(current)) current = Canonical(current);
            string remainder = Path.GetRelativePath(fullRoot, current);
            if (Path.IsPathRooted(remainder) || remainder == ".." || remainder.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                throw new InvalidDataException("Discovery asset escapes its declared root: " + relative);
        }
        return selected;
    }

    static string Canonical(string path)
    {
        if (!File.Exists(path) && !Directory.Exists(path)) return path;
        FileSystemInfo entry = Directory.Exists(path) ? new DirectoryInfo(path) : new FileInfo(path);
        return entry.ResolveLinkTarget(true)?.FullName ?? path;
    }

    IEnumerable<string> AssetPaths(RuntimeAsset asset, string relative, bool flattened)
    {
        yield return Contained(applicationDirectory, relative);
        if (flattened) yield return Contained(applicationDirectory, Path.GetFileName(relative));
        if (asset.Type == "package")
            foreach (string root in packageRoots)
                yield return Contained(Contained(root, asset.PackagePath), relative);
    }

    (string Path, byte[] Bytes)? SelectFile(IEnumerable<string> paths, string name, bool required)
    {
        (string Path, byte[] Bytes)? selected = null;
        foreach (string path in paths.Distinct(PathComparer).Where(File.Exists))
        {
            byte[] bytes = ReadFile(path);
            if (selected is { } prior && !prior.Bytes.AsSpan().SequenceEqual(bytes))
                throw new InvalidDataException("Ambiguous discovery files for " + name + ": " + prior.Path + ", " + path);
            selected ??= (Path.GetFullPath(path), bytes);
        }
        if (selected is null && required) throw new InvalidDataException("Selected runtime asset is missing: " + name);
        return selected;
    }

    internal string? FindSidecar(string name, string? implementationOverride, string expectedInterface)
    {
        (string Path, byte[] Bytes)? implementation = Implementation(name, implementationOverride, null, false);
        List<string> roots = [applicationDirectory];
        string? advertised = null;
        if (implementation is { } dll)
        {
            roots.Add(Path.GetDirectoryName(dll.Path)!);
            using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(dll.Bytes));
            advertised = AttributeDigest(module);
        }
        if (assets.TryGetValue(name, out RuntimeAsset? asset))
        {
            foreach (string root in packageRoots)
                if (asset.Type == "package") roots.Add(Contained(root, asset.PackagePath));
            foreach (string reference in asset.ReferenceAssets)
            {
                (string Path, byte[] Bytes)? selected = SelectFile(AssetPaths(asset, reference, false), name + " reference", false);
                if (selected is not { } file) continue;
                using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(file.Bytes));
                string? digest = AttributeDigest(module);
                if (digest is not null && advertised is not null && advertised != digest)
                    throw new InvalidDataException("Reference/runtime contract attribute mismatch: " + name);
                advertised ??= digest;
            }
        }
        if (advertised is not null && advertised != expectedInterface)
            throw new InvalidDataException("Contract attribute differs from independent interface digest: " + name);
        List<string> candidates = [];
        foreach (string root in roots.Distinct(PathComparer))
        {
            candidates.Add(Contained(root, name + ".leancil.contracts"));
            if (advertised is not null) candidates.Add(Contained(root, "contracts/" + advertised + ".leancil.contracts"));
        }
        string[] found = candidates.Distinct(PathComparer).Where(File.Exists).ToArray();
        if (found.Length == 0) return null;
        byte[] first = ReadFile(found[0]);
        if (found.Skip(1).Any(path => !ReadFile(path).AsSpan().SequenceEqual(first)))
            throw new InvalidDataException("Conflicting discovered contract sidecars: " + name);
        return found[0];
    }

    (string Path, byte[] Bytes)? Implementation(string name, string? explicitPath, string? sidecar, bool required)
    {
        if (explicitPath is not null)
        {
            string full = Path.GetFullPath(explicitPath);
            return (full, ReadFile(full));
        }
        if (assets.TryGetValue(name, out RuntimeAsset? asset))
        {
            if (asset.AssetPath.Length > 0)
                return SelectFile(AssetPaths(asset, asset.AssetPath, true), name + " / " + asset.Target, required);
            if (required) throw new InvalidDataException("Reference-only discovery located the interface but no runtime implementation: " + name);
            return null;
        }
        List<string> adjacent = [];
        if (sidecar is not null) adjacent.Add(Path.Combine(Path.GetDirectoryName(Path.GetFullPath(sidecar))!, name + ".dll"));
        adjacent.Add(Path.Combine(applicationDirectory, name + ".dll"));
        // Preserve the existing explicit-sidecar adjacent-DLL preference.
        string? path = adjacent.FirstOrDefault(File.Exists);
        if (path is not null) return (path, ReadFile(path));
        if (required) throw new InvalidDataException("Runtime implementation is missing; a reference assembly or discovery attribute cannot certify it: " + name);
        return null;
    }

    internal ImportResolution.Source Source(string sidecar, string? implementationOverride, string expectedHash, string expectedInterface)
    {
        if (!ContractInterface.Digest(expectedHash))
            throw new InvalidDataException("Import requires an independently supplied SHA-256: --import-sha256 Lib=<hex>.");
        if (!ContractInterface.Digest(expectedInterface))
            throw new InvalidDataException("Import requires an independently supplied interface digest: --import-interface-sha256 Lib=<hex>.");
        string fullSidecar = Path.GetFullPath(sidecar);
        byte[] sidecarBytes = ReadFile(fullSidecar);
        ContractInterface contract = Sidecar(fullSidecar);
        string name = AssemblyNameReference.Parse(contract.AssemblyIdentity).Name;
        (string implementationPath, byte[] implementationBytes) = Implementation(name, implementationOverride, fullSidecar, true)!.Value;
        List<DiscoveryFile> inputs = [.. manifestInputs];
        RuntimeAsset? asset = assets.GetValueOrDefault(name);
        if (asset is not null)
            foreach (string reference in asset.ReferenceAssets)
            {
                (string Path, byte[] Bytes)? selected = SelectFile(AssetPaths(asset, reference, false), name + " reference", false);
                if (selected is not { } file) continue;
                using ModuleDefinition referenceModule = ModuleDefinition.ReadModule(new MemoryStream(file.Bytes));
                string? referenceDigest = AttributeDigest(referenceModule);
                if (referenceDigest is not null && referenceDigest != expectedInterface)
                    throw new InvalidDataException("Reference contract attribute differs from independent interface digest: " + name);
                inputs.Add(new(file.Path, ContractInterface.Hash(file.Bytes)));
            }
        // Admission hashes and inspects this exact DLL buffer; it never reopens it.
        ContractDiscoveryProvenance provenance = new("net10.0", rid, asset?.Library, asset?.AssetPath,
            "sidecar", inputs.Distinct().ToArray());
        return new(fullSidecar, implementationPath, expectedHash, expectedInterface,
            new(sidecarBytes, implementationBytes, contract), provenance);
    }

    internal static string? AttributeDigest(ModuleDefinition module)
    {
        CustomAttribute[] attributes = module.Assembly.CustomAttributes.Where(attribute => attribute.AttributeType.FullName == AttributeName).ToArray();
        if (attributes.Length == 0) return null;
        if (attributes.Length != 1 || attributes[0].ConstructorArguments.Count != 1 ||
            attributes[0].ConstructorArguments[0].Type.FullName != "System.String" ||
            attributes[0].ConstructorArguments[0].Value is not string digest || !ContractInterface.Digest(digest))
            throw new InvalidDataException("Invalid or duplicate LeanCilContracts attribute.");
        return digest;
    }

    internal static bool ValidateResource(ModuleDefinition module, ContractInterface contract)
    {
        Resource[] resources = module.Resources.Where(resource => resource.Name == ResourceName).ToArray();
        if (resources.Length == 0) return false;
        if (resources.Length != 1 || resources[0] is not EmbeddedResource embedded)
            throw new InvalidDataException("Invalid or duplicate embedded contract interface resource.");
        ContractInterface.ValidateDescriptor(embedded.GetResourceData(), contract);
        return true;
    }
}
