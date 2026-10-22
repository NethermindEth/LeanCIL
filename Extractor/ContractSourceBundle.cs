using System.Text.Json;

namespace Nethermind.LeanCIL;

internal sealed record ContractBundleManifest(int Schema, SortedDictionary<string, string> Files, JsonElement Exports);

internal static class ContractSourceBundle
{
    internal static string Publish(string destination, SortedDictionary<string, string> sources, JsonElement exports)
    {
        Directory.CreateDirectory(destination);
        string staging = Path.Combine(destination, ".staging-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(staging);
        try
        {
            SortedDictionary<string, string> files = new(StringComparer.Ordinal);
            foreach ((string relative, string source) in sources)
            {
                if (!Permitted(relative) || (File.GetAttributes(source) & FileAttributes.ReparsePoint) != 0)
                    throw new InvalidDataException("Contract bundle contains an unsupported source path: " + relative);
                string target = Within(staging, relative);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(source, target);
                files[relative] = ContractInterface.Hash(File.ReadAllBytes(target));
            }
            ContractBundleManifest manifest = new(1, files, exports);
            byte[] bytes = JsonSerializer.SerializeToUtf8Bytes(manifest, ContractExportManifest.Json);
            string digest = ContractInterface.Hash(bytes);
            File.WriteAllBytes(Path.Combine(staging, "bundle.json"), bytes);
            string published = Path.Combine(destination, digest);
            if (Directory.Exists(published))
            {
                Validate(published, digest);
                return digest;
            }
            try { Directory.Move(staging, published); }
            catch (IOException) when (Directory.Exists(published)) { Validate(published, digest); }
            return digest;
        }
        finally
        {
            if (Directory.Exists(staging)) Directory.Delete(staging, true);
        }
    }

    internal static ContractBundleManifest Validate(string directory, string expectedDigest)
    {
        if ((File.GetAttributes(directory) & FileAttributes.ReparsePoint) != 0)
            throw new InvalidDataException("Contract source bundles must not be symbolic links.");
        byte[] bytes = File.ReadAllBytes(Path.Combine(directory, "bundle.json"));
        if (ContractInterface.Hash(bytes) != expectedDigest)
            throw new InvalidDataException("Contract source bundle manifest digest mismatch.");
        ContractBundleManifest manifest = JsonSerializer.Deserialize<ContractBundleManifest>(bytes, ContractExportManifest.Json)
            ?? throw new InvalidDataException("Missing contract source bundle manifest.");
        if (manifest.Schema != 1 || manifest.Files is null || manifest.Files.Count == 0)
            throw new InvalidDataException("Invalid contract source bundle manifest.");
        foreach ((string relative, string hash) in manifest.Files)
        {
            string path = Within(directory, relative);
            if (!Permitted(relative) || !ContractInterface.Digest(hash) || !File.Exists(path) ||
                (File.GetAttributes(path) & FileAttributes.ReparsePoint) != 0 || ContractInterface.Hash(File.ReadAllBytes(path)) != hash)
                throw new InvalidDataException("Contract source bundle file is missing or changed: " + relative);
        }
        foreach (string path in Directory.EnumerateFileSystemEntries(directory, "*", SearchOption.AllDirectories))
        {
            if ((File.GetAttributes(path) & FileAttributes.ReparsePoint) != 0)
                throw new InvalidDataException("Contract source bundles must not contain symbolic links.");
            if (Directory.Exists(path)) continue;
            string relative = Path.GetRelativePath(directory, path).Replace('\\', '/');
            if (relative != "bundle.json" && !manifest.Files.ContainsKey(relative))
                throw new InvalidDataException("Contract source bundle contains an unrecorded file: " + relative);
        }
        return manifest;
    }

    static bool Permitted(string relative)
    {
        if (relative == "bundle.json" || relative.Contains('\\') || Path.IsPathRooted(relative)) return false;
        string[] parts = relative.Split('/');
        for (int index = 0; index < parts.Length; index++)
            if (parts[index] is ".git" or "bin" or "obj" or ".work" or "artifacts" or "generated" ||
                (parts[index] == ".lake" && (index + 1 == parts.Length || parts[index + 1] != "packages")))
                return false;
        return Path.GetExtension(relative) is ".lean" or ".toml" or ".json" or ".md" || Path.GetFileName(relative) == "lean-toolchain";
    }

    static string Within(string root, string relative)
    {
        if (Path.IsPathRooted(relative)) throw new InvalidDataException("Absolute bundle path: " + relative);
        string target = Path.GetFullPath(relative, root);
        string back = Path.GetRelativePath(root, target);
        if (back == ".." || back.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            throw new InvalidDataException("Contract bundle path escapes its root: " + relative);
        return target;
    }
}
