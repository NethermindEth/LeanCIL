#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Security.Cryptography;
using System.Text.Json;

var root = Path.Combine(Path.GetTempPath(), "leancil-file-hashing-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
try
{
    var files = new List<(string Name, string Path)>();
    foreach (var size in new[] { 0, 1, 4096, 65535, 65536, 65537, 1048576 })
    {
        var path = Path.Combine(root, size + ".bin");
        var bytes = new byte[size];
        new Random(size).NextBytes(bytes);
        File.WriteAllBytes(path, bytes);
        files.Add((size + ".bin", path));
    }
    var expected = new SortedDictionary<string, string>(StringComparer.Ordinal);
    foreach (var (name, path) in files)
        expected.Add(name, Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path))));
    foreach (var entries in new[] { files.ToArray(), files.AsEnumerable().Reverse().ToArray() })
        if (JsonSerializer.Serialize(HashFiles(entries)) != JsonSerializer.Serialize(expected))
            throw new InvalidOperationException("Parallel hashing changed the manifest bytes.");
    if (HashFiles([]).Count != 0) throw new InvalidOperationException("Empty manifest changed.");

    File.WriteAllText(Path.Combine(root, "cache-manifest.json"), "excluded");
    File.WriteAllText(Path.Combine(root, "cache-receipt.hmac"), "excluded");
    if (!Same(expected, CacheFiles(root))) throw new InvalidOperationException("Cache file selection changed.");
    File.WriteAllText(files[0].Path, "changed");
    if (Same(expected, CacheFiles(root))) throw new InvalidOperationException("A later scan missed a changed file.");

    try
    {
        HashFiles([("missing-a", Path.Combine(root, "missing-a")), ("missing-b", Path.Combine(root, "missing-b"))]);
        throw new InvalidOperationException("Missing files were accepted.");
    }
    catch (FileNotFoundException) { }
    try
    {
        HashFiles([files[0], files[0]]);
        throw new InvalidOperationException("Duplicate manifest keys were accepted.");
    }
    catch (ArgumentException) { }
    Console.WriteLine("PASS parallel file hashes, deterministic manifests, fresh scans and failures");
}
finally { Directory.Delete(root, recursive: true); }
