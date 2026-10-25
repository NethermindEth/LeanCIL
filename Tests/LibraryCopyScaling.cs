#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// Synthetic performance fixture only: never supplied to a verifier or certified as Lean output.
var donor = Path.GetFullPath(args.FirstOrDefault() ?? At(".lake/build"));
var root = At("artifacts/CertifiedCopyProfile-" + Guid.NewGuid().ToString("N"));
var source = Path.Combine(root, "source");
Directory.CreateDirectory(source);
foreach (var path in Directory.EnumerateFiles(donor, "*", SearchOption.AllDirectories))
{
    var name = Path.GetRelativePath(donor, path).Replace('\\', '/');
    if (!(name.StartsWith("lib/lean/CIL/", StringComparison.Ordinal) ||
        name.StartsWith("lib/lean/CIL.", StringComparison.Ordinal) ||
        name.StartsWith("ir/CIL/", StringComparison.Ordinal) ||
        name.StartsWith("ir/CIL.", StringComparison.Ordinal) ||
        name.StartsWith("bin/", StringComparison.Ordinal))) continue;
    var target = Path.Combine(source, ".lake/build", name);
    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
    File.Copy(path, target);
}
const string key = "synthetic-performance-fixture-not-a-certified-library";
File.WriteAllText(Path.Combine(source, "CIL.lean"), "performance fixture source binding");
File.WriteAllText(Path.Combine(source, "library-key.txt"), key);
var manifest = CacheFiles(source);
var sources = LibrarySources(manifest);
File.WriteAllText(Path.Combine(source, "cache-manifest.json"), System.Text.Json.JsonSerializer.Serialize(manifest));
var digest = Sha(Path.Combine(source, "cache-manifest.json"));
var bytes = Directory.EnumerateFiles(source, "*", SearchOption.AllDirectories).Sum(path => new FileInfo(path).Length);
var results = new List<object>();
foreach (var iteration in Enumerable.Range(0, 4))
foreach (var fused in iteration % 2 == 0 ? new[] { false, true } : new[] { true, false })
{
    var destination = Path.Combine(root, $"{iteration}-{fused}");
    var timer = System.Diagnostics.Stopwatch.StartNew();
    if (fused)
    {
        if (!CopyCertifiedLibrary(source, destination, digest, key, sources)) throw new Exception("copy failed");
    }
    else
    {
        if (!ValidCertifiedLibrary(source, digest, key, sources)) throw new Exception("source failed");
        CopyTree(source, destination);
    }
    if (!ValidCertifiedLibrary(destination, digest, key, sources)) throw new Exception("destination failed");
    timer.Stop();
    var row = new { iteration, fused, files = manifest.Count + 1, bytes, seconds = timer.Elapsed.TotalSeconds };
    results.Add(row);
    Console.WriteLine(System.Text.Json.JsonSerializer.Serialize(row));
    Directory.Delete(destination, recursive: true);
}
File.WriteAllText(Path.Combine(root, "timings.json"), System.Text.Json.JsonSerializer.Serialize(results, Json));
Console.WriteLine(root);
