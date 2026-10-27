#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.IO.Compression;
using System.Text.Json;

if (args is [var releasedArchive, var releasedDescriptor, var releasedCache])
{
    using var receiver = new Program();
    var releasedAsset = JsonSerializer.Deserialize<CertifiedReleaseAsset>(File.ReadAllBytes(releasedDescriptor))!;
    var (releasedKey, releasedSources) = receiver.LibraryIdentity(CommonInputs());
    var cached = Path.Combine(Path.GetFullPath(releasedCache), releasedKey);
    if (Directory.Exists(cached)) throw new IOException("Roundtrip destination already exists");
    receiver.InstallReleasedLibrary(releasedArchive, cached + ".staging", cached, releasedAsset);
    if (!receiver.CertifiedLocalLibrary(cached, releasedKey) ||
        !ValidCertifiedLibrary(cached, releasedAsset.ManifestSha256, releasedKey, releasedSources))
        throw new Exception("Release roundtrip lost source/artifact binding or local authentication");
    Console.WriteLine("PASS real release archive validates, independently replays and installs authenticated cache");
    return;
}
if (args.Length != 0) throw new ArgumentException("Expected no arguments or archive, descriptor and cache directory");

var root = At("artifacts/LibraryRelease-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
using var verifier = new Program();
var (key, _) = verifier.LibraryIdentity(CommonInputs());
var runtime = System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier;
var archive = Path.Combine(root, "library.zip");
File.WriteAllText(archive, "not an archive");
var asset = new CertifiedReleaseAsset(1, "v0.1.0", runtime, key, ReleaseAssetName(runtime, key),
    new FileInfo(archive).Length, Sha(archive), new string('a', 64));
if (!ValidReleaseAsset(asset, key)) throw new Exception("Valid package descriptor rejected");
CertifiedReleaseAsset[] invalid =
[
    asset with { Schema = 2 }, asset with { Runtime = "another-runtime" },
    asset with { LibraryKey = new string('0', 64) }, asset with { Tag = "../../main" },
    asset with { Tag = "" }, asset with { Archive = "../library.zip" },
    asset with { ArchiveBytes = -1 }, asset with { ArchiveSha256 = "" },
    asset with { ManifestSha256 = new string('g', 64) },
    JsonSerializer.Deserialize<CertifiedReleaseAsset>("{\"Schema\":1}")!
];
if (invalid.Any(candidate => ValidReleaseAsset(candidate, key)))
    throw new Exception("Invalid package descriptor accepted");
Console.WriteLine("PASS release descriptors bind schema, runtime, source/toolchain key, tag, name and digests");

void Reject(string label, CertifiedReleaseAsset candidate)
{
    var staging = Path.Combine(root, label + "-staging");
    var cached = Path.Combine(root, label + "-cache");
    try { verifier.InstallReleasedLibrary(archive, staging, cached, candidate); }
    catch (Exception error) when (error is IOException or InvalidDataException or InvalidOperationException)
    {
        if (Directory.Exists(cached)) throw new Exception("Rejected release published a cache entry");
        Console.WriteLine("PASS release rejects " + label);
        return;
    }
    throw new Exception("Invalid release accepted: " + label);
}
Reject("changed-archive-digest", asset with { ArchiveSha256 = new string('0', 64) });
Reject("changed-archive-size", asset with { ArchiveBytes = asset.ArchiveBytes + 1 });
File.Delete(archive);
using (var zip = ZipFile.Open(archive, ZipArchiveMode.Create))
using (var writer = new StreamWriter(zip.CreateEntry("../escaped.txt").Open())) writer.Write("escape");
asset = asset with { ArchiveBytes = new FileInfo(archive).Length, ArchiveSha256 = Sha(archive) };
Reject("path-traversal", asset);
if (File.Exists(Path.Combine(root, "escaped.txt"))) throw new Exception("Archive escaped extraction directory");
File.Delete(archive);
using (var zip = ZipFile.Open(archive, ZipArchiveMode.Create))
using (var writer = new StreamWriter(zip.CreateEntry("cache-manifest.json").Open())) writer.Write("{}");
asset = asset with { ArchiveBytes = new FileInfo(archive).Length, ArchiveSha256 = Sha(archive) };
Reject("self-described-manifest", asset);
