#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs

using System.IO.Compression;
using System.Text.Json;

if (args is not [_, _, _, _])
    throw new ArgumentException("Usage: PackageCertifiedLibrary.cs <certified-directory> " +
        "<trusted-manifest-sha256> <release-tag> <output-directory>");
var directory = Path.GetFullPath(args[0]);
var digest = args[1];
var tag = args[2];
var output = Path.GetFullPath(args[3]);
using var verifier = new Program();
var (key, sources) = verifier.LibraryIdentity(CommonInputs());
var runtime = System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier;
var archiveName = ReleaseAssetName(runtime, key);
var asset = new CertifiedReleaseAsset(1, tag, runtime, key, archiveName, 1, new string('0', 64), digest);
if (!ValidReleaseAsset(asset, key)) throw new ArgumentException("Invalid release tag or producer digest");
if (verifier.ReusePreparedLibrary(directory, digest) is null)
    throw new InvalidDataException("Release input does not match the authenticated producer or current sources");
Directory.CreateDirectory(output);
var archive = Path.Combine(output, archiveName);
var descriptor = Path.Combine(output, $"certified-library-release.{runtime}.json");
if (File.Exists(archive) || File.Exists(descriptor))
    throw new IOException("Release output already exists");
var staged = Path.Combine(Path.GetTempPath(), "leancil-release-check-" + Guid.NewGuid().ToString("N"));
try
{
    ZipFile.CreateFromDirectory(directory, archive, CompressionLevel.Optimal, false);
    // Validate the bytes actually archived, not a second reading of a possibly changing source tree.
    ZipFile.ExtractToDirectory(archive, staged);
    if (!ValidCertifiedLibrary(staged, digest, key, sources))
        throw new InvalidDataException("Certified library changed while archiving");
    asset = asset with { ArchiveBytes = new FileInfo(archive).Length, ArchiveSha256 = Sha(archive) };
    if (!ValidReleaseAsset(asset, key)) throw new InvalidDataException("Release archive exceeds size limit");
    File.WriteAllText(descriptor, JsonSerializer.Serialize(asset, Json));
    Console.WriteLine("Release asset: " + archive);
    Console.WriteLine("Package-pinned descriptor: " + descriptor);
}
finally
{
    if (Directory.Exists(staged)) Directory.Delete(staged, true);
}
