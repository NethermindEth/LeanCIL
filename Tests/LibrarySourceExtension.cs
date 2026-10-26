#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// Synthetic artifacts test authentication and isolation; the CLI helper fixture
// separately verifies real compiled proofs against an extended certified library.
var root = At("artifacts/LibrarySourceExtension-" + Guid.NewGuid().ToString("N"));
var certifiedBase = Path.Combine(root, "base");
Directory.CreateDirectory(certifiedBase);
using var verifier = new Program();
const string addition = "CIL/Safety/ReturnArity.lean";
foreach (var source in LibrarySources(CommonInputs()).Keys.Where(name => name != addition))
{
    var target = Path.Combine(certifiedBase, source);
    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
    File.Copy(At(source), target);
}
var compiled = Path.Combine(certifiedBase, ".lake/build/lib/lean/CIL.olean");
Directory.CreateDirectory(Path.GetDirectoryName(compiled)!);
File.WriteAllText(compiled, "authenticated compiled bytes");
var fingerprintMetadata = Path.Combine(certifiedBase, CertifiedFingerprintsName);
File.WriteAllText(fingerprintMetadata, "authenticated prepared metadata");
string Publish()
{
    var (key, _) = verifier.LibraryIdentity(LibrarySources(CacheFiles(certifiedBase)));
    File.WriteAllText(Path.Combine(certifiedBase, "library-key.txt"), key);
    File.WriteAllText(Path.Combine(certifiedBase, "cache-manifest.json"),
        JsonSerializer.Serialize(CacheFiles(certifiedBase)));
    return Sha(Path.Combine(certifiedBase, "cache-manifest.json"));
}
var digest = Publish();
var destination = Path.Combine(root, "extended");
var extendedDigest = verifier.ExtendPreparedLibrary(destination, certifiedBase, digest);
var (expectedKey, expectedSources) = verifier.LibraryIdentity(CommonInputs());
if (!ValidCertifiedLibrary(destination, extendedDigest, expectedKey, expectedSources) ||
    Sha(Path.Combine(destination, addition)) != Sha(At(addition)) ||
    Sha(Path.Combine(destination, CertifiedFingerprintsName)) != Sha(fingerprintMetadata) ||
    File.Exists(Path.Combine(destination, ".lake/build/lib/lean/CIL/Safety/ReturnArity.olean")))
    throw new Exception("Source extension did not preserve the certified closure and bind its new source.");
File.AppendAllText(Path.Combine(destination, ".lake/build/lib/lean/CIL.olean"), "private mutation");
if (File.ReadAllText(compiled) != "authenticated compiled bytes")
    throw new Exception("Extended library shares mutable compiled bytes with its base.");

void Reject(string label, string trusted, string expected)
{
    var rejected = Path.Combine(root, label);
    try { verifier.ExtendPreparedLibrary(rejected, certifiedBase, trusted); }
    catch (Exception error) when (error.Message.Contains(expected, StringComparison.Ordinal))
    {
        if (Directory.Exists(rejected)) throw new Exception("Rejected extension published a destination: " + label);
        Console.WriteLine("PASS source extension rejects " + label);
        return;
    }
    throw new Exception("Source extension accepted " + label);
}
Reject("wrong-digest", new string('0', 64), "manifest digest mismatch");
File.AppendAllText(compiled, "corrupt");
Reject("changed-artifact", digest, "identity or integrity mismatch");
_ = Publish();
Reject("self-rehashed-artifact", digest, "manifest digest mismatch");
File.WriteAllText(compiled, "authenticated compiled bytes");
digest = Publish();
File.AppendAllText(fingerprintMetadata, "corrupt");
Reject("changed-prepared-metadata", digest, "identity or integrity mismatch");
File.WriteAllText(fingerprintMetadata, "authenticated prepared metadata");
var shadow = Path.Combine(certifiedBase, ".lake/build/lib/lean/CIL/Safety/ReturnArity.olean");
Directory.CreateDirectory(Path.GetDirectoryName(shadow)!);
File.WriteAllText(shadow, "previously compiled without source");
Reject("compiled-shadow", Publish(), "shadows a compiled module");
File.Delete(shadow);
var differentlyCased = Path.Combine(certifiedBase, ".lake/build/lib/lean/CIL/Safety/returnarity.olean");
File.WriteAllText(differentlyCased, "case variant of a compiled module");
if (File.Exists(shadow)) Reject("case-insensitive-compiled-shadow", Publish(), "shadows a compiled module");
File.Delete(differentlyCased);
var originalSource = File.ReadAllText(Path.Combine(certifiedBase, "CIL.lean"));
File.AppendAllText(Path.Combine(certifiedBase, "CIL.lean"), "\n-- changed existing source\n");
Reject("changed-existing-source", Publish(), "changed or removed an existing certified source");
File.WriteAllText(Path.Combine(certifiedBase, "CIL.lean"), originalSource);
var removed = Path.Combine(certifiedBase, "CIL/Removed.lean");
File.WriteAllText(removed, "theorem removed : True := True.intro\n");
Reject("removed-source", Publish(), "changed or removed an existing certified source");
File.Delete(removed);
var originalConfiguration = File.ReadAllText(Path.Combine(certifiedBase, "lakefile.toml"));
File.AppendAllText(Path.Combine(certifiedBase, "lakefile.toml"), "\n# changed configuration\n");
Reject("changed-configuration", Publish(), "changed or removed an existing certified source");
File.WriteAllText(Path.Combine(certifiedBase, "lakefile.toml"), originalConfiguration);
digest = Publish();
try { verifier.ExtendPreparedLibrary(destination, certifiedBase, digest); }
catch (InvalidOperationException error) when (error.Message.Contains("destination must be empty"))
{
    Console.WriteLine("PASS source extension preserves an existing destination");
    return;
}
throw new Exception("Source extension replaced an existing destination.");
