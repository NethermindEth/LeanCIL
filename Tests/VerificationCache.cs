#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

var originalCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
var originalDisabled = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
var directory = Path.Combine(Path.GetTempPath(), "leancil-certified-cache-test-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(directory);
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", Path.Combine(directory, "cache"));
Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
using var verifier = new Program();
try
{
    var source = Path.Combine(directory, "source");
    var destination = Path.Combine(directory, "destination");
    Directory.CreateDirectory(source);
    Directory.CreateDirectory(destination);
    File.WriteAllText(Path.Combine(source, "Proof.olean"), "certified object fixture");
    File.WriteAllText(Path.Combine(source, "Proof.olean.private"), "private declarations");
    verifier.PublishSuccess("original", source);
    if (!verifier.RestoreSuccess("original", destination)) throw new Exception("Valid success receipt rejected");
    File.AppendAllText(Path.Combine(destination, "Proof.olean"), "private copy change");
    if (!verifier.RestoreSuccess("original", destination)) throw new Exception("Private copy mutated cache");
    var cached = Path.Combine(SuccessCacheRoot, "original");
    CopyTree(cached, Path.Combine(SuccessCacheRoot, "different-key"));
    if (verifier.RestoreSuccess("different-key", destination)) throw new Exception("Receipt accepted under different input key");
    var artifact = Path.Combine(cached, "files", "Proof.olean.private");
    File.AppendAllText(artifact, "corruption");
    if (verifier.RestoreSuccess("original", destination)) throw new Exception("Corrupt private declarations accepted");
    File.WriteAllBytes(Path.Combine(cached, "receipt.json"), JsonSerializer.SerializeToUtf8Bytes(CacheFiles(Path.Combine(cached, "files"))));
    if (verifier.RestoreSuccess("original", destination)) throw new Exception("Self-rehashed cache accepted without certification");
    verifier.PublishSuccess("extra", source);
    File.WriteAllText(Path.Combine(SuccessCacheRoot, "extra", "files", "unexpected.olean"), "unchecked");
    if (verifier.RestoreSuccess("extra", destination)) throw new Exception("Unrecorded object accepted");
    verifier.PublishSuccess("missing", source);
    File.Delete(Path.Combine(SuccessCacheRoot, "missing", "files", "Proof.olean"));
    if (verifier.RestoreSuccess("missing", destination)) throw new Exception("Missing object accepted");
    // Publishing closure A must not carry unrelated B from the same session.
    var session = Path.Combine(directory, "session");
    var artifacts = Path.Combine(session, ".lake/build/lib/lean/Support");
    Directory.CreateDirectory(artifacts);
    File.WriteAllText(Path.Combine(artifacts, "A.olean"), "checked A");
    File.WriteAllText(Path.Combine(artifacts, "B.olean"), "old B");
    var ir = Path.Combine(session, ".lake/build/ir/Support");
    Directory.CreateDirectory(ir);
    File.WriteAllText(Path.Combine(ir, "A.c"), "A compiled IR");
    File.WriteAllText(Path.Combine(ir, "B.c"), "unrelated B IR");
    var closure = Path.Combine(directory, "closure");
    Directory.CreateDirectory(closure);
    CopySupportArtifacts(session, closure, new SortedDictionary<string, string> { ["Support/A.lean"] = "A source" });
    if (!File.Exists(Path.Combine(closure, ".lake/build/ir/Support/A.c")) ||
        File.Exists(Path.Combine(closure, ".lake/build/ir/Support/B.c")))
        throw new Exception("Support cache did not retain exactly its IR output closure");
    verifier.PublishSuccess("closure-A", closure);
    File.WriteAllText(Path.Combine(artifacts, "B.olean"), "new B from changed source");
    if (!verifier.RestoreSuccess("closure-A", session) || File.ReadAllText(Path.Combine(artifacts, "B.olean")) != "new B from changed source")
        throw new Exception("Restoring A overwrote unrelated B certification");
    var supplied = Path.Combine(directory, "supplied");
    var suppliedObject = Path.Combine(supplied, ".lake/build/lib/lean/CIL.olean");
    Directory.CreateDirectory(Path.GetDirectoryName(suppliedObject)!);
    File.WriteAllText(suppliedObject, "producer-checked fixture");
    File.WriteAllText(Path.Combine(supplied, "CIL.lean"), "source");
    File.WriteAllText(Path.Combine(supplied, "library-key.txt"), "toolchain-and-sources");
    File.WriteAllText(Path.Combine(supplied, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(supplied)));
    var trustedDigest = Sha(Path.Combine(supplied, "cache-manifest.json"));
    var suppliedSources = LibrarySources(CacheFiles(supplied));
    if (!ValidCertifiedLibrary(supplied, trustedDigest, "toolchain-and-sources", suppliedSources) ||
        ValidCertifiedLibrary(supplied, "wrong digest", "toolchain-and-sources", suppliedSources) ||
        ValidCertifiedLibrary(supplied, trustedDigest, "different toolchain", suppliedSources) ||
        ValidCertifiedLibrary(supplied, trustedDigest, "toolchain-and-sources", new SortedDictionary<string, string> { ["CIL.lean"] = "different source" }))
        throw new Exception("Producer digest/source/toolchain identity checks failed");
    File.AppendAllText(suppliedObject, "changed after initial validation");
    File.WriteAllText(Path.Combine(supplied, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(supplied)));
    var suppliedCopy = Path.Combine(directory, "supplied-copy");
    CopyTree(supplied, suppliedCopy);
    if (ValidCertifiedLibrary(supplied, trustedDigest, "toolchain-and-sources", suppliedSources) ||
        ValidCertifiedLibrary(suppliedCopy, trustedDigest, "toolchain-and-sources", suppliedSources))
        throw new Exception("Rehashed artifact or changed private copy accepted against original producer digest");
    using var fresh = new Program { freshLibrary = true };
    fresh.PublishSuccess("fresh", source);
    if (Directory.Exists(Path.Combine(SuccessCacheRoot, "fresh")) || fresh.RestoreSuccess("original", destination))
        throw new Exception("Fresh verification used success cache");
    Console.WriteLine("PASS certified cache input binding, authenticated provenance, corruption/missing/extra rejection, private copies and fresh bypass");
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", originalCache);
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", originalDisabled);
    Directory.Delete(directory, true);
}
