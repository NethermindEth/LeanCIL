#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// Child mode: one independent process publishing a receipt into a shared cache.
if (args is ["publish", var publishCache, var publishKey, var publishSource])
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", publishCache);
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
    using var publisher = new Program();
    publisher.PublishSuccess(publishKey, publishSource);
    return;
}

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
    var checkedCopy = Path.Combine(directory, "checked-copy");
    if (!OperatingSystem.IsWindows())
    {
        var executableMode = UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute;
        File.SetUnixFileMode(suppliedObject, executableMode);
        File.SetUnixFileMode(Path.Combine(supplied, "cache-manifest.json"), executableMode);
    }
    bool CopySupplied(string? digest = null, string key = "toolchain-and-sources",
        SortedDictionary<string, string>? sourceBinding = null) =>
        CopyCertifiedLibrary(supplied, checkedCopy, digest ?? trustedDigest, key, sourceBinding ?? suppliedSources);
    if (!CopySupplied() ||
        !ValidCertifiedLibrary(checkedCopy, trustedDigest, "toolchain-and-sources", suppliedSources) ||
        CopySupplied("wrong digest") || CopySupplied(key: "different toolchain") ||
        CopySupplied(sourceBinding: new() { ["CIL.lean"] = "different source" }))
        throw new Exception("Certified copy did not preserve pinned digest/source/toolchain binding");
    if (!OperatingSystem.IsWindows())
        foreach (var name in new[] { ".lake/build/lib/lean/CIL.olean", "cache-manifest.json" })
            if (File.GetUnixFileMode(Path.Combine(supplied, name)) !=
                File.GetUnixFileMode(Path.Combine(checkedCopy, name)))
                throw new Exception("Certified copy changed Unix file modes: " + name);
    File.AppendAllText(Path.Combine(checkedCopy, ".lake/build/lib/lean/CIL.olean"), "destination mutation");
    if (ValidCertifiedLibrary(checkedCopy, trustedDigest, "toolchain-and-sources", suppliedSources))
        throw new Exception("Independent destination validation accepted changed compiled bytes");
    foreach (var name in new[] { ".lake/build/lib/lean/CIL.olean", "CIL.lean" })
    {
        var path = Path.Combine(supplied, name);
        var original = File.ReadAllBytes(path);
        File.AppendAllText(path, "changed contents");
        if (CopySupplied()) throw new Exception("Certified copy accepted changed contents: " + name);
        File.Delete(path);
        if (CopySupplied()) throw new Exception("Certified copy accepted a missing file: " + name);
        File.WriteAllBytes(path, original);
    }
    var extraPart = suppliedObject + ".private";
    File.WriteAllText(extraPart, "unbound compiled part");
    if (CopySupplied()) throw new Exception("Certified copy accepted an extra compiled part");
    File.Delete(extraPart);
    if (!CopySupplied() || !ValidCertifiedLibrary(checkedCopy, trustedDigest, "toolchain-and-sources", suppliedSources))
        throw new Exception("Restored source bytes failed certified copying");
    Console.WriteLine("PASS fused certified copy preserves manifest, source, file-set and destination integrity");
    File.AppendAllText(suppliedObject, "changed after initial validation");
    File.WriteAllText(Path.Combine(supplied, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(supplied)));
    var suppliedCopy = Path.Combine(directory, "supplied-copy");
    CopyTree(supplied, suppliedCopy);
    if (ValidCertifiedLibrary(supplied, trustedDigest, "toolchain-and-sources", suppliedSources) ||
        ValidCertifiedLibrary(suppliedCopy, trustedDigest, "toolchain-and-sources", suppliedSources) || CopySupplied())
        throw new Exception("Rehashed artifact or changed private copy accepted against original producer digest");
    // Republishing identical content is a no-op; it must not create a second copy.
    var receipt = Path.Combine(SuccessCacheRoot, "original-identical", "receipt.hmac");
    verifier.PublishSuccess("original-identical", source);
    var firstWrite = File.GetLastWriteTimeUtc(receipt);
    verifier.PublishSuccess("original-identical", source);
    if (File.GetLastWriteTimeUtc(receipt) != firstWrite ||
        Directory.EnumerateDirectories(SuccessCacheRoot, "original-identical*").Count() != 1)
        throw new Exception("Identical publication was duplicated or rewritten");
    // A corrupt entry is replaced by the next certified publication.
    File.AppendAllText(Path.Combine(SuccessCacheRoot, "original-identical", "files", "Proof.olean"), "corruption");
    verifier.PublishSuccess("original-identical", source);
    if (!verifier.RestoreSuccess("original-identical", Path.Combine(directory, "replaced")) ||
        Directory.EnumerateDirectories(SuccessCacheRoot, "original-identical*").Count() != 1)
        throw new Exception("Corrupt entry was not replaced by a certified publication");
    // Concurrent processes race only on an atomic rename: one entry, no staging leftovers.
    string[] self = Path.GetFileNameWithoutExtension(Environment.ProcessPath) == "dotnet"
        ? [Environment.ProcessPath!, typeof(Program).Assembly.Location] : [Environment.ProcessPath!];
    var cacheDirectory = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR")!;
    var publishers = Enumerable.Range(0, 8).Select(_ => Task.Run(() =>
        Execute([.. self, "publish", cacheDirectory, "concurrent", source]))).ToArray();
    Task.WaitAll(publishers);
    if (publishers.Any(task => task.Result.Code != 0))
        throw new Exception("Concurrent publisher failed: " + string.Join("\n", publishers.Select(task => task.Result.Output)));
    if (Directory.EnumerateDirectories(SuccessCacheRoot, "concurrent*").Count() != 1 ||
        !verifier.RestoreSuccess("concurrent", Path.Combine(directory, "concurrent")))
        throw new Exception("Concurrent publication left duplicates, staging directories or an invalid entry");
    Console.WriteLine("PASS idempotent publication, corrupt entry replacement and concurrent publishers");
    // Generations of one family share unchanged bytes instead of holding a full copy each.
    var family = new string('a', 64);
    string Generation(char c) => family + "-" + new string(c, 64);
    var first = Path.Combine(directory, "generation-1");
    Directory.CreateDirectory(first);
    File.WriteAllText(Path.Combine(first, "Shared.olean"), "unchanged support module");
    File.WriteAllText(Path.Combine(first, "Proof.olean"), "first proof");
    verifier.PublishSuccess(Generation('b'), first, family);
    var second = Path.Combine(directory, "generation-2");
    CopyTree(first, second);
    File.WriteAllText(Path.Combine(second, "Proof.olean"), "second proof");
    // A sibling whose receipt misstates its bytes must not be linked into a new entry.
    var forged = Path.Combine(SuccessCacheRoot, Generation('0'));
    Directory.CreateDirectory(Path.Combine(forged, "files"));
    File.WriteAllText(Path.Combine(forged, "files", "Proof.olean"), "forged bytes");
    File.WriteAllText(Path.Combine(forged, "receipt.json"), JsonSerializer.Serialize(
        new SortedDictionary<string, string> { ["Proof.olean"] = Sha(Path.Combine(second, "Proof.olean")) }));
    verifier.PublishSuccess(Generation('c'), second, family);
    var linked = Path.Combine(directory, "linked");
    if (!verifier.RestoreSuccess(Generation('c'), linked) || File.ReadAllText(Path.Combine(linked, "Proof.olean")) != "second proof")
        throw new Exception("Generation linked to bytes its sibling's receipt misstated");
    File.AppendAllText(Path.Combine(SuccessCacheRoot, Generation('b'), "files", "Shared.olean"), " changed in place");
    if (File.ReadAllText(Path.Combine(SuccessCacheRoot, Generation('c'), "files", "Shared.olean")) != "unchanged support module changed in place" ||
        File.ReadAllText(Path.Combine(SuccessCacheRoot, Generation('c'), "files", "Proof.olean")) != "second proof")
        throw new Exception("Unchanged file was copied into a new generation, or a changed file was shared");
    // Shared bytes stay authenticated per entry: in-place damage rejects every sharer.
    if (verifier.RestoreSuccess(Generation('c'), Path.Combine(directory, "damaged")))
        throw new Exception("Damaged shared file accepted");
    Console.WriteLine("PASS support generations share unchanged files and stay individually authenticated");

    // Eviction removes only exact cache entry names past their age, never receipts or other names.
    var evictionRoot = Path.Combine(directory, "eviction");
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", evictionRoot);
    Directory.CreateDirectory(SuccessCacheRoot);
    string Entry(string name, int days)
    {
        var path = Path.Combine(SuccessCacheRoot, name);
        Directory.CreateDirectory(Path.Combine(path, "files"));
        File.WriteAllText(Path.Combine(path, "files", "artifact.olean"), name);
        Directory.SetLastWriteTimeUtc(path, DateTime.UtcNow.AddDays(-days));
        return path;
    }
    var staleGeneration = Entry(Generation('1'), 8);
    var usedGeneration = Entry(Generation('2'), 6);
    var restored = Entry(Generation('3'), 30);
    TouchSuccess(restored);
    var staleReceipt = Entry(new string('4', 64), 30);
    var abandoned = Entry(new string('5', 64) + "." + new string('6', 32), 2);
    var replaced = Entry(Generation('7') + ".invalid-" + new string('8', 32), 2);
    var publishing = Entry(Generation('9') + "." + new string('a', 32), 0);
    var unrelated = Entry("notes-" + Generation('b'), 30);
    var outside = Path.Combine(directory, "outside");
    Directory.CreateDirectory(outside);
    File.WriteAllText(Path.Combine(outside, "keep.txt"), "outside the cache");
    var link = Path.Combine(SuccessCacheRoot, Generation('c'));
    var linkCreated = true;
    try
    {
        Directory.CreateSymbolicLink(link, outside);
        Directory.SetLastWriteTimeUtc(link, DateTime.UtcNow.AddDays(-30));
    }
    catch (Exception error) when (error is IOException or UnauthorizedAccessException) { linkCreated = false; }
    supportEvicted = 0;
    EvictStaleSupport();
    if (Directory.Exists(staleGeneration) || Directory.Exists(abandoned) || Directory.Exists(replaced) ||
        !Directory.Exists(usedGeneration) || !Directory.Exists(restored) || !Directory.Exists(staleReceipt) ||
        !Directory.Exists(publishing) || !Directory.Exists(unrelated) || !File.Exists(Path.Combine(outside, "keep.txt")) ||
        linkCreated && !Directory.Exists(link) ||
        Directory.EnumerateDirectories(SuccessCacheRoot).Any(path => path.Contains(".evicted-")))
        throw new Exception("Eviction removed a used, unrelated or linked entry, or kept a stale one");
    Console.WriteLine(linkCreated
        ? "PASS eviction of unused support generations and abandoned staging; receipts, unrelated names and links kept"
        : "PASS eviction of unused support generations and abandoned staging; receipts and unrelated names kept (symbolic link check not run: no privilege)");

    // A cache that cannot be written leaves verification to succeed and says why.
    var blocked = Path.Combine(directory, "blocked");
    Directory.CreateDirectory(blocked);
    File.WriteAllText(Path.Combine(blocked, "success-v1"), "a file where the cache directory belongs");
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", blocked);
    var savedError = Console.Error;
    var warnings = new StringWriter();
    Console.SetError(warnings);
    try { verifier.PublishSuccess("blocked", source); }
    finally { Console.SetError(savedError); }
    if (!warnings.ToString().Contains("warning: success cache " + SuccessCacheRoot + " not updated"))
        throw new Exception("Unwritable cache did not report a warning naming the cache: " + warnings);
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", Path.Combine(directory, "cache"));
    Console.WriteLine("PASS unwritable cache warns with its location instead of failing a verified result");

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
