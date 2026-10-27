#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// Fast cache-integrity regressions; end-to-end cold/warm verification exercises the builder.
Run(["dotnet", "run", "--file", At("Tests/LibrarySourceExtension.cs")]);
Run(["dotnet", "run", "--file", At("Tests/LibraryIncremental.cs")]);
Run(["dotnet", "run", "--file", At("Tests/LibraryRelease.cs")]);
Run(["dotnet", "run", "--file", At("Tests/LibraryReplayCoverage.cs")]);
var directory = Path.Combine(Path.GetTempPath(), "leancil-cache-test-" + Guid.NewGuid().ToString("N"));
var prepared = directory + "-prepared";
var unrelated = directory + "-unrelated";
using var verifier = new Program { freshLibrary = true };
try
{
    // Cache entries are read in place, so only a receipt over the exact key and manifest admits one.
    var artifact = Path.Combine(directory, ".lake/build/lib/lean/CIL.olean");
    Directory.CreateDirectory(Path.GetDirectoryName(artifact)!);
    File.WriteAllText(artifact, "compiled artifact");
    var cacheManifest = Path.Combine(directory, "cache-manifest.json");
    File.WriteAllText(cacheManifest, System.Text.Json.JsonSerializer.Serialize(CacheFiles(directory)));
    void Receipt() => File.WriteAllBytes(Path.Combine(directory, "cache-receipt.hmac"), System.Security.Cryptography.HMACSHA256.HashData(
        verifier.ReceiptKey, System.Text.Encoding.UTF8.GetBytes("cache-key").Concat(File.ReadAllBytes(cacheManifest)).ToArray()));
    if (verifier.CertifiedLocalLibrary(directory, "cache-key")) throw new Exception("Unreceipted cache entry accepted");
    Receipt();
    if (!verifier.CertifiedLocalLibrary(directory, "cache-key")) throw new Exception("Receipted cache entry rejected");
    if (verifier.CertifiedLocalLibrary(directory, "other-key")) throw new Exception("Cache receipt accepted for another library key");
    File.WriteAllText(cacheManifest, System.Text.Json.JsonSerializer.Serialize(new SortedDictionary<string, string>(StringComparer.Ordinal)));
    if (verifier.CertifiedLocalLibrary(directory, "cache-key")) throw new Exception("Replaced cache manifest accepted");

    var snapshot = new SortedDictionary<string, string>(StringComparer.Ordinal)
    {
        ["CIL.lean"] = "root", ["CIL/Types.lean"] = "types", ["lean-toolchain"] = "toolchain",
        ["Examples/Proofs/Add.lean"] = "proof", ["Tests/Semantics.lean"] = "test", ["proof:custom.lean"] = "custom"
    };
    var sources = LibrarySources(snapshot);
    snapshot["Examples/Proofs/Add.lean"] = "edited proof";
    snapshot["proof:custom.lean"] = "edited custom";
    if (!Same(sources, LibrarySources(snapshot))) throw new Exception("Proof edits invalidate base library");
    snapshot["CIL/Types.lean"] = "edited types";
    if (Same(sources, LibrarySources(snapshot))) throw new Exception("Source edit does not invalidate base library");
    Console.WriteLine("PASS cache receipts bind key and manifest; source/proof key separation");

    Directory.CreateDirectory(unrelated);
    var sentinel = Path.Combine(unrelated, "keep.txt");
    File.WriteAllText(sentinel, "unrelated contents");
    ExpectRejection(() => verifier.PrepareLibrary(unrelated), "destination must be empty");
    ExpectRejection(() => verifier.PrepareLibrary(unrelated, new string('0', 64)), "destination left unchanged");
    if (File.ReadAllText(sentinel) != "unrelated contents") throw new Exception("Unrelated destination modified");

    // A self-consistent compiled tree is not evidence of a trusted producer.
    var compiled = Path.Combine(prepared, ".lake/build/lib/lean/CIL.olean");
    var auditor = Path.Combine(prepared, ".lake/build/bin", OperatingSystem.IsWindows() ? "leancil-audit.exe" : "leancil-audit");
    Directory.CreateDirectory(Path.GetDirectoryName(compiled)!);
    Directory.CreateDirectory(Path.GetDirectoryName(auditor)!);
    File.WriteAllText(compiled, "compiled fixture");
    File.WriteAllText(auditor, "native auditor fixture");
    File.WriteAllText(Path.Combine(prepared, "CIL.lean"), "source fixture");
    File.WriteAllText(Path.Combine(prepared, "library-key.txt"), "fixture-key");
    var manifest = Path.Combine(prepared, "cache-manifest.json");
    File.WriteAllText(manifest, System.Text.Json.JsonSerializer.Serialize(CacheFiles(prepared)));
    var trustedDigest = Sha(manifest);
    var preparedSources = LibrarySources(CacheFiles(prepared));
    if (!ValidCertifiedLibrary(prepared, trustedDigest, "fixture-key", preparedSources))
        throw new Exception("Pinned fixture rejected");
    if (verifier.ReusePreparedLibrary(prepared, null) is not null || verifier.ReusePreparedLibrary(prepared, "") is not null)
        throw new Exception("Reuse accepted without independent producer digest");
    foreach (var file in new[] { auditor, compiled })
    {
        var original = File.ReadAllText(file);
        File.WriteAllText(file, "substituted contents");
        File.WriteAllText(manifest, System.Text.Json.JsonSerializer.Serialize(CacheFiles(prepared)));
        if (!Same(ReadManifest(prepared)!, CacheFiles(prepared))) throw new Exception("Tamper fixture must remain internally consistent");
        if (ValidCertifiedLibrary(prepared, trustedDigest, "fixture-key", preparedSources))
            throw new Exception("Self-rehashed substitution accepted against producer digest");
        ExpectRejection(() => verifier.PrepareLibrary(prepared, trustedDigest), "destination left unchanged");
        if (File.ReadAllText(file) != "substituted contents") throw new Exception("Rejected reuse modified the destination");
        File.WriteAllText(file, original);
    }
    var legacy = Execute(["dotnet", "run", "--file", At("scripts/PrepareLibrary.cs"), "--", unrelated, "--reuse"]);
    if (legacy.Code == 0 || !legacy.Output.Contains("trusted-manifest-sha256") || File.ReadAllText(sentinel) != "unrelated contents")
        throw new Exception("Legacy unauthenticated --reuse did not fail safely: " + legacy.Output);
    Console.WriteLine("PASS unauthenticated reuse, substituted auditor/olean with regenerated manifests, and non-destructive destination rejection");
}
finally
{
    Directory.Delete(directory, true);
    if (Directory.Exists(prepared)) Directory.Delete(prepared, true);
    if (Directory.Exists(unrelated)) Directory.Delete(unrelated, true);
}

static void ExpectRejection(Action action, string message)
{
    try { action(); }
    catch (InvalidOperationException error) when (error.Message.Contains(message)) { return; }
    throw new Exception("Expected rejection: " + message);
}
