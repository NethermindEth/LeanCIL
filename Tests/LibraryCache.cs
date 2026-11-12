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
// Short, since a closure entry is built below it and Lean on Windows limits path lengths.
var builtCache = Path.Combine(Path.GetTempPath(), "lc-" + Guid.NewGuid().ToString("N")[..8]);
var fixture = Path.Combine(Path.GetTempPath(), "lf-" + Guid.NewGuid().ToString("N")[..8]);
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
    // A package may require an entry by path, where Lake rebuilds a module it finds stale. The receipt covers
    // only the manifest, so every file is hashed against it on each use, whatever its length and write time.
    var entryManifest = ReadManifest(directory)!;
    bool Unchanged() => HashedCacheEntry(directory, entryManifest) is not null;
    if (!Unchanged()) throw new Exception("Unchanged cache entry rejected");
    var certifiedAt = File.GetLastWriteTimeUtc(artifact);
    File.WriteAllText(artifact, "rebuilt artifact!");
    File.SetLastWriteTimeUtc(artifact, certifiedAt);
    if (Unchanged()) throw new Exception("A rewritten module with its length and write time kept was accepted");
    File.WriteAllText(artifact, "compiled artifact");
    File.SetLastWriteTimeUtc(artifact, certifiedAt.AddSeconds(10));
    if (!Unchanged()) throw new Exception("An entry whose files hash to its manifest was rejected");
    var unrecorded = Path.Combine(Path.GetDirectoryName(artifact)!, "Unrecorded.olean");
    File.WriteAllText(unrecorded, "built into the entry");
    if (Unchanged()) throw new Exception("A cache entry holding a file its manifest lacks was accepted");
    File.Delete(unrecorded);
    if (!Unchanged()) throw new Exception("A restored cache entry was rejected");
    Console.WriteLine("PASS a cache entry is accepted only while its files hash to the receipted manifest");

    // Reject in-place reuse if another build changes the library after it was opened.
    using (var opened = new Program { library = directory, libraryStamps = FileStamps(directory) })
    {
        opened.RequireUnchangedLibrary();
        // A module Lake builds into the library is a new file beside unchanged ones.
        File.WriteAllText(unrecorded, "built into the entry");
        ExpectRejection(opened.RequireUnchangedLibrary, "changed on disk during verification");
        File.Delete(unrecorded);
        opened.RequireUnchangedLibrary();
        File.SetLastWriteTimeUtc(artifact, certifiedAt.AddSeconds(15));
        ExpectRejection(opened.RequireUnchangedLibrary, "changed on disk during verification");
    }
    RequireUnwritten(directory, () => File.ReadAllText(artifact));
    ExpectRejection(() => RequireUnwritten(directory, () => File.WriteAllText(unrecorded, "built into the entry")),
        "wrote into the certified library");
    File.Delete(unrecorded);
    ExpectRejection(() => RequireUnwritten(directory, () => File.AppendAllText(artifact, " rebuilt")),
        "wrote into the certified library");
    Console.WriteLine("PASS a library read in place fails verification or an editor build that changed its files");

    // A closure entry holds the modules one proof imports. Its key names them, and it is no whole library.
    var closure = directory + "-closure";
    void Entry(string name, string contents)
    {
        Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(closure, name))!);
        File.WriteAllText(Path.Combine(closure, name), contents);
    }
    string[] closureModules = ["CIL.A", "CIL.B", AuditModule];
    Entry("CIL/A.lean", "import Lean\nimport CIL.B\n");
    Entry("CIL/B.lean", "import Std\n");
    Entry("CIL/OleanAudit.lean", "import Lean\n");
    foreach (var name in new[] { "lakefile.toml", "lake-manifest.json", "lean-toolchain" }) Entry(name, name);
    foreach (var module in closureModules) Entry(".lake/build/lib/lean/" + module.Replace('.', '/') + ".olean", module);
    var closureManifest = CacheFiles(closure);
    var wholeSources = new SortedDictionary<string, string>(LibrarySources(closureManifest), StringComparer.Ordinal)
    {
        ["CIL/C.lean"] = "outside the closure", ["CIL.lean"] = "aggregate"
    };
    string ReadSource(string name) => File.Exists(Path.Combine(closure, name))
        ? File.ReadAllText(Path.Combine(closure, name)) : "import CIL.A\nimport CIL.C\n";
    if (ImportClosure(wholeSources, ["CIL.A", "Lean", "Extracted"], ReadSource) is not { } imported ||
        !imported.SequenceEqual(closureModules) ||
        ImportClosure(wholeSources, ["CIL.Unknown"], ReadSource) is not null ||
        ImportClosure(wholeSources, ["CIL"], ReadSource) is not null)
        throw new Exception("The import closure is not the framework modules the roots import");
    var wholeKey = "whole-library-key";
    var closureKey = ClosureKey(wholeKey, closureModules);
    if (closureKey == wholeKey || closureKey == ClosureKey(wholeKey, [.. closureModules, "CIL.C"]) ||
        closureKey == ClosureKey("other-library-key", closureModules))
        throw new Exception("A closure key does not name its library and exactly its modules");
    if (!ClosureManifest(closureManifest, wholeSources, closureModules) ||
        ClosureManifest(closureManifest, wholeSources, [.. closureModules, "CIL.C"]) ||
        ClosureManifest(closureManifest, wholeSources, ["CIL.A", AuditModule]))
        throw new Exception("A closure manifest was accepted for another module list");
    // A module compiled into the entry without being named by its key was never replayed under that key.
    Entry(".lake/build/lib/lean/CIL/C.olean", "CIL.C");
    if (ClosureManifest(CacheFiles(closure), wholeSources, closureModules))
        throw new Exception("A closure entry holding a compiled module outside its closure was accepted");
    File.Delete(Path.Combine(closure, ".lake/build/lib/lean/CIL/C.olean"));
    // A source without its compiled module is one that Lake would build into the entry.
    Entry("CIL/C.lean", "outside the closure");
    if (ClosureManifest(CacheFiles(closure), wholeSources, closureModules))
        throw new Exception("A closure entry holding a source it did not compile was accepted");
    File.Delete(Path.Combine(closure, "CIL/C.lean"));
    using (var opened = new Program
    {
        library = closure, libraryKey = closureKey, libraryModules = closureModules,
        baseModules = new(closureModules.ToDictionary(module => module.Replace('.', '/') + ".olean", _ => "hash"),
            StringComparer.Ordinal)
    })
    {
        opened.RequireReplayedImports(["CIL.A", "CIL.B", "Lean", "Extracted"]);
        ExpectRejection(() => opened.RequireReplayedImports(["CIL.A", "CIL.C"]), "does not hold");
    }
    // Where the whole library is required, the receipt names another key and the sources are not all there.
    var closureManifestBytes = System.Text.Json.JsonSerializer.SerializeToUtf8Bytes(closureManifest);
    File.WriteAllBytes(Path.Combine(closure, "cache-manifest.json"), closureManifestBytes);
    File.WriteAllBytes(Path.Combine(closure, "cache-receipt.hmac"), System.Security.Cryptography.HMACSHA256.HashData(
        verifier.ReceiptKey, System.Text.Encoding.UTF8.GetBytes(closureKey).Concat(closureManifestBytes).ToArray()));
    if (!verifier.CertifiedLocalLibrary(closure, closureKey) || verifier.CertifiedLocalLibrary(closure, wholeKey) ||
        Same(wholeSources, LibrarySources(ReadManifest(closure)!)))
        throw new Exception("A closure entry was accepted as the whole library");
    // One closure entry exists per library: a proof with other imports gets the whole library, not a second one.
    var closureCache = directory + "-closure-cache";
    Directory.CreateDirectory(closureCache);
    File.WriteAllText(ClosureRecord(closureCache, wholeKey), new string('0', 64));
    if (verifier.ClosureLibrary(closureCache, wholeKey, LibrarySources(CommonInputs()), ["CIL.Features"]) is not null ||
        Directory.EnumerateDirectories(closureCache).Any())
        throw new Exception("A second closure entry was opened or built for one library");
    Console.WriteLine("PASS a closure entry is keyed by exactly its modules, rejects an import outside them, is " +
        "never the whole library and is the only one of its library");

    // A few modules stand in for the framework, so a closure and then the whole library are built, replayed
    // and cached in seconds by the code that serves the real sources. Certification under CI never reads the
    // cache, so for these cases this process is not CI and has no supplied library.
    var checkout = Root;
    string[] cleared = ["CI", "GITHUB_ACTIONS", "LEANCIL_CERTIFIED_LIBRARY", "LEANCIL_CERTIFIED_LIBRARY_SHA256",
        "LEANCIL_CACHE_DIR"];
    var inherited = cleared.ToDictionary(name => name, Environment.GetEnvironmentVariable);
    try
    {
        foreach (var name in new[] { "CIL/OleanAudit.lean", "CIL/Interface/Closure.lean", "CIL/Interface/Headers.lean",
            "CIL/Replay.lean", "lean-toolchain", "lake-manifest.json", "global.json", "Directory.Build.props",
            "Directory.Packages.props", ".editorconfig" })
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(fixture, name))!);
            File.Copy(At(name), Path.Combine(fixture, name));
        }
        foreach (var folder in new[] { "Examples", "Tests", "Extractor", "scripts" })
            Directory.CreateDirectory(Path.Combine(fixture, folder));
        void Write(string name, string text) => File.WriteAllText(Path.Combine(fixture, name), text);
        Write("lakefile.toml", "name = \"leancil\"\n\n[[lean_lib]]\nname = \"CIL\"\n" +
            "\n[[lean_exe]]\nname = \"leancil-audit\"\nroot = \"CIL.OleanAudit\"\n");
        Write("CIL/Inside.lean", "import CIL.Base\ntheorem CIL.inside : True := CIL.base\n");
        Write("CIL/Base.lean", "theorem CIL.base : True := True.intro\n");
        Write("CIL/Outside.lean", "theorem CIL.outside : True := True.intro\n");
        Write("CIL.lean", "import CIL.Inside\nimport CIL.Outside\nimport CIL.OleanAudit\n");
        foreach (var name in cleared) Environment.SetEnvironmentVariable(name, null);
        Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", builtCache);
        Root = fixture;
        const string outside = "CIL.Outside";
        string[] roots = ["CIL.Inside"];
        Program Open(string[]? closureRoots)
        {
            var opened = new Program();
            opened.Library(Inputs(At("CIL.lean")), closureRoots: closureRoots);
            return opened;
        }
        var (wholeLibraryKey, fixtureSources) = verifier.LibraryIdentity(CommonInputs());
        var wholeEntry = Path.Combine(builtCache, wholeLibraryKey);
        var first = Open(roots);
        var entry = first.library!;
        var compiledEntry = Path.Combine(entry, ".lake/build/lib/lean");
        try
        {
            string[] expected = ["CIL.Base", "CIL.Inside", "CIL.Interface.Closure", "CIL.Interface.Headers",
                AuditModule, "CIL.Replay"];
            if (first.libraryBuild != "closure" || !first.libraryModules!.SequenceEqual(expected) ||
                first.libraryKey != ClosureKey(wholeLibraryKey, expected) ||
                Path.GetFileName(entry) != first.libraryKey ||
                File.Exists(Path.Combine(entry, "CIL/Outside.lean")) || File.Exists(Path.Combine(entry, "CIL.lean")) ||
                !expected.All(module =>
                    File.Exists(Path.Combine(compiledEntry, module.Replace('.', '/') + ".olean"))) ||
                Directory.Exists(wholeEntry))
                throw new Exception("A first library is not a closure entry of exactly the imported modules");
            first.RequireReplayedImports(roots);
            ExpectRejection(() => first.RequireReplayedImports([outside]), "does not hold");
            // A reader keeps the entry against the whole library's publisher.
            RemoveClosure(builtCache, wholeLibraryKey);
            if (verifier.CachedClosure(builtCache, wholeLibraryKey, fixtureSources) != entry)
                throw new Exception("A closure entry was removed while a process read it");
        }
        finally { ((IDisposable)first).Dispose(); }
        Console.WriteLine($"PASS a closure of {first.libraryModules!.Length} modules is built and replayed from " +
            "an empty cache");

        // A whole library that cannot be built is reported, and leaves the entry for the next run.
        first.completesLibrary = true;
        Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", Path.Combine(builtCache, "no-such-library"));
        ExpectRejection(first.CompleteLibrary, "verified result above stands");
        Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", null);
        using (var second = Open(roots))
            if (second.libraryBuild != "closure-cache" || second.libraryKey != first.libraryKey ||
                Directory.Exists(wholeEntry))
                throw new Exception("A certified closure entry was not reused after a failed whole-library build");
        // The record beside a library is not authenticated: an entry of another library must not seed this one.
        File.WriteAllText(ClosureRecord(builtCache, "another-library"), first.libraryKey);
        var audited = Path.Combine(compiledEntry, AuditModule.Replace('.', '/') + ".olean");
        var certifiedModule = File.ReadAllBytes(audited);
        File.AppendAllText(audited, "rewritten");
        if (verifier.CachedClosure(builtCache, "another-library", fixtureSources) is not null ||
            verifier.CachedClosure(builtCache, wholeLibraryKey, fixtureSources) is not null)
            throw new Exception("A closure entry of another library, or one with a rewritten module, was accepted");
        File.WriteAllBytes(audited, certifiedModule);
        Console.WriteLine("PASS a failed whole-library build is thrown for the command and keeps the entry; a " +
            "rewritten entry and another library's are rejected");

        // After a reported result the whole library is built, seeded from the entry, and replaces it.
        first.completesLibrary = true;
        first.CompleteLibrary();
        using (var whole = Open(roots))
        {
            if (whole.libraryBuild != "cache" || whole.libraryModules is not null ||
                whole.libraryKey != wholeLibraryKey || whole.library != wholeEntry || Directory.Exists(entry) ||
                File.Exists(ClosureRecord(builtCache, wholeLibraryKey)))
                throw new Exception("The whole library did not replace the closure entry or was not preferred");
            // Lean accepts import spellings that a pattern over source text misses, so the boundary is read
            // from compiled import headers: the same proofs are refused once the library is the closure again.
            string[] spellings =
                [$"import Lean import {outside}\n", $"import\n  {outside}\n", "import «CIL».Outside\n"];
            for (var index = 0; index < spellings.Length; index++)
            {
                var proofs = Path.Combine(builtCache, "proof" + index);
                Directory.CreateDirectory(proofs);
                File.WriteAllText(Path.Combine(proofs, "Proof.lean"),
                    spellings[index] + "theorem closureBoundary : True := CIL.outside\n");
                Run([whole.LeanExecutable, "-o", Path.Combine(proofs, "Proof.olean"),
                    Path.Combine(proofs, "Proof.lean")], proofs, Path.Combine(wholeEntry, ".lake/build/lib/lean"));
                whole.libraryModules = null;
                whole.RequireReplayedImports(proofs, proofs);
                whole.libraryModules = first.libraryModules;
                ExpectRejection(() => whole.RequireReplayedImports(proofs, proofs), "does not hold");
            }
            whole.libraryModules = null;
        }
        Console.WriteLine("PASS the whole library replaces the closure entry and is preferred; an import outside " +
            "a closure is refused from the compiled header in every spelling");
    }
    finally
    {
        Root = checkout;
        foreach (var (name, value) in inherited) Environment.SetEnvironmentVariable(name, value);
    }
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
    if (Directory.Exists(directory + "-closure")) Directory.Delete(directory + "-closure", true);
    if (Directory.Exists(directory + "-closure-cache")) Directory.Delete(directory + "-closure-cache", true);
    if (Directory.Exists(builtCache)) Directory.Delete(builtCache, true);
    if (Directory.Exists(fixture)) Directory.Delete(fixture, true);
    if (Directory.Exists(prepared)) Directory.Delete(prepared, true);
    if (Directory.Exists(unrelated)) Directory.Delete(unrelated, true);
}

static void ExpectRejection(Action action, string message)
{
    try { action(); }
    catch (InvalidOperationException error) when (error.Message.Contains(message)) { return; }
    throw new Exception("Expected rejection: " + message);
}
