#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// Child mode: an independent process holding the use lock of one entry until told to stop.
if (args is ["hold-entry", var heldByChild, var childSignal, var childStop])
{
    using var childHold = HoldEntry(heldByChild);
    File.WriteAllText(childSignal, "holding");
    for (var waited = 0; waited < 600 && !File.Exists(childStop); waited++) Thread.Sleep(100);
    return;
}

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
var evictionRoots = At("artifacts/library-eviction-" + Guid.NewGuid().ToString("N")[..8]);
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
        "LEANCIL_CACHE_DIR", "LEANCIL_LIBRARY_RETENTION_DAYS", "LEANCIL_LIBRARY_MAX_ENTRIES"];
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
        // Publishing the first entry evicts what no run uses, says so, and keeps the entry it publishes.
        Directory.CreateDirectory(builtCache);
        var unusedEntry = Path.Combine(builtCache, new string('7', 64));
        var abandonedStaging = Path.Combine(builtCache, new string('8', 64) + "." + new string('e', 32));
        var otherData = Path.Combine(builtCache, "success-v1");
        var otherToolEntry = Path.Combine(builtCache, new string('9', 64));
        foreach (var planted in new[] { unusedEntry, abandonedStaging, otherData, otherToolEntry })
        {
            Directory.CreateDirectory(planted);
            // Only a published entry holds a manifest and a receipt; another tool's directory does not.
            if (planted == unusedEntry)
                foreach (var file in new[] { "cache-manifest.json", "cache-receipt.hmac" })
                    File.WriteAllText(Path.Combine(planted, file), "published");
            Directory.SetLastWriteTimeUtc(planted, DateTime.UtcNow.AddDays(-30));
        }
        libraryEvicted = 0;
        var notices = new StringWriter();
        var standardError = Console.Error;
        Console.SetError(notices);
        Program first;
        try { first = Open(roots); }
        finally { Console.SetError(standardError); }
        standardError.Write(notices);
        var entry = first.library!;
        if (Directory.Exists(unusedEntry) || Directory.Exists(abandonedStaging) || !Directory.Exists(otherData) ||
            !Directory.Exists(otherToolEntry) ||
            !Directory.Exists(entry) ||
            !notices.ToString().Contains("START Removing up to 2 unused certified library cache directories") ||
            !notices.ToString().Contains("END Removing up to 2 unused certified library cache directories: " +
                "removed 2 (exit 0,"))
            throw new Exception("Publishing a library entry did not evict unused entries and say so: " + notices);
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
        Directory.SetLastWriteTimeUtc(entry, DateTime.UtcNow.AddDays(-30));
        using (var second = Open(roots))
            if (second.libraryBuild != "closure-cache" || second.libraryKey != first.libraryKey ||
                Directory.Exists(wholeEntry))
                throw new Exception("A certified closure entry was not reused after a failed whole-library build");
        RequireRecentUse(entry);
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
        RequireRecentUse(wholeEntry);
        Directory.SetLastWriteTimeUtc(wholeEntry, DateTime.UtcNow.AddDays(-30));
        // Opening a cached entry evicts nothing: only a publication does, so the open stays cheap.
        var staleBesideOpen = Path.Combine(builtCache, new string('6', 64));
        Directory.CreateDirectory(staleBesideOpen);
        foreach (var file in new[] { "cache-manifest.json", "cache-receipt.hmac" })
            File.WriteAllText(Path.Combine(staleBesideOpen, file), "published");
        Directory.SetLastWriteTimeUtc(staleBesideOpen, DateTime.UtcNow.AddDays(-30));
        libraryEvicted = 0;
        using (var whole = Open(roots))
        {
            if (!Directory.Exists(staleBesideOpen))
                throw new Exception("Opening a cached library entry evicted another entry");
            // A run that uses an entry holds its lock until it ends, so no pass can take the entry from it.
            using (var probe = HoldEntryExclusively(wholeEntry))
                if (probe is not null) throw new Exception("A run using a library entry did not hold its lock");
            if (whole.libraryBuild != "cache" || whole.libraryModules is not null ||
                whole.libraryKey != wholeLibraryKey || whole.library != wholeEntry || Directory.Exists(entry) ||
                File.Exists(ClosureRecord(builtCache, wholeLibraryKey)))
                throw new Exception("The whole library did not replace the closure entry or was not preferred");
            RequireRecentUse(wholeEntry);
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
        using (var released = HoldEntryExclusively(wholeEntry))
            if (released is null) throw new Exception("A finished run kept the lock of a library entry");
        // The lock is taken before the entry is validated: a run that finds the entry locked waits, then
        // validates what was restored, where a run that validated first would reject the damaged entry.
        var damagedFile = Path.Combine(wholeEntry, "CIL", "Base.lean");
        var undamaged = File.ReadAllBytes(damagedFile);
        var exclusive = HoldEntryExclusively(wholeEntry) ?? throw new Exception("The entry was still locked");
        File.AppendAllText(damagedFile, "-- damaged while locked");
        var waiting = Task.Run(() => Open(roots));
        Thread.Sleep(TimeSpan.FromSeconds(5));
        File.WriteAllBytes(damagedFile, undamaged);
        exclusive.Dispose();
        using (var afterWait = waiting.Result)
            if (afterWait.libraryBuild != "cache" || afterWait.library != wholeEntry)
                throw new Exception("A run validated a library entry before it held the entry's lock");
        // A workspace or watch process runs Lake against its entry for as long as it lives, so it holds the lock.
        editorLibraryDirectory = null;
        try
        {
            if (EditorLibrary() != wholeEntry) throw new Exception("The editor library is not the cache entry");
            // Opening the library renewed the entry, so only its lock can protect it once it is old again, and
            // a handle that nothing roots is closed by a collection, which the probe must not depend on.
            Directory.SetLastWriteTimeUtc(wholeEntry, DateTime.UtcNow.AddDays(-30));
            GC.Collect();
            GC.WaitForPendingFinalizers();
            GC.Collect();
            using (var editorProbe = HoldEntryExclusively(wholeEntry))
                if (editorProbe is not null) throw new Exception("An editor process did not hold its entry's lock");
            if (EvictUnused(builtCache, KeyName(), LibraryStaging(), Days(7), 1, null, library: true)
                    .Contains(wholeLibraryKey) || !Directory.Exists(wholeEntry))
                throw new Exception("A pass removed the entry an editor process was using");
        }
        finally
        {
            foreach (var use in editorLibraryUses) use.Dispose();
            editorLibraryUses.Clear();
            editorLibraryDirectory = null;
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

    // Eviction frees disk that no run needs, so it takes only what this tool made, by exact name, and only
    // what no process uses.
    string LibraryKeyOf(char digit) => new(digit, 64);
    string Staging(char digit, string kind = "") => LibraryKeyOf(digit) + "." + kind + new string('f', 32);
    string NewEvictionRoot()
    {
        var root = Path.Combine(evictionRoots, Guid.NewGuid().ToString("N")[..8]);
        Directory.CreateDirectory(root);
        return root;
    }
    // A published entry holds its manifest and receipt beside its files.
    string PlantEntry(string root, string name, TimeSpan unused, bool receipt = true)
    {
        var path = Path.Combine(root, name);
        Directory.CreateDirectory(Path.Combine(path, ".lake"));
        File.WriteAllText(Path.Combine(path, ".lake", "artifact.olean"), name);
        File.WriteAllText(Path.Combine(path, "lean-toolchain"), "toolchain");
        if (receipt)
        {
            File.WriteAllText(Path.Combine(path, "cache-manifest.json"), "{}");
            File.WriteAllText(Path.Combine(path, "cache-receipt.hmac"), "receipt");
        }
        Directory.SetLastWriteTimeUtc(path, DateTime.UtcNow - unused);
        return path;
    }
    List<string> EvictLibraries(string root, int? limit = null, string? current = null, double retentionDays = 7) =>
        EvictUnused(root, KeyName(), LibraryStaging(), TimeSpan.FromDays(retentionDays), limit, current, library: true);
    TimeSpan Days(double days) => TimeSpan.FromDays(days);
    bool TryLink(string link, string target)
    {
        try { Directory.CreateSymbolicLink(link, target); return true; }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
        if (!OperatingSystem.IsWindows()) return false;
        // A junction needs no privilege.
        using var mklink = System.Diagnostics.Process.Start(new System.Diagnostics.ProcessStartInfo("cmd.exe",
            $"/c mklink /J \"{link}\" \"{target}\"")
        { CreateNoWindow = true, RedirectStandardOutput = true, UseShellExecute = false })!;
        mklink.StandardOutput.ReadToEnd();
        mklink.WaitForExit();
        return mklink.ExitCode == 0 && Directory.Exists(link);
    }

    var retained = NewEvictionRoot();
    var stale = PlantEntry(retained, LibraryKeyOf('1'), Days(8));
    var recent = PlantEntry(retained, LibraryKeyOf('2'), Days(6));
    var inUse = PlantEntry(retained, LibraryKeyOf('3'), Days(30));
    var killedPublisher = PlantEntry(retained, Staging('4'), Days(2), receipt: false);
    var killedDownload = PlantEntry(retained, Staging('5', "download-"), Days(2), receipt: false);
    var killedRemoval = PlantEntry(retained, Staging('6', "evicted-"), Days(2), receipt: false);
    var publishing = PlantEntry(retained, Staging('7'), Days(0), receipt: false);
    // Another tool's directory may have a name that looks like a key; only a publisher's files prove it is ours.
    var otherTool = PlantEntry(retained, LibraryKeyOf('e'), Days(30), receipt: false);
    var halfPublished = PlantEntry(retained, LibraryKeyOf('9'), Days(30));
    File.Delete(Path.Combine(halfPublished, "cache-receipt.hmac"));
    var unrelatedNames = new[] { "success-v1", "notes-" + LibraryKeyOf('8'), LibraryKeyOf('d').ToUpperInvariant(),
            LibraryKeyOf('a')[1..], LibraryKeyOf('b') + "x", LibraryKeyOf('f') + "." + new string('f', 31),
            LibraryKeyOf('f') + ".tmp", LibraryKeyOf('f') + ".invalid-" + new string('f', 32) }
        .Select(name => PlantEntry(retained, name, Days(30))).ToArray();
    var lockFile = Path.Combine(retained, LibraryKeyOf('1') + ".lock");
    File.WriteAllText(lockFile, "");
    File.SetLastWriteTimeUtc(lockFile, DateTime.UtcNow - Days(30));
    var elsewhere = Path.Combine(evictionRoots, "elsewhere");
    Directory.CreateDirectory(elsewhere);
    File.WriteAllText(Path.Combine(elsewhere, "keep.txt"), "outside the cache");
    // The linked directory looks like a published entry, so only its being a link keeps it.
    foreach (var file in new[] { "cache-manifest.json", "cache-receipt.hmac" })
        File.WriteAllText(Path.Combine(elsewhere, file), "published");
    var linkedEntry = Path.Combine(retained, LibraryKeyOf('c'));
    var linked = TryLink(linkedEntry, elsewhere);
    if (linked) Directory.SetLastWriteTimeUtc(linkedEntry, DateTime.UtcNow - Days(30));
    var removed = EvictLibraries(retained, current: Path.GetFileName(inUse));
    if (removed.Count != 4 || Directory.Exists(stale) || Directory.Exists(killedPublisher) ||
        Directory.Exists(killedDownload) || Directory.Exists(killedRemoval))
        throw new Exception("Eviction kept an unused entry or abandoned staging, or removed " +
            removed.Count + " directories");
    if (!Directory.Exists(recent) || !Directory.Exists(inUse) || !Directory.Exists(publishing) ||
        !Directory.Exists(otherTool) || !Directory.Exists(halfPublished) ||
        unrelatedNames.Any(path => !Directory.Exists(path)) || !File.Exists(lockFile) ||
        !File.Exists(Path.Combine(elsewhere, "keep.txt")) || linked && !Directory.Exists(linkedEntry) ||
        Directory.EnumerateDirectories(retained).Any(path => path.Contains(".evicted-")))
        throw new Exception("Eviction removed a used entry, the current entry, a live staging directory, a directory " +
            "without a publisher's files, another name, a lock file or a linked directory");
    Console.WriteLine(linked
        ? "PASS eviction removes library entries unused for the retention period and abandoned staging only"
        : "PASS eviction removes library entries unused for the retention period and abandoned staging only " +
          "(link check not run: no link could be made)");

    // A link inside an entry is removed as a link, never followed into the directory it names.
    var linkTarget = Path.Combine(evictionRoots, "link-target");
    Directory.CreateDirectory(linkTarget);
    File.WriteAllText(Path.Combine(linkTarget, "keep.txt"), "outside the entry");
    var holdsLink = NewEvictionRoot();
    var withLink = PlantEntry(holdsLink, LibraryKeyOf('a'), Days(30));
    if (TryLink(Path.Combine(withLink, ".lake", "link"), linkTarget))
    {
        if (EvictLibraries(holdsLink).Count != 1 || Directory.Exists(withLink) ||
            !File.Exists(Path.Combine(linkTarget, "keep.txt")))
            throw new Exception("Removing an entry followed a link inside it");
        Console.WriteLine("PASS a link inside an evicted entry is removed without touching its target");
    }
    else Console.WriteLine("SKIP link inside an entry: no link could be made");

    // The names are anchored, so a name that only ends in a newline is no key.
    if (KeyName().IsMatch(LibraryKeyOf('a') + "\n") || LibraryStaging().IsMatch(Staging('a') + "\n") ||
        SupportGeneration().IsMatch(LibraryKeyOf('a') + "-" + LibraryKeyOf('b') + "\n") ||
        AbandonedStaging().IsMatch(Staging('a') + "\n") || !KeyName().IsMatch(LibraryKeyOf('a')))
        throw new Exception("A cache name pattern matched a name with a trailing newline");
    Console.WriteLine("PASS cache names match exactly");

    // The least recently used entries beyond the limit go, but one used within a day may be open elsewhere.
    var limited = NewEvictionRoot();
    var todayNames = "abc".Select(digit => Path.GetFileName(
        PlantEntry(limited, LibraryKeyOf(digit), TimeSpan.FromHours(digit - 'a' + 1)))).ToArray();
    var earlier = "def".Select((digit, index) => PlantEntry(limited, LibraryKeyOf(digit), Days(index + 2))).ToArray();
    if (EvictLibraries(limited, 2).Count != 3 || earlier.Any(Directory.Exists) ||
        todayNames.Any(name => !Directory.Exists(Path.Combine(limited, name))))
        throw new Exception("The entry limit removed an entry used within a day, or kept an older one beyond it");
    var spared = NewEvictionRoot();
    "abc".ToList().ForEach(digit => PlantEntry(spared, LibraryKeyOf(digit), TimeSpan.FromHours(digit - 'a' + 1)));
    if (EvictLibraries(spared, 1).Count != 0 || Directory.EnumerateDirectories(spared).Count() != 3)
        throw new Exception("The entry limit removed entries that were all used within a day");
    // The current entry fills one place of the limit even when it is the oldest, and so does a limit of one.
    var reserved = NewEvictionRoot();
    var oldest = PlantEntry(reserved, LibraryKeyOf('a'), Days(5));
    var newest = PlantEntry(reserved, LibraryKeyOf('b'), Days(3));
    var middle = PlantEntry(reserved, LibraryKeyOf('c'), Days(4));
    if (EvictLibraries(reserved, 2, Path.GetFileName(oldest)).Count != 1 || !Directory.Exists(oldest) ||
        !Directory.Exists(newest) || Directory.Exists(middle))
        throw new Exception("The current entry did not hold one place of the entry limit");
    if (EvictLibraries(reserved, 1, Path.GetFileName(oldest)).Count != 1 || !Directory.Exists(oldest) ||
        Directory.Exists(newest))
        throw new Exception("A limit of one did not keep only the current entry");
    Console.WriteLine("PASS the entry limit removes the least recently used entries unused for a day, and no others");

    // Use is recorded by the entry directory's write time, so a used entry outlives one that was not.
    var renewed = NewEvictionRoot();
    var touched = PlantEntry(renewed, LibraryKeyOf('a'), Days(8));
    var untouched = PlantEntry(renewed, LibraryKeyOf('b'), Days(8));
    TouchEntry(touched);
    if (EvictLibraries(renewed).Count != 1 || !Directory.Exists(touched) || Directory.Exists(untouched))
        throw new Exception("An entry that was used after its age passed the retention period was evicted");
    // A run that uses an entry after the pass chose it keeps it: the use is checked again before the rename.
    var chosenEntry = PlantEntry(renewed, LibraryKeyOf('c'), Days(30));
    var chosen = new DirectoryInfo(chosenEntry);
    TouchEntry(chosenEntry);
    if (Evict(chosen, true, Days(7)) || Evict(chosen, false, Days(7)) || !Directory.Exists(chosenEntry))
        throw new Exception("An entry used after it was chosen was removed");
    // Publishing an entry records its use, whatever the age of the directory that was moved into place.
    var publishedFrom = PlantEntry(renewed, Staging('d'), Days(30));
    var publishedAs = Path.Combine(renewed, LibraryKeyOf('d'));
    PlantEntry(renewed, LibraryKeyOf('d'), Days(30));
    File.WriteAllText(Path.Combine(publishedAs, "replaced.txt"), "the entry that was replaced");
    PublishEntry(publishedFrom, publishedAs);
    RequireRecentUse(publishedAs);
    if (Directory.Exists(publishedFrom) || File.Exists(Path.Combine(publishedAs, "replaced.txt")))
        throw new Exception("Publishing an entry kept the staging directory or the entry it replaced");
    Console.WriteLine("PASS using or publishing an entry renews it for the retention period");

    // A donor or a cache directory is recognised however its path is spelled.
    var spelled = Path.Combine(renewed, LibraryKeyOf('a'));
    if (!IsEntryOf(renewed, spelled) || !IsEntryOf(renewed + Path.DirectorySeparatorChar, spelled) ||
        !IsEntryOf(renewed, spelled + Path.DirectorySeparatorChar) || IsEntryOf(renewed, renewed) ||
        IsEntryOf(renewed, Path.Combine(renewed, "nested", LibraryKeyOf('a'))) ||
        IsEntryOf(Path.Combine(renewed, "other"), spelled))
        throw new Exception("A cache entry was not recognised by its path, or another directory was");
    Console.WriteLine("PASS an entry is recognised by its path with or without a trailing separator");

    // A publication passes the settings, the current entry and a stage through, once per process.
    string RunLibraryEviction(string root, string current, string retention, string limit, Action? between = null)
    {
        Environment.SetEnvironmentVariable("LEANCIL_LIBRARY_RETENTION_DAYS", retention);
        Environment.SetEnvironmentVariable("LEANCIL_LIBRARY_MAX_ENTRIES", limit);
        libraryEvicted = 0;
        var notices = new StringWriter();
        var standardError = Console.Error;
        Console.SetError(notices);
        try
        {
            EvictUnusedLibraries(root, current);
            between?.Invoke();
            EvictUnusedLibraries(root, current);
        }
        finally
        {
            Console.SetError(standardError);
            Environment.SetEnvironmentVariable("LEANCIL_LIBRARY_RETENTION_DAYS", null);
            Environment.SetEnvironmentVariable("LEANCIL_LIBRARY_MAX_ENTRIES", null);
        }
        return notices.ToString();
    }
    var configured = NewEvictionRoot();
    var configuredNames = new[] { ('a', TimeSpan.FromHours(1)), ('b', Days(2)), ('c', Days(3)), ('d', Days(4)) }
        .Select(item => Path.GetFileName(PlantEntry(configured, LibraryKeyOf(item.Item1), item.Item2))).ToArray();
    // A second pass would find this entry, so only the once-per-process rule keeps it.
    var limitNotice = RunLibraryEviction(configured, configuredNames[2], "30", "2",
        between: () => PlantEntry(configured, LibraryKeyOf('9'), Days(30)));
    var remaining = Directory.EnumerateDirectories(configured).Select(path => Path.GetFileName(path)).Order();
    var stageLines = limitNotice.ReplaceLineEndings("\n").TrimEnd('\n').Split('\n');
    // Harnesses that require empty stderr strip only stage lines, so the report must be nothing else.
    if (!remaining.SequenceEqual(new[] { configuredNames[0], configuredNames[2], LibraryKeyOf('9') }.Order()) ||
        WithoutStageProgress(limitNotice).Length != 0 || stageLines.Length != 2 ||
        stageLines[0] != "START Removing up to 2 unused certified library cache directories" ||
        !stageLines[1].StartsWith("END Removing up to 2 unused certified library cache directories: removed 2 " +
            "(exit 0, "))
        throw new Exception("The entry limit setting, the current entry or the once-only stage was not honoured: " +
            limitNotice);
    var aged = NewEvictionRoot();
    PlantEntry(aged, LibraryKeyOf('a'), Days(1.2));
    PlantEntry(aged, LibraryKeyOf('b'), Days(2));
    var ageNotice = RunLibraryEviction(aged, LibraryKeyOf('f'), "1.5", "");
    if (Directory.EnumerateDirectories(aged).Count() != 1 || WithoutStageProgress(ageNotice).Length != 0 ||
        !ageNotice.StartsWith("START Removing up to 1 unused certified library cache directory\n"
            .ReplaceLineEndings()))
        throw new Exception("The retention setting was not honoured: " + ageNotice);
    // The stage says how many were removed, which is fewer when a run holds one of those chosen.
    var partial = NewEvictionRoot();
    var partialHeld = PlantEntry(partial, LibraryKeyOf('a'), Days(30));
    PlantEntry(partial, LibraryKeyOf('b'), Days(30));
    string partialNotice;
    using (HoldEntry(partialHeld)) partialNotice = RunLibraryEviction(partial, LibraryKeyOf('f'), "", "");
    if (!partialNotice.Contains("START Removing up to 2 unused certified library cache directories") ||
        !partialNotice.Contains("directories: removed 1 (exit 0, ") || WithoutStageProgress(partialNotice).Length != 0)
        throw new Exception("The stage did not report how many directories were removed: " + partialNotice);
    if (RunLibraryEviction(NewEvictionRoot(), LibraryKeyOf('f'), "", "").Length != 0)
        throw new Exception("Eviction announced a removal that did not happen");
    // No setting removes what was used within a day.
    var minutes = NewEvictionRoot();
    var usedToday = PlantEntry(minutes, LibraryKeyOf('a'), TimeSpan.FromMinutes(5));
    var usedBeforeADay = PlantEntry(minutes, LibraryKeyOf('b'), Days(1.5));
    foreach (var tiny in new[] { "0.001", "0.0000001", "0.5" })
    {
        RunLibraryEviction(minutes, LibraryKeyOf('f'), tiny, "");
        if (!Directory.Exists(usedToday))
            throw new Exception($"A retention of {tiny} days removed an entry used today");
    }
    if (Directory.Exists(usedBeforeADay))
        throw new Exception("An entry unused for more than a day was kept by a retention below a day");
    Console.WriteLine("PASS a publication evicts by the configured retention and limit and reports once, " +
        "as a stage and nothing else on stderr, and never takes an entry used within a day");

    // A reader's lock protects an entry on every platform, since a rename of an open directory can succeed.
    var locks = NewEvictionRoot();
    var readerEntry = PlantEntry(locks, LibraryKeyOf('a'), Days(30));
    var idleEntry = PlantEntry(locks, LibraryKeyOf('b'), Days(30));
    List<string> whileReading;
    using (HoldEntry(readerEntry))
    {
        var pass = Task.Run(() => EvictLibraries(locks));
        if (!pass.Wait(TimeSpan.FromSeconds(30))) throw new Exception("A pass waited for a lock that a reader holds");
        whileReading = pass.Result;
    }
    if (!whileReading.SequenceEqual(new[] { Path.GetFileName(idleEntry) }) || Directory.Exists(idleEntry) ||
        Directory.EnumerateDirectories(locks).Count() != 1 ||
        new[] { ".lake/artifact.olean", "lean-toolchain", "cache-manifest.json", "cache-receipt.hmac" }
            .Any(name => !File.Exists(Path.Combine(readerEntry, name))))
        throw new Exception("A pass removed or damaged an entry that a reader holds, or kept an idle one");
    if (!EvictLibraries(locks).SequenceEqual(new[] { Path.GetFileName(readerEntry) }))
        throw new Exception("An entry was kept once its reader had released it");
    // The lock file stays: a lock on a deleted file would exclude nothing from the next reader.
    if (!File.Exists(EntryUse(readerEntry)) || !File.Exists(EntryUse(idleEntry)))
        throw new Exception("A pass deleted the use lock file of an entry it removed");
    Console.WriteLine("PASS a pass skips an entry whose use lock is held without waiting, and removes it " +
        "once released");

    // Another process holds the lock: the exclusion is the file system's, not a flag of this process.
    var crossed = NewEvictionRoot();
    var childEntry = PlantEntry(crossed, LibraryKeyOf('a'), Days(30));
    var childIdle = PlantEntry(crossed, LibraryKeyOf('b'), Days(30));
    var childReady = Path.Combine(evictionRoots, "ready-" + Guid.NewGuid().ToString("N")[..8]);
    var childRelease = Path.Combine(evictionRoots, "release-" + Guid.NewGuid().ToString("N")[..8]);
    string[] testProcess = Path.GetFileNameWithoutExtension(Environment.ProcessPath) == "dotnet"
        ? [Environment.ProcessPath!, typeof(Program).Assembly.Location] : [Environment.ProcessPath!];
    var childStart = new System.Diagnostics.ProcessStartInfo(testProcess[0]) { UseShellExecute = false };
    foreach (var argument in testProcess.Skip(1).Concat(new[] { "hold-entry", childEntry, childReady, childRelease }))
        childStart.ArgumentList.Add(argument);
    using (var child = System.Diagnostics.Process.Start(childStart)!)
    {
        for (var waited = 0; waited < 1200 && !File.Exists(childReady); waited++) Thread.Sleep(100);
        if (!File.Exists(childReady)) throw new Exception("The process holding an entry did not start");
        var seenByChild = EvictLibraries(crossed);
        File.WriteAllText(childRelease, "release");
        if (!child.WaitForExit(60_000)) throw new Exception("The process holding an entry did not finish");
        if (!seenByChild.SequenceEqual(new[] { Path.GetFileName(childIdle) }) || !Directory.Exists(childEntry))
            throw new Exception("A pass removed an entry another process holds, or kept an idle one");
    }
    if (EvictLibraries(crossed).Count != 1 || Directory.Exists(childEntry))
        throw new Exception("An entry was kept once the process holding it had ended");
    Console.WriteLine("PASS a pass skips an entry that another process holds");
    // A package that requires an entry by path keeps it, whatever its age or the entry limit.
    var pinned = NewEvictionRoot();
    var pinnedEntry = PlantEntry(pinned, LibraryKeyOf('a'), Days(30));
    var unpinned = PlantEntry(pinned, LibraryKeyOf('b'), Days(30));
    var other = PlantEntry(pinned, LibraryKeyOf('c'), Days(30));
    var packageOwner = Path.Combine(evictionRoots, "package-" + Guid.NewGuid().ToString("N")[..8]);
    Directory.CreateDirectory(packageOwner);
    var cacheBefore = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", pinned);
    try { FrameworkPackage(packageOwner, pinnedEntry, pin: true); }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cacheBefore); }
    PlantEntry(pinned, LibraryKeyOf('d'), Days(2));
    var pinFiles = () => Directory.EnumerateFiles(pinned, "*.pin-*").ToArray();
    if (pinFiles().Length != 1) throw new Exception("An editor package did not pin the entry it requires");
    var pinPass = EvictLibraries(pinned, 1);
    if (!Directory.Exists(pinnedEntry) || Directory.Exists(unpinned) || Directory.Exists(other) ||
        pinPass.Count != 3)
        throw new Exception("An entry a package requires was removed, or an unpinned one beyond the limit kept");
    // The package is pointed at another entry. A pin written moments ago is live whatever its package says,
    // since a package being set up has its pin before its lakefile, so the first entry goes a day later.
    var successor = PlantEntry(pinned, LibraryKeyOf('e'), Days(30));
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", pinned);
    try { FrameworkPackage(packageOwner, successor, pin: true); }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cacheBefore); }
    string[] PinsOf(string entry) => Directory.EnumerateFiles(pinned, Path.GetFileName(entry) + ".pin-*").ToArray();
    if (EvictLibraries(pinned).Count != 0 || !Directory.Exists(pinnedEntry))
        throw new Exception("An entry was removed while its pin was younger than a day");
    foreach (var pin in PinsOf(pinnedEntry)) File.SetLastWriteTimeUtc(pin, DateTime.UtcNow - Days(2));
    if (EvictLibraries(pinned).Count != 1 || Directory.Exists(pinnedEntry) || !Directory.Exists(successor) ||
        pinFiles().Length != 1)
        throw new Exception("An entry its package no longer requires was kept, or the one it requires removed");
    // The package directory is missing, as when a drive is unmounted or a project moved: the pin keeps the
    // entry until it has not been renewed for the retention period, which every workspace run does.
    Directory.Move(Path.Combine(packageOwner, ".lake"), Path.Combine(packageOwner, "moved"));
    foreach (var pin in PinsOf(successor)) File.SetLastWriteTimeUtc(pin, DateTime.UtcNow - Days(2));
    if (EvictLibraries(pinned).Count != 0 || !Directory.Exists(successor))
        throw new Exception("An entry was removed within the retention period of its package going missing");
    foreach (var pin in PinsOf(successor)) File.SetLastWriteTimeUtc(pin, DateTime.UtcNow - Days(8));
    if (EvictLibraries(pinned).Count != 1 || Directory.Exists(successor) || pinFiles().Length != 0)
        throw new Exception("An entry whose package stayed missing past the retention period was kept");
    Console.WriteLine("PASS an entry that a package requires by path stays until the package is pointed " +
        "elsewhere, or missing for the retention period");

    // A pin that cannot be understood keeps its entry for the retention period and never fails the pass.
    string PlantPin(string root, string entry, string content, double ageDays)
    {
        var pin = Path.Combine(root, Path.GetFileName(entry) + ".pin-" + Guid.NewGuid().ToString("N"));
        File.WriteAllText(pin, content);
        File.SetLastWriteTimeUtc(pin, DateTime.UtcNow - Days(ageDays));
        return pin;
    }
    var damaged = NewEvictionRoot();
    var damagedEntries = "abcd".Select(digit => PlantEntry(damaged, LibraryKeyOf(digit), Days(30))).ToArray();
    var damagedPins = new[] { "\0\0\0\0", "", "bad|path<>\u0001:?*", "\0" + packageOwner }
        .Select((content, index) => PlantPin(damaged, damagedEntries[index], content, 2)).ToArray();
    var survivors = EvictLibraries(damaged);
    if (survivors.Count != 0 || damagedEntries.Any(path => !Directory.Exists(path)))
        throw new Exception("An entry whose pin could not be read was removed within the retention period");
    foreach (var pin in damagedPins) File.SetLastWriteTimeUtc(pin, DateTime.UtcNow - Days(8));
    if (EvictLibraries(damaged).Count != 4 || damagedPins.Any(File.Exists))
        throw new Exception("A pin that could not be read outlived the retention period");
    // The whole pass, as a verification calls it, raises nothing for a pin or for a root it cannot read, and a
    // failure is reported on the stage line with exit 1.
    string Captured(Action action)
    {
        var captured = new StringWriter();
        var before = Console.Error;
        Console.SetError(captured);
        try { action(); }
        finally { Console.SetError(before); }
        return captured.ToString();
    }
    var careful = NewEvictionRoot();
    PlantPin(careful, PlantEntry(careful, LibraryKeyOf('a'), Days(30)), "\0\0", 2);
    libraryEvicted = 0;
    if (Captured(() => EvictUnusedLibraries(careful, LibraryKeyOf('f'))).Length != 0)
        throw new Exception("A pass over an unreadable pin printed a stage though it chose nothing");
    libraryEvicted = 0;
    var badRoot = Captured(() => EvictUnusedLibraries("not\0a\0directory", LibraryKeyOf('f')));
    if (!badRoot.Contains("END Removing unused certified library cache directories: removed 0, stopped by ") ||
        !badRoot.Contains("(exit 1, ") || WithoutStageProgress(badRoot).Length != 0)
        throw new Exception("A pass that failed did not report it on its stage line: " + badRoot);
    var vanishing = NewEvictionRoot();
    PlantEntry(vanishing, LibraryKeyOf('a'), Days(30));
    PlantEntry(vanishing, LibraryKeyOf('b'), Days(30));
    if (EvictUnused(vanishing, KeyName(), LibraryStaging(), Days(7), 8, null, _ => Directory.Delete(vanishing, true),
            library: true).Count != 0)
        throw new Exception("A pass counted entries it could not remove from a root that vanished");
    var counted = NewEvictionRoot();
    PlantEntry(counted, LibraryKeyOf('a'), Days(30));
    PlantEntry(counted, LibraryKeyOf('b'), Days(30));
    var countReport = new PassReport();
    if (EvictUnused(counted, KeyName(), LibraryStaging(), Days(7), null, null, null, true, countReport).Count != 2 ||
        countReport.Removed != 2)
        throw new Exception("The report did not count the directories removed");
    Console.WriteLine("PASS a pin that cannot be read keeps its entry for the retention period, and no pass raises");

    // A package being set up has a pin before its lakefile, and its pin is read whichever way the root is spelled.
    var setup = NewEvictionRoot();
    var settingUp = PlantEntry(setup, LibraryKeyOf('a'), Days(30));
    var noLakefile = Path.Combine(packageOwner, "no-lakefile");
    Directory.CreateDirectory(noLakefile);
    PlantPin(setup, settingUp, noLakefile, 0);
    if (EvictLibraries(setup).Count != 0 || !Directory.Exists(settingUp))
        throw new Exception("An entry was removed between its package's pin and its package's lakefile");
    // Another process may reach the cache through a link, a junction or another case, so the lakefile's path is
    // judged by its last segment, the key, and never compared whole against the path this pass used.
    var spelledRoot = NewEvictionRoot();
    var spelledEntry = PlantEntry(spelledRoot, LibraryKeyOf('a'), Days(30));
    var spelledLink = Path.Combine(evictionRoots, "link-to-" + Path.GetFileName(spelledRoot));
    var spelledOwner = Path.Combine(packageOwner, "spelled");
    var reachedByLink = TryLink(spelledLink, spelledRoot);
    var entryThroughLink = Path.Combine(reachedByLink ? spelledLink : spelledRoot, LibraryKeyOf('a'));
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", reachedByLink ? spelledLink : spelledRoot);
    try { FrameworkPackage(spelledOwner, entryThroughLink, pin: true); }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cacheBefore); }
    var spelledLakefile = Path.Combine(spelledOwner, ".lake", "leancil-framework", "lakefile.toml");
    void AgePins(string root, double days)
    {
        foreach (var pin in Directory.EnumerateFiles(root, "*.pin-*"))
            File.SetLastWriteTimeUtc(pin, DateTime.UtcNow - Days(days));
    }
    AgePins(spelledRoot, 2);
    if (EvictLibraries(spelledRoot).Count != 0 || !Directory.Exists(spelledEntry))
        throw new Exception("A pin was not recognised because the cache directory was reached through a link");
    var upper = File.ReadAllText(spelledLakefile).Replace(spelledLink.Replace('\\', '/'),
        spelledLink.Replace('\\', '/').ToUpperInvariant()).Replace(spelledRoot.Replace('\\', '/'),
        spelledRoot.Replace('\\', '/').ToUpperInvariant());
    File.WriteAllText(spelledLakefile, upper.Replace(LibraryKeyOf('a'), LibraryKeyOf('a').ToUpperInvariant()));
    if (EvictLibraries(spelledRoot).Count != 0 || !Directory.Exists(spelledEntry))
        throw new Exception("A pin was not recognised because the cache directory was spelled in another case");
    // A lakefile that names another key, or none, releases the entry once its pin is a day old.
    File.WriteAllText(spelledLakefile, File.ReadAllText(spelledLakefile)
        .Replace(LibraryKeyOf('a').ToUpperInvariant(), LibraryKeyOf('b')));
    if (EvictLibraries(spelledRoot).Count != 1 || Directory.Exists(spelledEntry))
        throw new Exception("An entry whose package names another key was kept");
    var namesNone = PlantEntry(spelledRoot, LibraryKeyOf('c'), Days(30));
    File.WriteAllText(spelledLakefile, "name = \"leancil\"\n");
    PlantPin(spelledRoot, namesNone, Path.GetDirectoryName(spelledLakefile)!, 2);
    if (EvictLibraries(spelledRoot).Count != 1 || Directory.Exists(namesNone))
        throw new Exception("An entry whose package names no library was kept");
    Console.WriteLine("PASS a pin is live while its package is set up, and judged by key when the cache is " +
        "spelled in another case or reached by a link");
    if (!reachedByLink) Console.WriteLine("SKIP cache reached through a link: no link or junction could be made");

    // The rule that keeps the library of an editor user who has not run workspace for a week: a package whose
    // lakefile names the entry keeps it however old its pin, and renewing the pin needs no write.
    var keeping = NewEvictionRoot();
    var keptByLakefile = PlantEntry(keeping, LibraryKeyOf('a'), Days(30));
    var keepOwner = Path.Combine(packageOwner, "keeping");
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", keeping);
    try { FrameworkPackage(keepOwner, keptByLakefile, pin: true); }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cacheBefore); }
    AgePins(keeping, 30);
    if (EvictLibraries(keeping).Count != 0 || !Directory.Exists(keptByLakefile))
        throw new Exception("An entry its package's lakefile names was removed after the retention period");
    var keepPin = Directory.EnumerateFiles(keeping, "*.pin-*").Single();
    using (new FileStream(keepPin, FileMode.Open, FileAccess.Read, FileShare.None))
    {
        Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", keeping);
        try { PinEntry(keptByLakefile, Path.Combine(keepOwner, ".lake", "leancil-framework")); }
        finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cacheBefore); }
    }
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", keeping);
    try { PinEntry(keptByLakefile, Path.Combine(keepOwner, ".lake", "leancil-framework")); }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cacheBefore); }
    if (DateTime.UtcNow - File.GetLastWriteTimeUtc(keepPin) > Days(1) ||
        Directory.EnumerateFiles(keeping, "*.pin-*").Count() != 1)
        throw new Exception("Renewing a pin did not touch it, or left another file");
    Console.WriteLine("PASS a package's lakefile keeps its entry whatever the age of the pin, and a held pin " +
        "does not fail its renewal");

    // A pin renewed after the pass decided it was dead is not deleted: it is renamed away, read again, and
    // renamed back.
    var racing = NewEvictionRoot();
    var racedEntry = PlantEntry(racing, LibraryKeyOf('a'), Days(30));
    var racePackage = Path.Combine(packageOwner, "racing");
    Directory.CreateDirectory(racePackage);
    File.WriteAllText(Path.Combine(racePackage, "lakefile.toml"),
        "name = \"leancil\"\nsrcDir = \"" + Path.Combine(racing, LibraryKeyOf('b')).Replace('\\', '/') + "\"\n");
    var racedPin = PlantPin(racing, racedEntry, racePackage, 2);
    beforePinRetired = pin => File.SetLastWriteTimeUtc(pin, DateTime.UtcNow);
    try { EvictLibraries(racing); }
    finally { beforePinRetired = null; }
    if (!File.Exists(racedPin) || !Directory.Exists(racedEntry) ||
        Directory.EnumerateFiles(racing, "*.dead-*").Any())
        throw new Exception("A pin renewed while a pass retired it was deleted, or left under another name");
    if (EvictLibraries(racing).Count != 0 || !File.Exists(racedPin))
        throw new Exception("A renewed pin stopped protecting its entry");
    File.SetLastWriteTimeUtc(racedPin, DateTime.UtcNow - Days(2));
    if (EvictLibraries(racing).Count != 1 || File.Exists(racedPin))
        throw new Exception("A pin of a package that names another key was kept once it was a day old");
    Console.WriteLine("PASS a pin renewed during a pass is renamed back instead of deleted");

    // A lakefile that never answers, as on a dead network mount or a named pipe, delays a pass by a bounded
    // time and keeps what it cannot judge.
    var slowRoot = NewEvictionRoot();
    var slowEntries = "abcd".Select(digit => PlantEntry(slowRoot, LibraryKeyOf(digit), Days(30))).ToArray();
    var slowPackage = Path.Combine(packageOwner, "slow");
    Directory.CreateDirectory(slowPackage);
    foreach (var slowEntry in slowEntries) PlantPin(slowRoot, slowEntry, slowPackage, 2);
    var unpinnedStale = PlantEntry(slowRoot, LibraryKeyOf('e'), Days(30));
    var savedReader = packageReader;
    var savedReadLimit = packageReadLimit;
    var savedPassLimit = passLimit;
    var neverAnswers = new ManualResetEventSlim(false);
    try
    {
        packageReader = _ => { neverAnswers.Wait(); return ""; };
        packageReadLimit = TimeSpan.FromMilliseconds(300);
        var singleRead = System.Diagnostics.Stopwatch.StartNew();
        var single = EvictLibraries(slowRoot);
        if (singleRead.Elapsed > TimeSpan.FromSeconds(30) || slowEntries.Any(path => !Directory.Exists(path)) ||
            !single.SequenceEqual(new[] { Path.GetFileName(unpinnedStale) }))
            throw new Exception("A lakefile that never answers delayed the pass, or its entries were removed");
        // The whole pass is bounded too: it stops reading, stops removing, and says so.
        PlantEntry(slowRoot, LibraryKeyOf('f'), Days(30));
        packageReadLimit = TimeSpan.FromSeconds(30);
        passLimit = TimeSpan.FromMilliseconds(500);
        var wholePass = System.Diagnostics.Stopwatch.StartNew();
        var gaveUp = new PassReport();
        var stopped = EvictUnused(slowRoot, KeyName(), LibraryStaging(), Days(7), null, null, null, true, gaveUp);
        if (wholePass.Elapsed > TimeSpan.FromSeconds(20) || !gaveUp.GaveUp || stopped.Count != 0 ||
            !Directory.Exists(Path.Combine(slowRoot, LibraryKeyOf('f'))))
            throw new Exception("The pass was not bounded, or did not say that it gave up");
        libraryEvicted = 0;
        var gaveUpStage = Captured(() => EvictUnusedLibraries(slowRoot, LibraryKeyOf('9')));
        if (!gaveUpStage.Contains("END ") || !gaveUpStage.Contains("s limit") || !gaveUpStage.Contains("(exit 0, ") ||
            WithoutStageProgress(gaveUpStage).Length != 0)
            throw new Exception("A pass that gave up did not report it: " + gaveUpStage);
    }
    finally
    {
        neverAnswers.Set();
        (packageReader, packageReadLimit, passLimit) = (savedReader, savedReadLimit, savedPassLimit);
    }
    if (OperatingSystem.IsWindows())
        Console.WriteLine("SKIP lakefile that is a named pipe: a Windows directory cannot hold a named pipe");
    else
    {
        var pipeRoot = NewEvictionRoot();
        var pipeEntry = PlantEntry(pipeRoot, LibraryKeyOf('a'), Days(30));
        var pipePackage = Path.Combine(packageOwner, "pipe");
        Directory.CreateDirectory(pipePackage);
        using (var mkfifo = System.Diagnostics.Process.Start("mkfifo", Path.Combine(pipePackage, "lakefile.toml"))!)
            mkfifo.WaitForExit();
        PlantPin(pipeRoot, pipeEntry, pipePackage, 2);
        packageReadLimit = TimeSpan.FromMilliseconds(500);
        try
        {
            var pipeRead = System.Diagnostics.Stopwatch.StartNew();
            if (EvictLibraries(pipeRoot).Count != 0 || !Directory.Exists(pipeEntry) ||
                pipeRead.Elapsed > TimeSpan.FromSeconds(30))
                throw new Exception("A lakefile that is a named pipe delayed the pass, or its entry was removed");
        }
        finally { packageReadLimit = savedReadLimit; }
    }
    Console.WriteLine("PASS a lakefile that never answers delays a pass by a bounded time and keeps its entry");

    // What a pass could not read, it keeps, whatever the age of the pin: a healthy package whose lakefile is
    // never read, because the limit has passed, the clock jumped past it or the read did not finish, keeps the
    // entry of an editor user who has not run workspace for a month.
    var unread = NewEvictionRoot();
    var unreadEntry = PlantEntry(unread, LibraryKeyOf('a'), Days(30));
    var unreadOwner = Path.Combine(packageOwner, "unread");
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", unread);
    try { FrameworkPackage(unreadOwner, unreadEntry, pin: true); }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cacheBefore); }
    AgePins(unread, 30);
    var unreadStale = PlantEntry(unread, LibraryKeyOf('b'), Days(30));
    var unreadRecord = Path.Combine(unread, LibraryKeyOf('d') + ".closure");
    File.WriteAllText(unreadRecord, LibraryKeyOf('7'));
    void RequireUnreadKept(string how, bool staleToo = true)
    {
        if (!Directory.Exists(unreadEntry) || Directory.EnumerateFiles(unread, "*.pin-*").Count() != 1 ||
            staleToo && (!Directory.Exists(unreadStale) || !File.Exists(unreadRecord)))
            throw new Exception("A pass that could not read a healthy package's lakefile removed its pin or its " +
                "entry, or removed another entry after its limit: " + how);
    }
    var zeroLimit = passLimit;
    try
    {
        passLimit = TimeSpan.Zero;
        EvictLibraries(unread);
        RequireUnreadKept("a limit of zero");
    }
    finally { passLimit = zeroLimit; }
    var jumpStart = DateTime.UtcNow;
    var clockCalls = 0;
    var realClock = passClock;
    try
    {
        passClock = () => clockCalls++ == 0 ? jumpStart : jumpStart.AddHours(2);
        var jumped = new PassReport();
        EvictUnused(unread, KeyName(), LibraryStaging(), Days(7), null, null, null, true, jumped);
        RequireUnreadKept("a clock that jumped");
        if (!jumped.GaveUp) throw new Exception("A pass whose clock jumped past its limit did not say so");
    }
    finally { passClock = realClock; }
    var holdsRead = new ManualResetEventSlim(false);
    var readerBefore = (packageReader, packageReadLimit);
    try
    {
        packageReader = _ => { holdsRead.Wait(); return ""; };
        packageReadLimit = TimeSpan.FromMilliseconds(300);
        var timedOut = new PassReport();
        EvictUnused(unread, KeyName(), LibraryStaging(), Days(7), null, null, null, true, timedOut);
        RequireUnreadKept("a read that did not finish", staleToo: false);
        if (timedOut.Unjudged != 1) throw new Exception("A read that did not finish was not counted");
    }
    finally
    {
        holdsRead.Set();
        (packageReader, packageReadLimit) = readerBefore;
    }
    // Read in time, the same pin keeps the entry through the lakefile.
    if (EvictLibraries(unread).Count != 0 || !Directory.Exists(unreadEntry))
        throw new Exception("A readable lakefile did not keep its entry");
    // A lakefile larger than any a workspace writes is not read whole.
    var bigLakefile = Path.Combine(packageOwner, "big.toml");
    File.WriteAllText(bigLakefile, new string('x', 70 * 1024));
    var smallLakefile = Path.Combine(packageOwner, "small.toml");
    File.WriteAllText(smallLakefile, "name = \"leancil\"\n");
    if (ReadSmallFile(smallLakefile) != "name = \"leancil\"\n")
        throw new Exception("A small lakefile was not read");
    try { ReadSmallFile(bigLakefile); throw new Exception("A lakefile of 70 KiB was read whole"); }
    catch (InvalidDataException) { }
    Console.WriteLine("PASS a pass keeps what it could not read, past its limit, on a clock jump or a slow read");

    // A pass set a pin aside and did not finish: the next pass puts it back and judges it, whatever its age.
    var retiredRoot = NewEvictionRoot();
    var retiredEntry = PlantEntry(retiredRoot, LibraryKeyOf('a'), Days(30));
    var retiredOwner = Path.Combine(packageOwner, "retired");
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", retiredRoot);
    try { FrameworkPackage(retiredOwner, retiredEntry, pin: true); }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cacheBefore); }
    AgePins(retiredRoot, 30);
    var retiredPin = Directory.EnumerateFiles(retiredRoot, "*.pin-*").Single();
    var setAside = retiredPin + ".dead-" + new string('f', 32);
    File.Move(retiredPin, setAside);
    var redundant = PlantEntry(retiredRoot, LibraryKeyOf('b'), Days(30));
    var redundantPin = Path.Combine(retiredRoot, LibraryKeyOf('b') + ".pin-" + new string('2', 32));
    File.WriteAllText(redundantPin, retiredOwner);
    File.SetLastWriteTimeUtc(redundantPin, DateTime.UtcNow - Days(30));
    File.WriteAllText(redundantPin + ".dead-" + new string('f', 32), "an older pin of the same name");
    var afterRestore = EvictLibraries(retiredRoot);
    if (!File.Exists(retiredPin) || File.Exists(setAside) || !Directory.Exists(retiredEntry) ||
        Directory.EnumerateFiles(retiredRoot, "*.dead-*").Any() || !afterRestore.Contains(Path.GetFileName(redundant)))
        throw new Exception("A pin that a pass set aside was not put back, or did not keep its entry");
    Console.WriteLine("PASS a pin set aside by an unfinished pass is put back and judged again");

    // Only a file another process holds is waited for: a lock file that cannot be created fails at once.
    var noDirectory = Path.Combine(evictionRoots, "absent-" + Guid.NewGuid().ToString("N")[..8], LibraryKeyOf('a'));
    var failing = System.Diagnostics.Stopwatch.StartNew();
    try { HoldEntry(noDirectory); throw new Exception("A lock file in a missing directory was opened"); }
    catch (IOException error) when (error.Message.Contains(EntryUse(noDirectory)) &&
        !error.Message.Contains("after waiting")) { }
    if (failing.Elapsed > TimeSpan.FromSeconds(5))
        throw new Exception("A lock file that cannot be created was waited for as if another process held it");
    Console.WriteLine("PASS a use lock that cannot be created fails at once and names the file");
    // Files beside an entry go with it, and a lock file stays for the processes that reopen it.
    var beside = NewEvictionRoot();
    var goneEntry = PlantEntry(beside, LibraryKeyOf('a'), Days(30));
    var keptEntry = PlantEntry(beside, LibraryKeyOf('b'), Days(0));
    var deadPin = LibraryKeyOf('a') + ".pin-" + new string('1', 32);
    var recordedClosure = LibraryKeyOf('a') + ".closure";
    foreach (var name in new[] { LibraryKeyOf('a') + ".use", recordedClosure, deadPin, LibraryKeyOf('a') + ".lock",
        LibraryKeyOf('b') + ".lock", LibraryKeyOf('b') + ".use", LibraryKeyOf('c') + ".closure",
        LibraryKeyOf('d') + ".closure", LibraryKeyOf('e') + ".use", LibraryKeyOf('9') + ".lock" })
        File.WriteAllText(Path.Combine(beside, name), name.EndsWith(".closure", StringComparison.Ordinal)
            ? name[0] == 'c' ? LibraryKeyOf('7') : name[0] == 'd' ? LibraryKeyOf('b') : LibraryKeyOf('a') : "");
    File.SetLastWriteTimeUtc(Path.Combine(beside, deadPin), DateTime.UtcNow - Days(8));
    bool Beside(string name) => File.Exists(Path.Combine(beside, name));
    EvictLibraries(beside);
    if (Directory.Exists(goneEntry) || !Directory.Exists(keptEntry) || Beside(recordedClosure) || Beside(deadPin) ||
        Beside(LibraryKeyOf('c') + ".closure"))
        throw new Exception("Files beside a removed entry, or a record of an absent entry, were kept");
    if (!Beside(LibraryKeyOf('a') + ".lock") || !Beside(LibraryKeyOf('b') + ".lock") ||
        !Beside(LibraryKeyOf('b') + ".use") || !Beside(LibraryKeyOf('d') + ".closure") ||
        !Beside(LibraryKeyOf('9') + ".lock") || !Beside(LibraryKeyOf('a') + ".use") ||
        !Beside(LibraryKeyOf('e') + ".use"))
        throw new Exception("A lock file, a use lock file, or the record of a present entry was removed");
    // Files a killed publisher left go after a day, and no earlier.
    var leftovers = NewEvictionRoot();
    var oldDownload = Path.Combine(leftovers, LibraryKeyOf('a') + ".download-" + new string('f', 32) + ".zip");
    var newDownload = Path.Combine(leftovers, LibraryKeyOf('b') + ".download-" + new string('f', 32) + ".zip");
    var oldPin = Path.Combine(leftovers,
        LibraryKeyOf('a') + ".pin-" + new string('1', 32) + ".tmp-" + new string('f', 32));
    var unrelatedZip = Path.Combine(leftovers, "other.download-" + new string('f', 32) + ".zip");
    foreach (var path in new[] { oldDownload, newDownload, oldPin, unrelatedZip }) File.WriteAllText(path, "partial");
    foreach (var path in new[] { oldDownload, oldPin, unrelatedZip })
        File.SetLastWriteTimeUtc(path, DateTime.UtcNow - Days(2));
    EvictLibraries(leftovers);
    if (File.Exists(oldDownload) || File.Exists(oldPin) || !File.Exists(newDownload) || !File.Exists(unrelatedZip))
        throw new Exception("A killed publisher's files were kept past a day, or other files were removed");
    Console.WriteLine("PASS files beside a removed entry go with it, lock files stay, and killed downloads go");

    // A reader holds a file open without sharing: renaming its entry fails, so the entry stays whole.
    if (OperatingSystem.IsWindows())
    {
        var busy = NewEvictionRoot();
        var held = PlantEntry(busy, LibraryKeyOf('a'), Days(30));
        var heldFile = Path.Combine(held, ".lake", "artifact.olean");
        var freed = PlantEntry(busy, LibraryKeyOf('b'), Days(30));
        // A delete in place would remove this file before it failed on the held one.
        var neighbour = Path.Combine(held, "cache-manifest.json");
        List<string> removedWhileHeld;
        using (new FileStream(heldFile, FileMode.Open, FileAccess.Read, FileShare.None))
            removedWhileHeld = EvictLibraries(busy);
        if (removedWhileHeld.Count != 1 || Directory.Exists(freed) || !File.Exists(heldFile) ||
            !File.Exists(neighbour) ||
            File.ReadAllText(heldFile) != Path.GetFileName(held) ||
            Directory.EnumerateDirectories(busy).Count() != 1 || !Directory.Exists(held))
            throw new Exception($"Eviction touched an entry a reader holds open or miscounted " +
                $"({removedWhileHeld.Count})");
        if (EvictLibraries(busy).Count != 1 || Directory.Exists(held))
            throw new Exception("An entry was not removed once its reader had closed it");
        Console.WriteLine("PASS an entry with a file held open is skipped whole and the others are still removed");
    }
    else Console.WriteLine("SKIP held-open file check: other systems delete open files");

    // Invalid settings keep the defaults, so a typo never turns retention off or removes everything.
    var settings = new[] { "LEANCIL_LIBRARY_RETENTION_DAYS", "LEANCIL_LIBRARY_MAX_ENTRIES",
        "LEANCIL_SUPPORT_RETENTION_DAYS" };
    var savedSettings = settings.ToDictionary(name => name, Environment.GetEnvironmentVariable);
    void Setting(string retention, string limit)
    {
        Environment.SetEnvironmentVariable("LEANCIL_LIBRARY_RETENTION_DAYS", retention);
        Environment.SetEnvironmentVariable("LEANCIL_SUPPORT_RETENTION_DAYS", retention);
        Environment.SetEnvironmentVariable("LEANCIL_LIBRARY_MAX_ENTRIES", limit);
    }
    try
    {
        foreach (var name in settings) Environment.SetEnvironmentVariable(name, null);
        if (LibraryRetention != Days(7) || SupportRetention != Days(7) || LibraryEntryLimit != 8)
            throw new Exception("Unset settings did not give the defaults");
        Setting("2.5", "3");
        if (LibraryRetention != Days(2.5) || SupportRetention != Days(2.5) || LibraryEntryLimit != 3)
            throw new Exception("Settings were not honoured");
        // The library never goes below the day that a concurrent run needs; the success cache has no such floor.
        Setting("0.001", "1");
        if (LibraryRetention != Days(1) || SupportRetention != Days(0.001) || LibraryEntryLimit != 1)
            throw new Exception("A library retention below a day was not raised to a day");
        foreach (var invalid in new[] { "0", "-1", "abc", "", " ", "NaN", "-Infinity", "-0" })
        {
            Setting(invalid, invalid);
            if (LibraryRetention != Days(7) || SupportRetention != Days(7) || LibraryEntryLimit != 8)
                throw new Exception($"The setting '{invalid}' did not fall back to the default");
        }
        // A whole number of entries only; a value too large to count means that many.
        foreach (var invalid in new[] { "2.5", "3.0", "1e3", "3,0", "0x3" })
        {
            Setting("7", invalid);
            if (LibraryEntryLimit != 8) throw new Exception($"The entry limit '{invalid}' did not fall back");
        }
        Setting("7", "+3");
        if (LibraryEntryLimit != 3) throw new Exception("A signed entry limit was not read");
        Setting("1e300", "99999999999999999999");
        if (LibraryRetention != TimeSpan.MaxValue || SupportRetention != TimeSpan.MaxValue ||
            LibraryEntryLimit != int.MaxValue)
            throw new Exception("A huge setting did not mean for ever, or as many as can be counted");
        Setting("Infinity", "1");
        if (LibraryRetention != TimeSpan.MaxValue || SupportRetention != TimeSpan.MaxValue)
            throw new Exception("An infinite retention did not mean for ever");
        Setting("99999999999", "2147483648");
        if (LibraryRetention != TimeSpan.MaxValue || LibraryEntryLimit != int.MaxValue)
            throw new Exception("A value past the largest time span or count did not clamp to it");
    }
    finally
    {
        foreach (var (name, value) in savedSettings) Environment.SetEnvironmentVariable(name, value);
    }
    Console.WriteLine("PASS eviction settings are honoured, raised to a day, clamped when huge, and default " +
        "when malformed");
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
    if (Directory.Exists(evictionRoots)) DeleteTree(evictionRoots);
}

// Opening or publishing an entry is a use, which eviction reads from the entry directory's write time.
static void RequireRecentUse(string entry)
{
    if (DateTime.UtcNow - Directory.GetLastWriteTimeUtc(entry) > TimeSpan.FromMinutes(10))
        throw new Exception("A library entry that was opened or published keeps its old use time: " + entry);
}

static void ExpectRejection(Action action, string message)
{
    try { action(); }
    catch (InvalidOperationException error) when (error.Message.Contains(message)) { return; }
    throw new Exception("Expected rejection: " + message);
}
