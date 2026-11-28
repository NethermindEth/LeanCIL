using System.Buffers;
using System.Diagnostics;
using System.Runtime.ExceptionServices;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

// Certified Lean library cache, pinning, retention, eviction and session setup.
partial class Program
{
    /// <summary>The certified library, read in place; deleted on disposal only when this process built it.</summary>
    string? library;
    bool ownsLibrary;
    /// <summary>The cache entry this process published from the library it built, which outlives the process.</summary>
    string? publishedLibrary;
    /// <summary>Length and write time of each file of a library read in place, as it was when opened.</summary>
    SortedDictionary<string, string>? libraryStamps;
    /// <summary>The independently retained manifest of the authenticated or kernel-replayed library.</summary>
    SortedDictionary<string, string>? libraryManifest;
    /// <summary>
    /// Every module of the open library when it is a closure entry, which holds only those; null for the
    /// whole library. <see cref="libraryKey"/> then names exactly this list.
    /// </summary>
    string[]? libraryModules;
    /// <summary>A report was written against a closure entry, so the whole library is still to be built.</summary>
    bool completesLibrary;
    StandaloneCachePromotion? standaloneCachePromotion;
    /// <summary>The use locks of the cache entries this process reads in place, held until it is disposed.</summary>
    readonly List<FileStream> entryUses = [];
    /// <summary>This process's writable package, which requires <see cref="library"/> by path.</summary>
    string? session;
    /// <summary>The base library's compiled module artifacts, taken from its validated manifest.</summary>
    SortedDictionary<string, string>? baseModules;
    const string CertifiedFingerprintsName = "canonical-fingerprints.json";
    string? certifiedFingerprintsSha;
    string? resolvedToolchain;
    bool extractorBuilt;

    const string ExtractorBuildEnvironment = "LEANCIL_PREPARED_EXTRACTOR";
    const string PrebuiltToolsEnvironment = "LEANCIL_PREBUILT_TOOLS";

    /// <summary>The directory of certified library entries, each named by its key, and of the success cache.</summary>
    static string LibraryCacheRoot => Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
        Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL",
            "libraries");

    static string SuccessCacheRoot => Path.Combine(LibraryCacheRoot, "success-v1");

    byte[] ReceiptKey
    {
        get
        {
            if (receiptKey is not null) return receiptKey;
            var directory = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "receipts");
            Directory.CreateDirectory(directory);
            var path = Path.Combine(directory, "key-v1");
            try
            {
                var options = new FileStreamOptions { Mode = FileMode.CreateNew, Access = FileAccess.Write, Share = FileShare.None };
                if (!OperatingSystem.IsWindows()) options.UnixCreateMode = UnixFileMode.UserRead | UnixFileMode.UserWrite;
                using var file = new FileStream(path, options);
                file.Write(RandomNumberGenerator.GetBytes(32));
            }
            catch (IOException) when (File.Exists(path)) { }
            for (var attempt = 0; ; attempt++)
            {
                try
                {
                    var bytes = File.ReadAllBytes(path);
                    if (bytes.Length != 32) throw new InvalidDataException("Invalid local certification key");
                    return receiptKey = bytes;
                }
                catch (IOException) when (attempt < 100) { Thread.Sleep(10); }
            }
        }
    }

    static string ContentKey(string value) => Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(value)));

    SortedDictionary<string, string>? AuthenticatedSuccess(string key)
    {
        var cached = Path.Combine(SuccessCacheRoot, key);
        try
        {
            var manifest = File.ReadAllBytes(Path.Combine(cached, "receipt.json"));
            var signature = File.ReadAllBytes(Path.Combine(cached, "receipt.hmac"));
            if (!CryptographicOperations.FixedTimeEquals(HMACSHA256.HashData(ReceiptKey, Encoding.UTF8.GetBytes(key).Concat(manifest).ToArray()), signature)) return null;
            var expected = JsonSerializer.Deserialize<SortedDictionary<string, string>>(manifest);
            return expected is not null && Same(expected, CacheFiles(Path.Combine(cached, "files"))) ? expected : null;
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException) { return null; }
    }

    bool RestoreSuccess(string key, string destination)
    {
        if (!UseSuccessCache) return false;
        try
        {
            var expected = AuthenticatedSuccess(key);
            if (expected is null) return false;
            CopyTree(Path.Combine(SuccessCacheRoot, key, "files"), destination);
            foreach (var (name, hash) in expected)
                if (Sha(Path.Combine(destination, name)) != hash)
                    throw new InvalidOperationException("Certified cache changed while copying");
            return true;
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException) { return false; }
    }

    /// <summary>The success cache keys this process has published, so its own entries are told from others'.</summary>
    internal readonly List<string> publishedSuccess = [];

    // The cache only saves work: a full disk warns instead of failing a verified result.
    void PublishSuccess(string key, string source, string? family = null)
    {
        if (!UseSuccessCache) return;
        lock (publishedSuccess) publishedSuccess.Add(key);
        try { PublishCertified(key, source, family); }
        catch (IOException error)
        {
            long? free = null;
            try { free = new DriveInfo(Path.GetFullPath(SuccessCacheRoot)).AvailableFreeSpace; }
            catch (Exception probe) when (probe is IOException or ArgumentException or UnauthorizedAccessException) { }
            Console.Error.WriteLine($"warning: success cache {SuccessCacheRoot} not updated" +
                (free is long bytes ? $" ({bytes / 1e9:0.0} GB free)" : "") + ": " + error.Message);
        }
    }

    // Published entries are immutable: an authenticated entry is never duplicated
    // or overwritten, and concurrent publishers race only on an atomic rename.
    void PublishCertified(string key, string source, string? family)
    {
        Directory.CreateDirectory(SuccessCacheRoot);
        var cached = Path.Combine(SuccessCacheRoot, key);
        if (AuthenticatedSuccess(key) is not null)
        {
            TouchEntry(cached);
            return;
        }
        var staging = cached + "." + Guid.NewGuid().ToString("N");
        try
        {
            var files = Path.Combine(staging, "files");
            Directory.CreateDirectory(files);
            if (family is null) CopyTree(source, files);
            else LinkOrCopyTree(source, files, family);
            var manifest = JsonSerializer.SerializeToUtf8Bytes(CacheFiles(files));
            File.WriteAllBytes(Path.Combine(staging, "receipt.json"), manifest);
            File.WriteAllBytes(Path.Combine(staging, "receipt.hmac"), HMACSHA256.HashData(ReceiptKey, Encoding.UTF8.GetBytes(key).Concat(manifest).ToArray()));
            try
            {
                MoveCacheDirectory(staging, cached);
                return;
            }
            catch (IOException) when (Directory.Exists(cached)) { }
            if (AuthenticatedSuccess(key) is not null) return;
            // Replace a corrupt or unauthenticated entry; readers authenticate every file.
            var invalid = cached + ".invalid-" + Guid.NewGuid().ToString("N");
            try
            {
                MoveCacheDirectory(cached, invalid);
                MoveCacheDirectory(staging, cached);
            }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
            finally
            {
                try { if (Directory.Exists(invalid)) Directory.Delete(invalid, true); }
                catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
            }
        }
        finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
    }

    // A reader without delete sharing on Windows can briefly block an atomic cache-directory rename.
    static void MoveCacheDirectory(string source, string destination)
    {
        const int accessDenied = unchecked((int)0x80070005);
        const int sharingViolation = unchecked((int)0x80070020);
        const int retryLimit = 20;
        for (var attempt = 0; ; attempt++)
        {
            try
            {
                Directory.Move(source, destination);
                return;
            }
            catch (IOException error) when (OperatingSystem.IsWindows() && attempt < retryLimit &&
                error.HResult is accessDenied or sharingViolation && !Directory.Exists(destination))
            {
                Thread.Sleep(50);
            }
        }
    }

    static SortedDictionary<string, string> Inputs(string proof, string? settings = null)
        => Inputs(CommonInputs(), proof, settings);

    static SortedDictionary<string, string> CommonInputs(bool libraryOnly = false)
    {
        var files = CertifiedLibraryRoots.Select(root => root + ".lean")
            .Prepend("lake-manifest.json").Prepend("lean-toolchain").Select(name => (name, At(name))).ToList();
        var folders = CertifiedLibraryRoots.Select(root => (root, new[] { ".lean" })).ToList();
        AddHarnessCommonInputs(files, folders, libraryOnly);
        foreach (var (folder, extensions) in folders)
            foreach (var path in Directory.EnumerateFiles(At(folder), "*", SearchOption.AllDirectories))
            {
                if (!extensions.Contains(Path.GetExtension(path))) continue;
                var relative = Path.GetRelativePath(Root, path).Replace('\\', '/');
                if (!relative.Contains("/bin/", StringComparison.Ordinal) &&
                    !relative.Contains("/obj/", StringComparison.Ordinal))
                    files.Add((relative, path));
            }
        var result = HashFiles(files);
        // The checkout key also covers test declarations omitted from the certified library.
        var lakefile = File.ReadAllBytes(At("lakefile.toml"));
        if (!libraryOnly) result[CheckoutLakefileInput] = Convert.ToHexStringLower(SHA256.HashData(lakefile));
        result["lakefile.toml"] = ContentKey(LibraryLakefile(Encoding.UTF8.GetString(lakefile)));
        return result;
    }

    /// <summary>The snapshot key of the complete checkout lakefile, which no certified library contains.</summary>
    const string CheckoutLakefileInput = "checkout:lakefile.toml";

    /// <summary>
    /// The lakefile the certified library is built from: the checkout's, without blank lines, comments,
    /// the editor library, or any plain <c>[[lean_lib]]</c> table that declares only a library outside
    /// <see cref="CertifiedLibraryRoots"/>.
    /// </summary>
    static string LibraryLakefile(string lakefile)
    {
        var lines = lakefile.ReplaceLineEndings("\n").Split('\n');
        // A multi-line string can hold header-like lines, so such a file is kept whole.
        if (lakefile.Contains("\"\"\"", StringComparison.Ordinal) ||
            lakefile.Contains("'''", StringComparison.Ordinal))
            return string.Join("\n", lines);
        var tables = new List<List<string>> { new() };
        foreach (var line in lines)
        {
            if (line.StartsWith('[')) tables.Add([]);
            if (!string.IsNullOrWhiteSpace(line) && !line.TrimStart().StartsWith('#')) tables[^1].Add(line);
        }
        static string? OtherLibrary(List<string> table) =>
            table is ["[[lean_lib]]", var declaration] &&
            LibraryName.Match(declaration) is { Success: true } match && match.Groups[1].Value is var name &&
            !IsCertifiedLibraryModule(name) ? name : null;
        // A certificate must never resolve Extracted to the editor's sources.
        static bool EditorLibrary(List<string> table) =>
            table is ["[[lean_lib]]", var declaration, ..] && declaration == $"name = \"{EditorLibraryName}\"";
        tables.RemoveAll(EditorLibrary);
        var named = string.Join("\n", tables.Where(table => OtherLibrary(table) is null).SelectMany(table => table));
        // A library that a kept table names, such as a default target, stays declared.
        return string.Concat(tables.Where(table => OtherLibrary(table) is not { } name ||
                named.Contains('"' + name + '"', StringComparison.Ordinal))
            .SelectMany(table => table).Select(line => line + "\n"));
    }

    /// <summary>The framework library whose modules are the editor's extraction, below `.lake/leancil`.</summary>
    const string EditorLibraryName = "LeanCILEditor";

    [GeneratedRegex(@"\Aname = ""([A-Za-z_][A-Za-z0-9_.]*)""\z")]
    private static partial Regex LibraryName { get; }

    /// <summary>Copies one certified library source from the checkout; the lakefile is its library view.</summary>
    static void CopyLibrarySource(string name, string destination)
    {
        if (name == "lakefile.toml")
            File.WriteAllText(destination,
                LibraryLakefile(Encoding.UTF8.GetString(File.ReadAllBytes(At(name)))));
        else File.Copy(At(name), destination, true);
    }

    static SortedDictionary<string, string> Inputs(SortedDictionary<string, string> common, string proof,
        string? settings = null)
    {
        var result = new SortedDictionary<string, string>(common, StringComparer.Ordinal);
        result["proof:" + proof] = Sha(proof);
        if (settings is not null)
            result["settings:" + settings] = Sha(settings);

        return result;
    }

    static bool Same(SortedDictionary<string, string> left, SortedDictionary<string, string> right) =>
        left.Count == right.Count && left.All(p => right.TryGetValue(p.Key, out var value) && value == p.Value);

    /// <summary>
    /// Names the first file present on one side only, or the first file whose bytes differ and the offset of the first
    /// differing byte, between two directory trees; null when every file matches.
    /// </summary>
    static string? FirstDifference(string left, string right)
    {
        string[] Files(string root) => [.. Directory.EnumerateFiles(root, "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path)).Order(StringComparer.Ordinal)];
        var (leftFiles, rightFiles) = (Files(left), Files(right));
        foreach (var name in leftFiles.Except(rightFiles, StringComparer.Ordinal).Take(1))
            return $"{name} exists only in {left}";
        foreach (var name in rightFiles.Except(leftFiles, StringComparer.Ordinal).Take(1))
            return $"{name} exists only in {right}";
        foreach (var name in leftFiles)
        {
            var (leftBytes, rightBytes) = (File.ReadAllBytes(Path.Combine(left, name)),
                File.ReadAllBytes(Path.Combine(right, name)));
            var offset = leftBytes.AsSpan().CommonPrefixLength(rightBytes);
            if (offset != leftBytes.Length || offset != rightBytes.Length)
                return $"{name} differs at byte {offset} ({leftBytes.Length} and {rightBytes.Length} bytes) " +
                    $"between {left} and {right}";
        }
        return null;
    }

    bool freshLibrary { get; init; }
    /// <summary>An editor's library is no certificate input, so it is cached where certification never is.</summary>
    bool editorLibrary { get; init; }
    /// <summary>
    /// With no whole library cached, verify one proof against a closure entry of the modules it imports and
    /// build the whole library after reporting. Only for a process that verifies a single proof.
    /// </summary>
    bool importClosureFirst { get; init; }
    bool freshProofs { get; init; }
    string? incrementalLibrary { get; init; }
    string? incrementalDigest { get; init; }
    string? libraryKey;
    string? fullLibraryKey;
    string? libraryBuild;

    // This descriptor is distributed inside the installed CLI, not read from the downloaded archive.
    sealed record CertifiedReleaseAsset(int Schema, string Tag, string Runtime, string LibraryKey,
        string Archive, long ArchiveBytes, string ArchiveSha256, string ManifestSha256);

    static string ReleaseAssetName(string runtime, string key) => $"leancil-library-{runtime}-{key}.zip";

    static bool ValidReleaseAsset(CertifiedReleaseAsset asset, string key) => asset.Schema == 1 &&
        asset.Runtime == RuntimeInformation.RuntimeIdentifier && asset.LibraryKey == key &&
        asset.Tag is not null && Regex.IsMatch(asset.Tag, @"\A[A-Za-z0-9][A-Za-z0-9._-]*\z") &&
        asset.Archive == ReleaseAssetName(asset.Runtime, key) &&
        asset.ArchiveBytes is > 0 and <= 4L * 1024 * 1024 * 1024 &&
        asset.ArchiveSha256 is not null && Regex.IsMatch(asset.ArchiveSha256, @"\A[0-9a-f]{64}\z") &&
        asset.ManifestSha256 is not null && Regex.IsMatch(asset.ManifestSha256, @"\A[0-9a-f]{64}\z");


    void InstallReleasedLibrary(string archive, string staging, string cached, CertifiedReleaseAsset asset)
    {
        var (key, _) = LibraryIdentity(CommonInputs(libraryOnly: true));
        if (!ValidReleaseAsset(asset, key) || new FileInfo(archive).Length != asset.ArchiveBytes ||
            Sha(archive) != asset.ArchiveSha256)
            throw new InvalidDataException("Release archive identity or integrity mismatch");
        using (var zip = System.IO.Compression.ZipFile.OpenRead(archive))
            if (zip.Entries.Count > 100_000 || zip.Entries.Sum(entry => entry.Length) > 8L * 1024 * 1024 * 1024)
                throw new InvalidDataException("Released library exceeds extraction limits");
        // ZipFile rejects entries escaping the destination; the entire extracted tree must match the manifest.
        System.IO.Compression.ZipFile.ExtractToDirectory(archive, staging);
        if (ReplayPreparedLibrary(staging, asset.ManifestSha256) is null)
            throw new InvalidDataException("Released library identity or integrity mismatch");
        var manifestBytes = File.ReadAllBytes(Path.Combine(staging, "cache-manifest.json"));
        File.WriteAllBytes(Path.Combine(staging, "cache-receipt.hmac"),
            HMACSHA256.HashData(ReceiptKey, Encoding.UTF8.GetBytes(key).Concat(manifestBytes).ToArray()));
        PublishEntry(staging, cached);
    }

    static SortedDictionary<string, string> LibrarySources(SortedDictionary<string, string> snapshot) =>
        new(snapshot.Where(p => IsCertifiedLibrarySource(p.Key) ||
            p.Key is "lakefile.toml" or "lake-manifest.json" or "lean-toolchain").ToDictionary(), StringComparer.Ordinal);

    /// <summary>The libraries a certified library builds and kernel-replays: the framework and the binding audit.</summary>
    static readonly string[] CertifiedLibraryRoots = ["CIL", BindingLibrary];

    /// <summary>The binding audit library, whose propositions the deep checks prove about pinned images.</summary>
    const string BindingLibrary = "StrictBinding";

    /// <summary>Whether `module` is a root of <see cref="CertifiedLibraryRoots"/> or a module below one.</summary>
    static bool IsCertifiedLibraryModule(string module) => CertifiedLibraryRoots.Any(root =>
        module == root || module.StartsWith(root + ".", StringComparison.Ordinal));

    /// <summary>Whether the checkout-relative `path` is a source file of a certified library root.</summary>
    static bool IsCertifiedLibrarySource(string path) => CertifiedLibraryRoots.Any(root =>
        path == root + ".lean" || path.StartsWith(root + "/", StringComparison.Ordinal));

    static SortedDictionary<string, string> CacheFiles(string directory) =>
        HashFiles(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path) is not ("cache-manifest.json" or "cache-receipt.hmac"))
            .Select(path => (Path.GetRelativePath(directory, path).Replace('\\', '/'), path)));

    static bool ValidCertifiedLibrary(string directory, string? trustedDigest, string key, SortedDictionary<string, string> sources)
    {
        try
        {
            var bytes = File.ReadAllBytes(Path.Combine(directory, "cache-manifest.json"));
            if (string.IsNullOrWhiteSpace(trustedDigest) || Convert.ToHexStringLower(SHA256.HashData(bytes)) != trustedDigest ||
                File.ReadAllText(Path.Combine(directory, "library-key.txt")) != key)
                return false;
            // Hash the tree once; the pinned manifest and the source binding must describe the same bytes.
            var manifest = JsonSerializer.Deserialize<SortedDictionary<string, string>>(bytes);
            var files = CacheFiles(directory);
            return manifest is not null && manifest.ContainsKey(".lake/build/lib/lean/CIL.olean") && Same(manifest, files) &&
                Same(sources, LibrarySources(files));
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException) { return false; }
    }

    bool CertifiedLocalLibrary(string directory, string key)
    {
        try
        {
            var manifest = File.ReadAllBytes(Path.Combine(directory, "cache-manifest.json"));
            return CryptographicOperations.FixedTimeEquals(
                HMACSHA256.HashData(ReceiptKey, Encoding.UTF8.GetBytes(key).Concat(manifest).ToArray()),
                File.ReadAllBytes(Path.Combine(directory, "cache-receipt.hmac")));
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return false; }
    }

    /// <summary>The length and write time of every file <see cref="CacheFiles"/> hashes, by the same names.</summary>
    static SortedDictionary<string, string> FileStamps(string directory) =>
        new(new DirectoryInfo(directory).EnumerateFiles("*", SearchOption.AllDirectories)
            .Where(file => file.Name is not ("cache-manifest.json" or "cache-receipt.hmac"))
            .ToDictionary(file => Path.GetRelativePath(directory, file.FullName).Replace('\\', '/'), FileStamp),
            StringComparer.Ordinal);

    static string FileStamp(FileInfo file) => string.Create(System.Globalization.CultureInfo.InvariantCulture,
        $"{file.Length}:{file.LastWriteTimeUtc.Ticks}");

    /// <summary>
    /// The stamps of a cache entry whose files all hash to `manifest`; null, naming the entry on stderr, when
    /// they do not. A package that requires an entry by path lets Lake rebuild a module it finds stale into the
    /// entry, so every run hashes every file. Stamps equal before and after hashing describe the hashed bytes.
    /// </summary>
    static SortedDictionary<string, string>? HashedCacheEntry(string cached,
        SortedDictionary<string, string> manifest)
    {
        string reason;
        try
        {
            var stamps = FileStamps(cached);
            if (Same(manifest, CacheFiles(cached)) && Same(stamps, FileStamps(cached))) return stamps;
            reason = "its files no longer match the manifest it was certified with";
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { reason = error.Message; }
        Console.Error.WriteLine("The cached certified library " + cached + " is not used and is replaced: " + reason);
        return null;
    }

    /// <summary>
    /// Fails if the library this process reads in place gained or lost a file, or any file differs by length or
    /// write time, since it was opened: a build that wrote into it would otherwise pass for the certified bytes.
    /// </summary>
    void RequireUnchangedLibrary()
    {
        if (libraryStamps is null) return;
        var current = FileStamps(library!);
        if (libraryStamps.Keys.Union(current.Keys).FirstOrDefault(name =>
                libraryStamps.GetValueOrDefault(name) != current.GetValueOrDefault(name)) is { } changed)
            throw new InvalidOperationException("The certified library changed on disk during verification: " +
                Path.Combine(library!, changed));
    }

    /// <summary>Physical file hashes from a whole-library check, usable until the next command or callback.</summary>
    sealed class CheckedLibraryContents(string library, IReadOnlyDictionary<string, string> files)
    {
        public readonly string Library = library;
        public readonly IReadOnlyDictionary<string, string> Files = files;
    }

    /// <summary>Requires every library file to retain its certified bytes, including in a private build.</summary>
    CheckedLibraryContents CheckCertifiedLibraryContents()
    {
        var files = libraryManifest is not null ? CacheFiles(library!) : null;
        if (files is null || !Same(libraryManifest!, files))
            throw new InvalidOperationException("The certified library contents changed during verification");
        return new(library!, files);
    }

    void RequireCertifiedLibraryContents() => CheckCertifiedLibraryContents();

    // The pinned manifest binds the source snapshot before copying. Hash exactly the bytes
    // written to the private destination; callers independently verify that destination.
    static bool CopyCertifiedLibrary(string source, string destination, string? trustedDigest,
        string key, SortedDictionary<string, string> sources)
    {
        try
        {
            var bytes = File.ReadAllBytes(Path.Combine(source, "cache-manifest.json"));
            if (string.IsNullOrWhiteSpace(trustedDigest) ||
                Convert.ToHexStringLower(SHA256.HashData(bytes)) != trustedDigest ||
                File.ReadAllText(Path.Combine(source, "library-key.txt")) != key) return false;
            var manifest = JsonSerializer.Deserialize<SortedDictionary<string, string>>(bytes);
            if (manifest is null || !manifest.ContainsKey(".lake/build/lib/lean/CIL.olean") ||
                !Same(sources, LibrarySources(manifest))) return false;
            var files = Directory.EnumerateFiles(source, "*", SearchOption.AllDirectories)
                .ToDictionary(path => Path.GetRelativePath(source, path).Replace('\\', '/'),
                    path => path, StringComparer.Ordinal);
            static bool Included(string path) =>
                Path.GetFileName(path) is not ("cache-manifest.json" or "cache-receipt.hmac");
            if (!manifest.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(files.Keys.Where(Included))) return false;
            var entries = files.ToArray();
            var valid = new bool[entries.Length];
            var failures = new ExceptionDispatchInfo?[entries.Length];
            const int maximumWorkers = 4;
            Parallel.For(0, entries.Length,
                new ParallelOptions { MaxDegreeOfParallelism = Math.Min(maximumWorkers, Environment.ProcessorCount) },
                index =>
                {
                    try
                    {
                        var (name, path) = entries[index];
                        var target = Path.Combine(destination, name);
                        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                        if (Included(name)) valid[index] = HashAndCopyFile(path, target, manifest[name]);
                        else { File.Copy(path, target, true); valid[index] = true; }
                    }
                    catch (Exception error) { failures[index] = ExceptionDispatchInfo.Capture(error); }
                });
            for (var index = 0; index < entries.Length; index++)
            {
                failures[index]?.Throw();
                if (!valid[index]) return false;
            }
            return files.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                Directory.EnumerateFiles(source, "*", SearchOption.AllDirectories)
                    .Select(path => Path.GetRelativePath(source, path).Replace('\\', '/')));
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException)
        {
            return false;
        }
    }

    static bool HashAndCopyFile(string source, string destination, string expectedHash)
    {
        const int copyBufferSize = 1024 * 1024;
        var buffer = ArrayPool<byte>.Shared.Rent(copyBufferSize);
        try
        {
            using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
            using var input = new FileStream(source, FileMode.Open, FileAccess.Read, FileShare.Read, 1,
                FileOptions.SequentialScan);
            using var output = new FileStream(destination, FileMode.Create, FileAccess.Write, FileShare.None, 1);
            int length;
            while ((length = input.Read(buffer)) != 0)
            {
                hash.AppendData(buffer, 0, length);
                output.Write(buffer, 0, length);
            }
            if (Convert.ToHexStringLower(hash.GetHashAndReset()) != expectedHash) return false;
            if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(destination, File.GetUnixFileMode(source));
            return true;
        }
        finally { ArrayPool<byte>.Shared.Return(buffer); }
    }
    static void CopyTree(string source, string destination)
    {
        foreach (var path in Directory.EnumerateFiles(source, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(destination, Path.GetRelativePath(source, path));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(path, target, true);
        }
    }

    // Generations of one family share most compiled files; cache readers only copy out, so a
    // hard link is never written through. Each candidate is rehashed against the source bytes.
    static void LinkOrCopyTree(string source, string destination, string family)
    {
        var known = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var generation in Directory.EnumerateDirectories(SuccessCacheRoot, family + "-*"))
        {
            if (Path.GetFileName(generation).Contains('.')) continue;
            try
            {
                var manifest = JsonSerializer.Deserialize<SortedDictionary<string, string>>(File.ReadAllBytes(Path.Combine(generation, "receipt.json")));
                foreach (var (name, hash) in manifest ?? []) known.TryAdd(hash, Path.Combine(generation, "files", name));
            }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException) { }
        }
        foreach (var path in Directory.EnumerateFiles(source, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(destination, Path.GetRelativePath(source, path));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            var hash = Sha(path);
            if (!known.TryGetValue(hash, out var existing) || !TryHardLink(existing, hash, target)) File.Copy(path, target, true);
        }
    }

    static bool TryHardLink(string existing, string hash, string target)
    {
        try
        {
            if (Sha(existing) != hash) return false;
            return OperatingSystem.IsWindows() ? CreateHardLinkW(Win32Path(target), Win32Path(existing), 0) : link(existing, target) == 0;
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return false; }
    }

    // Cache paths exceed MAX_PATH, which raw Win32 calls reject without the extended prefix.
    static string Win32Path(string path)
    {
        var full = Path.GetFullPath(path);
        return full.StartsWith(@"\\?\", StringComparison.Ordinal) ? full
            : full.StartsWith(@"\\", StringComparison.Ordinal) ? @"\\?\UNC\" + full[2..] : @"\\?\" + full;
    }

    [DllImport("kernel32", CharSet = CharSet.Unicode)]
    static extern bool CreateHardLinkW(string fileName, string existingFileName, nint securityAttributes);

    [DllImport("libc", CharSet = CharSet.Ansi)]
    static extern int link(string existing, string target);

    // Recency is last use: opening, restoring or publishing a cache entry renews it.
    static void TouchEntry(string entry)
    {
        try { Directory.SetLastWriteTimeUtc(entry, DateTime.UtcNow); }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
    }

    /// <summary>Publishes the finished directory staging as the entry directory, replacing any entry there.</summary>
    static void PublishEntry(string staging, string directory)
    {
        if (Directory.Exists(directory)) Directory.Delete(directory, true);
        Directory.Move(staging, directory);
        TouchEntry(directory);
    }

    /// <summary>The name of a certified library entry: its key.</summary>
    [GeneratedRegex(@"\A[0-9a-f]{64}\z")]
    private static partial Regex KeyName { get; }

    [GeneratedRegex(@"\A[0-9a-f]{64}-[0-9a-f]{64}\z")]
    private static partial Regex SupportGeneration { get; }

    [GeneratedRegex(@"\A[0-9a-f]{64}(?:-[0-9a-f]{64})?\.(?:(?:invalid|evicted)-)?[0-9a-f]{32}\z")]
    private static partial Regex AbandonedStaging { get; }

    /// <summary>The names a library publisher gives a directory it is still filling or has set aside.</summary>
    [GeneratedRegex(@"\A[0-9a-f]{64}\.(?:(?:evicted|download)-)?[0-9a-f]{32}\z")]
    private static partial Regex LibraryStaging { get; }

    /// <summary>A file beside a library entry that goes with it: a closure record or an editor pin.</summary>
    [GeneratedRegex(@"\A(?<key>[0-9a-f]{64})\.(?<kind>closure|pin-[0-9a-f]{32})\z")]
    private static partial Regex LibrarySidecar { get; }

    /// <summary>A file a killed publisher leaves: a download archive or a pin being written.</summary>
    [GeneratedRegex(@"\A[0-9a-f]{64}\.(?:download-[0-9a-f]{32}\.zip|pin-[0-9a-f]{32}\.tmp-[0-9a-f]{32})\z")]
    private static partial Regex LibraryStagingFile { get; }

    /// <summary>A pin a pass set aside while it judged it, by the name it was given.</summary>
    [GeneratedRegex(@"\A[0-9a-f]{64}\.pin-[0-9a-f]{32}\.dead-[0-9a-f]{32}\z")]
    private static partial Regex RetiredPin { get; }

    /// <summary>The part of a retired pin's name that the pin's own name lacks.</summary>
    [GeneratedRegex(@"\.dead-[0-9a-f]{32}\z")]
    private static partial Regex DeadPinSuffix { get; }

    /// <summary>The line of a framework package's lakefile that names the directory of the library.</summary>
    [GeneratedRegex(@"^srcDir = (?<path>"".*"")\r?$", RegexOptions.Multiline)]
    private static partial Regex SourceDirectoryLine { get; }

    static int supportEvicted;
    static int libraryEvicted;

    /// <summary>A staging directory this old belongs to a publisher that was killed.</summary>
    static readonly TimeSpan AbandonedAfter = TimeSpan.FromDays(1);

    /// <summary>A library entry used within this time may be open in a concurrent run; no setting removes it.</summary>
    static readonly TimeSpan RecentUse = TimeSpan.FromDays(1);

    const int DefaultRetentionDays = 7;
    const int DefaultLibraryEntries = 8;

    /// <summary>
    /// The positive number of days an environment variable holds, with infinity and a value too large for a
    /// time span meaning for ever; the default for an unset, malformed, NaN or non-positive value.
    /// </summary>
    static TimeSpan RetentionFromEnvironment(string variable)
    {
        if (!double.TryParse(Environment.GetEnvironmentVariable(variable), System.Globalization.NumberStyles.Float,
                System.Globalization.CultureInfo.InvariantCulture, out var days) || double.IsNaN(days) || days <= 0)
            return TimeSpan.FromDays(DefaultRetentionDays);
        return days >= TimeSpan.MaxValue.TotalDays ? TimeSpan.MaxValue : TimeSpan.FromDays(days);
    }

    static TimeSpan SupportRetention => RetentionFromEnvironment("LEANCIL_SUPPORT_RETENTION_DAYS");

    /// <summary>How long a library entry may go unused: `LEANCIL_LIBRARY_RETENTION_DAYS`, never below a day.</summary>
    static TimeSpan LibraryRetention =>
        TimeSpan.FromTicks(Math.Max(RetentionFromEnvironment("LEANCIL_LIBRARY_RETENTION_DAYS").Ticks, RecentUse.Ticks));

    /// <summary>
    /// The most certified library entries to keep, as `LEANCIL_LIBRARY_MAX_ENTRIES` sets it: a positive whole
    /// number, with one too large for an int meaning that many; the default for any other value.
    /// </summary>
    static int LibraryEntryLimit =>
        System.Numerics.BigInteger.TryParse(Environment.GetEnvironmentVariable("LEANCIL_LIBRARY_MAX_ENTRIES"),
            System.Globalization.NumberStyles.Integer, System.Globalization.CultureInfo.InvariantCulture,
            out var limit) && limit > 0
            ? (int)System.Numerics.BigInteger.Min(limit, int.MaxValue) : DefaultLibraryEntries;

    /// <summary>
    /// Beside a library entry: a file that every process reading the entry in place holds open shared from
    /// before it validates the entry until it ends, and that a pass must hold exclusively to remove the entry.
    /// </summary>
    static string EntryUse(string entry) => entry + ".use";

    /// <summary>
    /// Holds the use lock of `entry` shared, so no pass removes it. A pass holds the lock only while it renames
    /// the entry away, so a short wait gets it. Only a file that exists can be held by another process, so a
    /// failure to open a file that does not exist, such as a full disk or a missing directory, is not waited
    /// for. Any failure names the file and carries the operating system's reason. Null where the lock file
    /// cannot be created for want of permission, which leaves the entry protected only by its recent use.
    /// Dispose the stream to release it.
    /// </summary>
    static FileStream? HoldEntry(string entry)
    {
        for (var attempt = 0; ; attempt++)
        {
            try { return new FileStream(EntryUse(entry), FileMode.OpenOrCreate, FileAccess.Read, FileShare.Read); }
            catch (UnauthorizedAccessException) { return null; }
            catch (IOException) when (attempt < 200 && File.Exists(EntryUse(entry))) { Thread.Sleep(50); }
            catch (IOException error)
            {
                throw new IOException("The use lock file " + EntryUse(entry) + " of the certified library cache " +
                    "entry could not be opened" + (attempt > 0 ? " after waiting for it" : "") + ": " + error.Message,
                    error);
            }
        }
    }

    /// <summary>
    /// Records that this process uses `entry` and holds its use lock until it is disposed, before anything
    /// reads the entry, so that no pass removes it from under the process.
    /// </summary>
    void UseEntry(string entry)
    {
        if (HoldEntry(entry) is { } use) entryUses.Add(use);
        TouchEntry(entry);
    }

    /// <summary>The use lock of `entry` held exclusively, or null at once when a reader holds it.</summary>
    static FileStream? HoldEntryExclusively(string entry)
    {
        try { return new FileStream(EntryUse(entry), FileMode.OpenOrCreate, FileAccess.ReadWrite, FileShare.None); }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return null; }
    }

    static void DeleteQuietly(string file)
    {
        try { File.Delete(file); }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
    }

    /// <summary>Renames `directory` to a dotted name, which readers skip, so none sees it half deleted.</summary>
    static string MoveAside(string directory)
    {
        var aside = directory + ".evicted-" + Guid.NewGuid().ToString("N");
        Directory.Move(directory, aside);
        return aside;
    }

    /// <summary>Whether path names a directory directly under cacheRoot, however either is spelled.</summary>
    static bool IsEntryOf(string cacheRoot, string path) =>
        Path.GetDirectoryName(Path.TrimEndingDirectorySeparator(Path.GetFullPath(path))) is { } parent &&
        SamePath(parent, cacheRoot);

    /// <summary>
    /// Whether two spellings of a path made by one process name the same directory. It resolves relative
    /// segments and separators only, so it is for paths this process derived from one setting, never for
    /// paths another process wrote.
    /// </summary>
    static bool SamePath(string first, string second) =>
        LocationComparer.Equals(Path.GetFullPath(first), Path.GetFullPath(second));

    /// <summary>Whether `entry` holds the manifest and receipt that only a library publisher writes.</summary>
    static bool HoldsReceipt(DirectoryInfo entry) =>
        File.Exists(Path.Combine(entry.FullName, "cache-manifest.json")) &&
        File.Exists(Path.Combine(entry.FullName, "cache-receipt.hmac"));

    /// <summary>
    /// Records that the package at `package`, which requires the library entry `entry` by path, needs it:
    /// beside the entry, so the entry's hashed files stay as certified. The pin is written under another
    /// name and moved into place, so a pass never reads half of it. A pin that exists is renewed by touching
    /// it, since its name is the hash of the content it holds, so a scanner holding it open cannot fail the
    /// command. Does nothing for a library that is not an entry of the cache.
    /// </summary>
    static void PinEntry(string entry, string package)
    {
        var full = Path.TrimEndingDirectorySeparator(Path.GetFullPath(entry));
        if (Path.GetDirectoryName(full) is not { } parent || !KeyName.IsMatch(Path.GetFileName(full)) ||
            !SamePath(parent, LibraryCacheRoot))
            return;
        var packageFull = Path.GetFullPath(package);
        var pin = Path.Combine(parent, Path.GetFileName(full) + ".pin-" + ContentKey(packageFull)[..32]);
        try
        {
            if (File.Exists(pin))
            {
                if (File.ReadAllText(pin) == packageFull) File.SetLastWriteTimeUtc(pin, DateTime.UtcNow);
                else File.Delete(pin);
                if (File.Exists(pin)) return;
            }
        }
        // A pin another process holds briefly still names this package, and its lakefile keeps the entry; a pin
        // a pass moved aside meanwhile is written again below.
        catch (Exception error) when (error is IOException or UnauthorizedAccessException)
        {
            if (File.Exists(pin)) return;
        }
        var writing = pin + ".tmp-" + Guid.NewGuid().ToString("N");
        File.WriteAllText(writing, packageFull);
        // A pass reading the old pin holds it for a moment, and Windows refuses to replace a file that is open.
        for (var attempt = 0; ; attempt++)
        {
            try { File.Move(writing, pin, true); return; }
            catch (Exception error) when (attempt < 40 && error is IOException or UnauthorizedAccessException)
            {
                Thread.Sleep(25);
            }
        }
    }

    /// <summary>The directory a framework lakefile reads the library from, or empty when it names none.</summary>
    static string SourceDirectoryOf(string lakefile) => SourceDirectoryLine.Match(lakefile) is { Success: true } line
        ? JsonSerializer.Deserialize<string>(line.Groups["path"].Value) ?? "" : "";

    /// <summary>What a library pass did, for the stage that reports it.</summary>
    sealed class PassReport
    {
        public int Removed;
        public int Unjudged;
        /// <summary>The pass reached its limit; from then on it read and removed nothing.</summary>
        public bool GaveUp;
        public string? Failure;
    }

    /// <summary>The longest a pass waits for one package's lakefile, which lies outside the cache.</summary>
    internal static TimeSpan packageReadLimit = TimeSpan.FromSeconds(2);

    /// <summary>The longest a library pass runs before it stops choosing and reading and reports.</summary>
    internal static TimeSpan passLimit = TimeSpan.FromSeconds(60);

    /// <summary>Reads a package's lakefile for a pass; tests replace it with a slow or blocking reader.</summary>
    internal static Func<string, string> packageReader = ReadSmallFile;

    static readonly DateTime PassClockOrigin = DateTime.UtcNow;
    static readonly Stopwatch PassClockRun = Stopwatch.StartNew();

    /// <summary>
    /// The clock a pass takes its time limit from. It counts from when the process first read it, so a change
    /// of the system clock moves it neither forward nor back; tests replace it to jump past the limit.
    /// </summary>
    internal static Func<DateTime> passClock = () => PassClockOrigin + PassClockRun.Elapsed;

    /// <summary>Called with a pin's path just before a pass retires it; tests renew the pin here.</summary>
    internal static Action<string> beforePinRetired = static _ => { };

    /// <summary>The largest lakefile a pass reads; the one a workspace writes is a few hundred bytes.</summary>
    const int MaxLakefileBytes = 64 * 1024;

    /// <summary>The text of `path`, which must hold at most <see cref="MaxLakefileBytes"/> bytes.</summary>
    static string ReadSmallFile(string path)
    {
        using var file = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
        var buffer = new byte[MaxLakefileBytes + 1];
        var length = 0;
        int read;
        while (length < buffer.Length && (read = file.Read(buffer, length, buffer.Length - length)) > 0)
            length += read;
        if (length > MaxLakefileBytes) throw new InvalidDataException(path + " is larger than a lakefile.");
        return Encoding.UTF8.GetString(buffer, 0, length);
    }

    /// <summary>
    /// Reads the lakefile in `package` on a background thread that is never waited for beyond the limit, since
    /// a network mount that does not answer, or a named pipe, blocks a read without end. Finished is false
    /// when the read was not attempted because the pass had reached its limit, or did not complete in time, and
    /// the caller must then keep what it cannot judge; with Finished, the text is null when the read failed.
    /// A read that does not complete within the rest of the pass limit ends the pass.
    /// </summary>
    static (bool Finished, string? Text) ReadPackageLakefile(string package, DateTime deadline, PassReport report)
    {
        var remaining = report.GaveUp ? TimeSpan.Zero : deadline - passClock();
        if (remaining <= TimeSpan.Zero)
        {
            report.GaveUp = true;
            return (false, null);
        }
        var wait = remaining < packageReadLimit ? remaining : packageReadLimit;
        string? text = null;
        var worker = new Thread(() =>
        {
            try { text = packageReader(Path.Combine(package, "lakefile.toml")); }
            catch (Exception) { }
        }) { IsBackground = true };
        worker.Start();
        if (worker.Join(wait)) return (true, text);
        report.Unjudged++;
        // The wait is rounded down to whole milliseconds, so the clock can still read before the deadline here.
        if (wait == remaining) report.GaveUp = true;
        return (false, null);
    }

    /// <summary>The last directory name of a path spelled with either separator.</summary>
    static string LastSegment(string path)
    {
        var trimmed = path.TrimEnd('/', '\\');
        return trimmed[(trimmed.LastIndexOfAny(['/', '\\']) + 1)..];
    }

    /// <summary>
    /// Whether the package a pin names still needs the entry with key `key`. A pin renewed within a day is
    /// live, so a package being set up is never caught between its pin and its lakefile. Otherwise the
    /// package's framework lakefile decides when it can be read in time: the pin is dead when the directory it
    /// names ends in another key or names none. Paths are not compared whole, since another process may have
    /// reached the cache through a link, a drive letter or another spelling; keys are hashes, so the last
    /// segment tells the entry. A lakefile that was not read, because the pass limit had passed or the read did
    /// not finish in time, leaves the pin live whatever its age, since the pass cannot judge it. When a read
    /// finished and found the package missing or unreadable, which an unmounted drive, a moved project and a
    /// pin damaged by a crash all look like, the pin stays live until it has not been renewed for `retention`;
    /// every `workspace` run renews it. Whatever reading the pin or the lakefile raises counts as unreadable.
    /// </summary>
    static bool PinLive(FileInfo pin, string key, TimeSpan retention, DateTime now, DateTime deadline,
        PassReport report)
    {
        var age = now - pin.LastWriteTimeUtc;
        if (age <= RecentUse) return true;
        bool? requires = null;
        try
        {
            var package = File.ReadAllText(pin.FullName).Trim();
            if (package.Length > 0)
            {
                var (finished, lakefile) = ReadPackageLakefile(package, deadline, report);
                if (!finished) return true;
                if (lakefile is not null)
                    requires = string.Equals(LastSegment(SourceDirectoryOf(lakefile)), key,
                        StringComparison.OrdinalIgnoreCase);
            }
        }
        catch (Exception) { }
        return requires ?? age <= retention;
    }

    /// <summary>
    /// Puts a pin that a pass set aside and did not finish with back under its name, whatever its age, so that
    /// the pass judges it by the normal rules. A pin that took the name meanwhile makes the old one redundant.
    /// Null when the file could not be restored.
    /// </summary>
    static FileInfo? RestorePin(FileInfo retired)
    {
        var restored = Path.Combine(retired.DirectoryName!, DeadPinSuffix.Replace(retired.Name, ""));
        try
        {
            File.Move(retired.FullName, restored);
            return new FileInfo(restored);
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException)
        {
            if (File.Exists(restored)) DeleteQuietly(retired.FullName);
            return null;
        }
    }

    /// <summary>
    /// Deletes a pin that no longer protects its entry. The pin is renamed to a name no pin pattern matches,
    /// and its age and liveness are read again from the renamed file; a pin that was renewed meanwhile is
    /// renamed back, and one that cannot be renamed is left where it is. True when the pin is gone. A pass that
    /// has reached its limit retires no pin.
    /// </summary>
    static bool RetirePin(FileInfo pin, string key, TimeSpan retention, DateTime deadline, PassReport report)
    {
        if (PassStopped(deadline, report)) return false;
        beforePinRetired(pin.FullName);
        var aside = pin.FullName + ".dead-" + Guid.NewGuid().ToString("N");
        try { File.Move(pin.FullName, aside); }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return false; }
        if (!PinLive(new FileInfo(aside), key, retention, DateTime.UtcNow, deadline, report))
        {
            DeleteQuietly(aside);
            return true;
        }
        // A pin written since takes the name, and then the old one is redundant.
        for (var attempt = 0; attempt < 20; attempt++)
        {
            try { File.Move(aside, pin.FullName); return false; }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException)
            {
                if (File.Exists(pin.FullName)) { DeleteQuietly(aside); return false; }
                Thread.Sleep(25);
            }
        }
        return false;
    }

    /// <summary>
    /// Removes the directories directly under `root` that were not used for a long time: an entry (a name
    /// `entries` matches) unused for `retention`; with `limit`, the least recently used entries beyond it that
    /// were not used within a day; and staging (a name `staging` matches) abandoned for a day. Other names,
    /// reparse points and `protectedName` are never touched. Each directory is renamed to a dotted name,
    /// which readers skip, before it is deleted.
    /// With `library`, which is for the certified library cache, an entry is also removed only if it holds
    /// the files a publisher writes, and never while an editor package pinned to it still requires it or any
    /// process holds its use lock, which a reader takes before it validates the entry. The lock is taken
    /// exclusively without waiting, so the pass skips an entry in use on every platform. The lock files stay,
    /// since a lock on a deleted file excludes nothing; the closure records and pins of a removed entry go
    /// with it, and so do download archives and unfinished pins a killed publisher left for a day. A pin
    /// that a pass set aside and did not finish with is put back and judged again.
    /// `removing` is told how many directories are chosen, before the first is deleted, when there are any.
    /// With `library` the pass stops choosing, reading and removing once <see cref="passLimit"/> has passed
    /// or a lakefile read has waited out the rest of it, and a lakefile outside the cache is waited for at most
    /// <see cref="packageReadLimit"/>. A pin whose lakefile was not read, for either reason, keeps its entry,
    /// so once the pass has reached its limit it removes no pin, entry or closure record; a deletion under way
    /// finishes. `report` says what happened. Reads each directory's name and write time once. Returns the
    /// names of the directories removed.
    /// </summary>
    static List<string> EvictUnused(string root, Regex entries, Regex staging, TimeSpan retention, int? limit = null,
        string? protectedName = null, Action<int>? removing = null, bool library = false,
        PassReport? report = null)
    {
        var now = DateTime.UtcNow;
        var deadline = passClock() + passLimit;
        report ??= new PassReport();
        var items = new DirectoryInfo(root).EnumerateFileSystemInfos().ToList();
        var restoredPins = new List<FileInfo>();
        if (library)
        {
            foreach (var file in items.OfType<FileInfo>().Where(file => LibraryStagingFile.IsMatch(file.Name) &&
                         now - file.LastWriteTimeUtc > AbandonedAfter))
                DeleteQuietly(file.FullName);
            // A pin set aside by a pass that did not finish is judged again, by this pass's rules, at any age.
            foreach (var file in items.OfType<FileInfo>().Where(file => RetiredPin.IsMatch(file.Name)))
                if (RestorePin(file) is { } restored) restoredPins.Add(restored);
        }
        var sidecars = items.OfType<FileInfo>().Where(file => library && LibrarySidecar.IsMatch(file.Name))
            .Concat(restoredPins).ToList();
        var pins = sidecars.Where(file => file.Name.Contains(".pin-", StringComparison.Ordinal))
            .ToLookup(file => file.Name[..64], StringComparer.Ordinal);
        var directories = items.OfType<DirectoryInfo>().ToList();
        var doomed = new List<(DirectoryInfo Directory, TimeSpan Unused)>();
        var kept = new List<DirectoryInfo>();
        var reserved = 0;
        foreach (var entry in directories)
        {
            if (entry.Name == protectedName) { reserved++; continue; }
            if (entry.Attributes.HasFlag(FileAttributes.ReparsePoint)) continue;
            var isEntry = entries.IsMatch(entry.Name);
            if (isEntry && library && !HoldsReceipt(entry)) continue;
            if (isEntry && library && PinnedByPackage(entry, pins[entry.Name], retention, deadline, report))
            {
                reserved++;
                continue;
            }
            var age = now - entry.LastWriteTimeUtc;
            if (staging.IsMatch(entry.Name) && age > AbandonedAfter) doomed.Add((entry, AbandonedAfter));
            else if (isEntry && age > retention) doomed.Add((entry, retention));
            else if (isEntry) kept.Add(entry);
        }
        if (limit is { } most)
            doomed.AddRange(kept.OrderByDescending(entry => entry.LastWriteTimeUtc)
                .Skip(Math.Max(0, most - reserved))
                .Where(entry => now - entry.LastWriteTimeUtc > RecentUse).Select(entry => (entry, RecentUse)));
        if (doomed.Count > 0) removing?.Invoke(doomed.Count);
        var removed = new List<string>();
        foreach (var (entry, unused) in doomed)
        {
            if (library && PassStopped(deadline, report)) break;
            if (!Evict(entry, library && entries.IsMatch(entry.Name), unused)) continue;
            removed.Add(entry.Name);
            report.Removed++;
        }
        if (library && !PassStopped(deadline, report))
            RemoveSidecars(sidecars, directories.Select(entry => entry.Name).ToHashSet(), removed, retention,
                deadline, report);
        return removed;
    }

    /// <summary>
    /// Whether a library pass has reached its limit, by the clock or by a read that waited out the rest of it.
    /// Once true it stays true for the pass, and `report` says so.
    /// </summary>
    static bool PassStopped(DateTime deadline, PassReport report)
    {
        if (!report.GaveUp && passClock() > deadline) report.GaveUp = true;
        return report.GaveUp;
    }

    /// <summary>Whether a package still requires `entry` by path; pins of packages that do not are retired.</summary>
    static bool PinnedByPackage(DirectoryInfo entry, IEnumerable<FileInfo> pins, TimeSpan retention,
        DateTime deadline, PassReport report)
    {
        var live = false;
        foreach (var pin in pins)
            if (PinLive(pin, entry.Name, retention, DateTime.UtcNow, deadline, report) ||
                !RetirePin(pin, entry.Name, retention, deadline, report))
                live = true;
        return live;
    }

    /// <summary>
    /// Renames `entry` away and deletes it, unless it was used since it was chosen or, when `locked`, a
    /// process holds its use lock; false then, and when the entry cannot be renamed or deleted.
    /// </summary>
    static bool Evict(DirectoryInfo entry, bool locked, TimeSpan unused)
    {
        FileStream? hold = null;
        try
        {
            if (locked && (hold = HoldEntryExclusively(entry.FullName)) is null) return false;
            // A reader records its use after taking the lock, so the write time is current once the lock is ours.
            entry.Refresh();
            if (entry.Attributes.HasFlag(FileAttributes.ReparsePoint) ||
                DateTime.UtcNow - entry.LastWriteTimeUtc <= unused)
                return false;
            var target = entry.Name.Contains('.') ? entry.FullName : MoveAside(entry.FullName);
            hold?.Dispose();
            hold = null;
            Directory.Delete(target, true);
            return true;
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return false; }
        finally { hold?.Dispose(); }
    }

    /// <summary>
    /// Deletes the pins of removed entries and the closure records that name an entry that is absent or was
    /// removed. A pin renewed since the pass listed it stays. The `.use` and `.lock` files stay: a lock on a
    /// file that was deleted excludes nothing, because the next process locks a new file of the same name.
    /// Nothing is deleted once the pass has reached its limit.
    /// </summary>
    static void RemoveSidecars(List<FileInfo> sidecars, HashSet<string> present, List<string> removed,
        TimeSpan retention, DateTime deadline, PassReport report)
    {
        var gone = removed.ToHashSet(StringComparer.Ordinal);
        foreach (var file in sidecars)
        {
            if (PassStopped(deadline, report)) return;
            var match = LibrarySidecar.Match(file.Name);
            var key = match.Groups["key"].Value;
            if (match.Groups["kind"].Value == "closure")
            {
                if (ClosureNamesGone(file, present, gone)) DeleteQuietly(file.FullName);
            }
            else if (gone.Contains(key)) RetirePin(file, key, retention, deadline, report);
        }
    }

    /// <summary>Whether the closure record `file` names an entry that was removed or is not there.</summary>
    static bool ClosureNamesGone(FileInfo file, HashSet<string> present, HashSet<string> gone)
    {
        try
        {
            var named = File.ReadAllText(file.FullName).Trim();
            return gone.Contains(named) || !present.Contains(named);
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return false; }
    }

    // Once per process, removes support generations unused for the retention period and staging
    // left by killed publishers. Only exact cache entry names directly under the root are touched.
    static void EvictStaleSupport()
    {
        if (Interlocked.Exchange(ref supportEvicted, 1) != 0) return;
        EvictUnused(SuccessCacheRoot, SupportGeneration, AbandonedStaging, SupportRetention);
    }

    /// <summary>
    /// Once per process, after this process published a library entry: removes certified library entries
    /// that were not used for the retention period or fall beyond the entry limit, and staging left by killed
    /// publishers, as a stage on stderr: START names how many directories it chose, and END how many it
    /// removed, with the reason when it stopped early. `current` is the entry this process uses and is never
    /// removed. Nothing the pass raises reaches the caller, whose verification has already published its
    /// library; the failure is reported on the END line instead, with exit 1.
    /// </summary>
    static void EvictUnusedLibraries(string cacheRoot, string current)
    {
        if (Interlocked.Exchange(ref libraryEvicted, 1) != 0) return;
        var elapsed = Stopwatch.StartNew();
        string? stage = null;
        var report = new PassReport();
        try
        {
            EvictUnused(cacheRoot, KeyName, LibraryStaging, LibraryRetention, LibraryEntryLimit, current,
                count =>
                {
                    stage = $"Removing up to {count} unused certified library cache " +
                        (count == 1 ? "directory" : "directories");
                    Console.Error.WriteLine("START " + stage);
                }, library: true, report: report);
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            report.Failure = (error.GetType().Name + ": " + error.Message).ReplaceLineEndings(" ");
        }
        if (stage is null && report.Failure is null && !report.GaveUp && report.Unjudged == 0) return;
        if (stage is null)
        {
            stage = "Removing unused certified library cache directories";
            Console.Error.WriteLine("START " + stage);
        }
        Console.Error.WriteLine($"END {stage}: removed {report.Removed}" +
            (report.GaveUp ? $", stopped at the {passLimit.TotalSeconds:F0}s limit" : "") +
            (report.Unjudged > 0 ? $", {report.Unjudged} lakefiles not read in time" : "") +
            (report.Failure is null ? "" : ", stopped by " + report.Failure) +
            $" (exit {(report.Failure is null ? 0 : 1)}, {elapsed.Elapsed.TotalSeconds:F1}s)");
    }

    (string Key, SortedDictionary<string, string> Sources) LibraryIdentity(SortedDictionary<string, string> common)
    {
        var sources = LibrarySources(common);
        // Include the resolved toolchain, platform and cache format, not the selected proof.
        var toolchain = Toolchain;
        var compiler = Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean");
        var checker = Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
        return (ContentKey("leancil-library-v5-all-modules-kernel-replayed\n" + RuntimeInformation.RuntimeIdentifier +
            "\n" + Sha(checker) + "\n" + Sha(compiler) + "\n" + JsonSerializer.Serialize(sources)), sources);
    }

    /// <summary>
    /// The writable session package for this process: it requires the certified library in place
    /// as a path dependency, so support and proof builds write only their own modules. A caller
    /// that writes into the library itself passes <paramref name="writes"/> and gets a private copy.
    /// </summary>
    string Library(SortedDictionary<string, string> snapshot, bool writes = false,
        IReadOnlyCollection<string>? closureRoots = null)
    {
        var common = new SortedDictionary<string, string>(snapshot.Where(p =>
            !p.Key.StartsWith("proof:", StringComparison.Ordinal) && !p.Key.StartsWith("settings:", StringComparison.Ordinal)).ToDictionary(), StringComparer.Ordinal);
        if (session is not null)
        {
            if (!Same(common, libraryInputs!))
                throw new InvalidOperationException("Proof session source inputs changed");
            return session;
        }

        (libraryKey, var sources) = LibraryIdentity(common);
        fullLibraryKey = libraryKey;
        static bool Set(string variable) => string.Equals(Environment.GetEnvironmentVariable(variable), "true",
            StringComparison.OrdinalIgnoreCase);
        var fresh = freshLibrary || !editorLibrary && (Set("CI") || Set("GITHUB_ACTIONS"));
        var cacheRoot = LibraryCacheRoot;
        var cached = Path.Combine(cacheRoot, libraryKey);
        var publishedEntry = false;
        SortedDictionary<string, string> manifest;
        FileStream? cacheLock = null;
        try
        {
            if (!fresh)
            {
                Directory.CreateDirectory(cacheRoot);
                // Serialize same-key builders. A lock is released even after a crashed process, and a build
                // may outlast any fixed wait, so a waiter waits for as long as the lock file is held.
                var waiting = Stopwatch.StartNew();
                var announced = false;
                while (cacheLock is null)
                {
                    try { cacheLock = new FileStream(cached + ".lock", FileMode.OpenOrCreate, FileAccess.ReadWrite, FileShare.None); }
                    catch (IOException) when (File.Exists(cached + ".lock"))
                    {
                        if (!announced && waiting.Elapsed > TimeSpan.FromSeconds(10))
                        {
                            announced = true;
                            Console.Error.WriteLine("Waiting for another leancil process that is building or " +
                                "opening the certified library in " + cacheRoot + ".");
                        }
                        Thread.Sleep(100);
                    }
                }
            }
            var supplied = Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY");
            var suppliedDigest = Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY_SHA256");
            // Held, and recorded as used, before the entry is validated, so no pass removes it meanwhile.
            if (!fresh && string.IsNullOrWhiteSpace(supplied))
            {
                UseEntry(cached);
            }
            // Every branch that opens a certified library without building it traces the open, timed from here.
            var openStarted = DateTimeOffset.UtcNow;
            var openElapsed = Stopwatch.StartNew();
            void TraceOpen() => Trace("Opening certified Lean verification library", openStarted, library,
                openElapsed.Elapsed, 0, "", [library]);
            // A supplied certified library is not a local cache, so --rebuild-library still uses it.
            if (!string.IsNullOrWhiteSpace(supplied))
            {
                library = Path.GetFullPath(supplied);
                manifest = SuppliedLibraryManifest(library, suppliedDigest, libraryKey, sources)
                    ?? throw new InvalidOperationException("Certified library identity or integrity mismatch");
                certifiedFingerprintsSha = manifest.GetValueOrDefault(CertifiedFingerprintsName);
                libraryBuild = "certified-artifact";
                TraceOpen();
            }
            else if (!fresh && CertifiedLocalLibrary(cached, libraryKey) &&
                ReadManifest(cached) is { } cachedManifest && Same(sources, LibrarySources(cachedManifest)) &&
                (libraryStamps = HashedCacheEntry(cached, cachedManifest)) is not null)
            {
                // The receipt binds this manifest, and the entry's files still hash to it.
                RemoveClosure(cacheRoot, libraryKey);
                library = cached;
                manifest = cachedManifest;
                libraryBuild = "cache";
                TraceOpen();
            }
            else if (!fresh && DownloadReleasedLibrary(cached, libraryKey))
            {
                publishedEntry = true;
                library = cached;
                manifest = ReadManifest(cached) ?? throw new InvalidDataException("Missing downloaded library manifest");
                libraryBuild = "release";
                TraceOpen();
            }
            else if (!fresh && closureRoots is not null &&
                ClosureLibrary(cacheRoot, libraryKey, sources, closureRoots) is { } closure)
            {
                // The certificate names the closure's own key, which states exactly the modules replayed.
                (library, manifest, libraryKey, libraryModules) =
                    (closure.Directory, closure.Manifest, closure.Key, closure.Modules);
                libraryStamps = closure.Stamps;
                libraryBuild = closure.Built ? "closure" : "closure-cache";
                publishedEntry = closure.Built;
                if (!closure.Built) TraceOpen();
            }
            else
            {
                library = Path.Combine(Path.GetTempPath(), "leancil-library-" + Guid.NewGuid().ToString("N"));
                ownsLibrary = true;
                Directory.CreateDirectory(library);
                if (incrementalLibrary is not null)
                {
                    // A donor that is a cache entry is held and recorded as used while it is copied.
                    var donorInCache = IsEntryOf(cacheRoot, incrementalLibrary);
                    using var donorUse = donorInCache ? HoldEntry(incrementalLibrary) : null;
                    if (donorInCache) TouchEntry(incrementalLibrary);
                    StageIncrementalLibrary(library, incrementalLibrary, incrementalDigest, sources);
                }
                // Lake reuses a closure entry's modules by trace; every module is replayed below all the same.
                else if (!fresh && CachedClosure(cacheRoot, libraryKey, sources) is { } built)
                {
                    // Held and recorded as used before the copy; an entry removed since it was validated is no seed.
                    using var seedUse = HoldEntry(built);
                    if (Directory.Exists(built))
                    {
                        TouchEntry(built);
                        CopyTree(Path.Combine(built, ".lake", "build"), Path.Combine(library, ".lake", "build"));
                    }
                }
                foreach (var (name, hash) in sources)
                {
                    var destination = Path.Combine(library, name);
                    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                    CopyLibrarySource(name, destination);
                    if (Sha(destination) != hash)
                        throw new InvalidOperationException("Library source changed while copying: " + name);
                }
                // Modules no root imports are built here too, so importing one never builds into a shared library.
                var sourceModules = sources.Keys.Where(name => IsCertifiedLibrarySource(name) &&
                    name.EndsWith(".lean", StringComparison.Ordinal)).Select(name => "+" + name[..^".lean".Length].Replace('/', '.'));
                LogLibraryBuildNotice(cached, fresh);
                Run(["lake", "build", .. CertifiedLibraryRoots, "leancil-audit", .. sourceModules], library, streamOutput: true,
                    progress: "Building fresh Lean verification library");
                // An incremental build replays donor modules too: an unchanged olean may import changed ones.
                ReplayLibrary(library, (incrementalLibrary is null ? "fresh" : "incremental") +
                    " Lean verification library");
                if (!Same(sources, CommonInputs(libraryOnly: true)))
                    throw new InvalidDataException("Library sources changed during preparation");
                libraryBuild = incrementalLibrary is null ? "fresh" : "incremental";
                manifest = CacheFiles(library);
                if (!fresh)
                {
                    File.WriteAllText(Path.Combine(library, "cache-manifest.json"), JsonSerializer.Serialize(manifest, Json));
                    File.WriteAllBytes(Path.Combine(library, "cache-receipt.hmac"), HMACSHA256.HashData(ReceiptKey,
                        Encoding.UTF8.GetBytes(libraryKey).Concat(File.ReadAllBytes(Path.Combine(library, "cache-manifest.json"))).ToArray()));
                    var staging = cached + "." + Guid.NewGuid().ToString("N");
                    try
                    {
                        CopyTree(library, staging);
                        PublishEntry(staging, cached);
                        publishedLibrary = cached;
                        publishedEntry = true;
                        RemoveClosure(cacheRoot, libraryKey);
                    }
                    finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
                    // Consumer cache keys bind the library directory: read the entry later runs open, unless
                    // this run writes into the library, which only its private build allows.
                    if (!writes)
                    {
                        libraryStamps = HashedCacheEntry(cached, manifest)
                            ?? throw new InvalidOperationException("Certified cache changed while copying");
                        Directory.Delete(library, true);
                        library = cached;
                        ownsLibrary = false;
                    }
                }
            }
        }
        finally { cacheLock?.Dispose(); }
        // Only a publication evicts, so opening a cached entry reads no other entry, and it runs after
        // the key's lock is released so that a waiter is not held up by deleting other entries.
        if (publishedEntry) EvictUnusedLibraries(cacheRoot, libraryKey!);
        // Lake compiles a dependency's missing modules into its own build directory, so a library
        // extended with uncompiled sources is read from a private copy; a complete one is never written.
        var incomplete = manifest.Keys.Any(name => IsCertifiedLibrarySource(name) &&
            name.EndsWith(".lean", StringComparison.Ordinal) &&
            !manifest.ContainsKey(CompiledLibraryPrefix + name[..^".lean".Length] + ".olean"));
        if (!ownsLibrary && (incomplete || writes))
        {
            var started = DateTimeOffset.UtcNow;
            var elapsed = Stopwatch.StartNew();
            var copy = Path.Combine(Path.GetTempPath(), "leancil-library-" + Guid.NewGuid().ToString("N"));
            CopyTree(library, copy);
            library = copy;
            ownsLibrary = true;
            Trace(incomplete ? "Copying incomplete certified Lean verification library" : "Copying certified Lean verification library",
                started, copy, elapsed.Elapsed, 0, "", [copy]);
        }
        RequireLakeReadable(library, manifest.Keys);
        // Lake rebuilds a module it finds stale into the library; no build of this process may have done so.
        libraryStamps = ownsLibrary ? null : libraryStamps ?? FileStamps(library);
        libraryManifest = new(manifest, StringComparer.Ordinal);
        baseModules = new(manifest.Where(pair =>
                pair.Key.StartsWith(CompiledLibraryPrefix, StringComparison.Ordinal) &&
                Path.GetFileName(pair.Key).Contains(".olean", StringComparison.Ordinal))
            .ToDictionary(pair => pair.Key[CompiledLibraryPrefix.Length..], pair => pair.Value),
            StringComparer.Ordinal);
        certifiedModules = new(baseModules, StringComparer.Ordinal);
        libraryInputs = common;
        auditExecutable = Path.Combine(library, ".lake/build/bin", OperatingSystem.IsWindows() ? "leancil-audit.exe" : "leancil-audit");
        auditExecutableSha = manifest.GetValueOrDefault(Path.GetRelativePath(library, auditExecutable).Replace('\\', '/'));
        // Workflow artifacts drop the mode bits that the cache manifest does not cover.
        if (!OperatingSystem.IsWindows() && auditExecutableSha is not null &&
            !File.GetUnixFileMode(auditExecutable).HasFlag(UnixFileMode.UserExecute))
            File.SetUnixFileMode(auditExecutable, File.GetUnixFileMode(auditExecutable) | UnixFileMode.UserExecute);
        session = CreateSession(library, common.Keys.Where(name =>
            name.EndsWith(".lean", StringComparison.Ordinal) && !sources.ContainsKey(name)));
        return session;
    }

    /// <summary>A certified cache entry that holds only `Modules`, under the `Key` that names them.</summary>
    sealed record ClosureEntry(string Directory, string Key, string[] Modules,
        SortedDictionary<string, string> Manifest, SortedDictionary<string, string> Stamps, bool Built);

    /// <summary>Whether `module` is a framework module: the `CIL` aggregate or a module below it.</summary>
    static bool IsFrameworkModule(string module) =>
        module == "CIL" || module.StartsWith("CIL.", StringComparison.Ordinal);

    /// <summary>The build configuration every library entry holds beside its sources.</summary>
    static readonly string[] LibraryConfiguration = ["lakefile.toml", "lake-manifest.json", "lean-toolchain"];

    /// <summary>The module that the audit executable is built from; every library entry holds its imports.</summary>
    const string AuditModule = "CIL.OleanAudit";

    /// <summary>The directory of a library that holds its compiled modules, their companions and hashes.</summary>
    const string CompiledLibraryPrefix = ".lake/build/lib/lean/";

    /// <summary>
    /// The longest full path of a compiled library file that Lake reads on Windows; it reports a longer one as a
    /// missing file, so no package builds against a library holding one.
    /// </summary>
    const int LakePathLimit = 259;

    /// <summary>
    /// Refuses, on Windows, a library holding a compiled file whose full path is longer than Lake reads, naming
    /// the file, since every package that requires the library would fail on it.
    /// </summary>
    static void RequireLakeReadable(string library, IEnumerable<string> files)
    {
        if (!OperatingSystem.IsWindows()) return;
        var longest = files.Where(name => name.StartsWith(CompiledLibraryPrefix, StringComparison.Ordinal))
            .MaxBy(name => name.Length);
        var length = longest is null ? 0 : Path.Combine(library, longest).Length;
        if (length > LakePathLimit)
            throw new InvalidOperationException($"The certified library {library} cannot be read by Lake on " +
                $"Windows: its file {longest} makes a path of {length} characters and Lake reads at most " +
                $"{LakePathLimit}. Use a library cache directory (LEANCIL_CACHE_DIR) or supplied library " +
                $"(LEANCIL_CERTIFIED_LIBRARY) whose path is at least {length - LakePathLimit} characters shorter.");
    }

    // Resolve source roots through Lake so library and package srcDir settings agree with imports.
    internal static string[] ConsumerSourceDirectories(string session, IEnumerable<string> packageRoots)
    {
        var lines = Run(["lake", "env"], session).Split('\n', StringSplitOptions.TrimEntries)
            .Where(line => line.StartsWith("LEAN_SRC_PATH=", StringComparison.Ordinal)).ToArray();
        if (lines.Length != 1) throw new InvalidDataException("Could not resolve consumer Lean source paths.");
        return lines[0]["LEAN_SRC_PATH=".Length..]
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(path => Path.GetFullPath(path, session)).Concat(packageRoots).Distinct().ToArray();
    }

    static string ModuleSource(string module) => module.Replace('.', '/') + ".lean";

    /// <summary>
    /// The framework modules that `roots` and the audit executable import, transitively, in order; null when
    /// one of them is not a framework source, or when they include the `CIL` aggregate and so every module.
    /// </summary>
    static string[]? ImportClosure(SortedDictionary<string, string> sources, IEnumerable<string> roots,
        Func<string, string> read)
    {
        var closure = new SortedSet<string>(StringComparer.Ordinal);
        var pending = new Queue<string>(roots.Where(IsFrameworkModule).Append(AuditModule));
        while (pending.TryDequeue(out var module))
        {
            if (!closure.Add(module)) continue;
            if (module == "CIL" || !sources.ContainsKey(ModuleSource(module))) return null;
            foreach (Match import in SourceImport.Matches(read(ModuleSource(module))))
                if (IsFrameworkModule(import.Groups[1].Value)) pending.Enqueue(import.Groups[1].Value);
        }
        return [.. closure];
    }

    /// <summary>The key of the closure entry of the library `libraryKey` that holds exactly `modules`.</summary>
    static string ClosureKey(string libraryKey, string[] modules) => ContentKey(
        "leancil-library-closure-v1-these-modules-kernel-replayed\n" + libraryKey + "\n" + string.Join("\n", modules));

    /// <summary>The closure key recorded beside the library cache entry before the full closure is built.</summary>
    static string ClosureRecord(string cacheRoot, string libraryKey) =>
        Path.Combine(cacheRoot, libraryKey + ".closure");

    /// <summary>
    /// Whether `manifest` describes a closure entry of exactly `modules`: their sources and the build
    /// configuration as in `sources`, no other framework source, and compiled modules for those and no other.
    /// </summary>
    static bool ClosureManifest(SortedDictionary<string, string> manifest, SortedDictionary<string, string> sources,
        string[] modules)
    {
        var expected = modules.Select(ModuleSource).Concat(LibraryConfiguration).ToHashSet(StringComparer.Ordinal);
        var compiled = manifest.Keys.Where(name => name.StartsWith(CompiledLibraryPrefix, StringComparison.Ordinal) &&
                Path.GetFileName(name).Contains(".olean", StringComparison.Ordinal))
            .Select(name => ModuleName(name[CompiledLibraryPrefix.Length..])).ToHashSet(StringComparer.Ordinal);
        return expected.SetEquals(LibrarySources(manifest).Keys) && compiled.SetEquals(modules) &&
            expected.All(name => sources.TryGetValue(name, out var hash) && manifest[name] == hash);
    }

    /// <summary>
    /// The directory of the closure entry recorded for the library `libraryKey`, when it is one: the record
    /// is not authenticated, so the entry's own modules must give the recorded key, its sources must be those
    /// in `sources`, and its receipt and files must authenticate it. Null otherwise.
    /// </summary>
    string? CachedClosure(string cacheRoot, string libraryKey, SortedDictionary<string, string> sources)
    {
        try
        {
            var key = File.ReadAllText(ClosureRecord(cacheRoot, libraryKey)).Trim();
            var directory = Path.Combine(cacheRoot, key);
            if (!KeyName.IsMatch(key) || !CertifiedLocalLibrary(directory, key) ||
                ReadManifest(directory) is not { } manifest) return null;
            const string extension = ".lean";
            string[] modules = [.. LibrarySources(manifest).Keys
                .Where(name => name.EndsWith(extension, StringComparison.Ordinal))
                .Select(name => name[..^extension.Length].Replace('/', '.')).Order(StringComparer.Ordinal)];
            return ClosureKey(libraryKey, modules) == key && ClosureManifest(manifest, sources, modules) &&
                HashedCacheEntry(directory, manifest) is not null ? directory : null;
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return null; }
    }

    /// <summary>
    /// Removes the closure entry recorded for a library whose whole entry is published, unless a process still
    /// reads it; a later run then removes it. The entry is renamed away before its record goes, so a failure
    /// leaves either both or neither.
    /// </summary>
    static void RemoveClosure(string cacheRoot, string libraryKey)
    {
        try
        {
            var record = ClosureRecord(cacheRoot, libraryKey);
            if (!File.Exists(record)) return;
            var key = File.ReadAllText(record).Trim();
            var directory = Path.Combine(cacheRoot, key);
            if (KeyName.IsMatch(key) && Directory.Exists(directory) && HoldsReceipt(new DirectoryInfo(directory)))
            {
                string doomed;
                using (var hold = HoldEntryExclusively(directory))
                {
                    if (hold is null) return;
                    doomed = MoveAside(directory);
                }
                File.Delete(record);
                Directory.Delete(doomed, true);
            }
            else File.Delete(record);
        }
        // A reader holds the entry, or its files; the whole library is preferred from now on regardless.
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
    }
    /// <summary>
    /// A certified entry holding only the import closure of `roots`: its sources, their compiled modules, each
    /// kernel-replayed, and the audit executable. Its key and receipt name exactly those modules, and it holds
    /// no source without a compiled module, so neither Lean nor Lake can take any other module from it. Null
    /// when the closure is the whole library, or when another closure of this library was built: the whole
    /// library is built then.
    /// </summary>
    ClosureEntry? ClosureLibrary(string cacheRoot, string libraryKey, SortedDictionary<string, string> sources,
        IReadOnlyCollection<string> roots)
    {
        if (ImportClosure(sources, roots, name => File.ReadAllText(At(name))) is not { } modules) return null;
        var key = ClosureKey(libraryKey, modules);
        var record = ClosureRecord(cacheRoot, libraryKey);
        var directory = Path.Combine(cacheRoot, key);
        var held = false;
        if (File.Exists(record))
        {
            if (File.ReadAllText(record).Trim() != key) return null;
            // Held, and recorded as used, before the entry is validated, so no pass removes it meanwhile.
            UseEntry(directory);
            held = true;
            if (CertifiedLocalLibrary(directory, key) && ReadManifest(directory) is { } cached &&
                ClosureManifest(cached, sources, modules) && HashedCacheEntry(directory, cached) is { } stamps)
                return new(directory, key, modules, cached, stamps, Built: false);
        }
        var build = Path.Combine(Path.GetTempPath(), "leancil-library-" + Guid.NewGuid().ToString("N"));
        var staging = directory + "." + Guid.NewGuid().ToString("N");
        try
        {
            foreach (var name in modules.Select(ModuleSource).Concat(LibraryConfiguration))
            {
                var destination = Path.Combine(build, name);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                CopyLibrarySource(name, destination);
                if (Sha(destination) != sources[name])
                    throw new InvalidOperationException("Library source changed while copying: " + name);
            }
            Console.Error.WriteLine($"Building and kernel-replaying the {modules.Length} framework modules this " +
                "proof imports. The whole certified library is built after a verified result is reported.");
            Run(["lake", "build", "leancil-audit", .. modules.Select(module => "+" + module)], build,
                streamOutput: true, progress: "Building the framework modules the proof imports");
            if (!ModuleArtifacts(build).Keys.Select(ModuleName).ToHashSet(StringComparer.Ordinal).SetEquals(modules))
                throw new InvalidOperationException("Lake built other modules than the import closure it was given.");
            ReplayLibrary(build, "the framework modules the proof imports");
            var manifest = CacheFiles(build);
            if (!ClosureManifest(manifest, CommonInputs(libraryOnly: true), modules))
                throw new InvalidDataException("Library sources changed during preparation");
            File.WriteAllText(Path.Combine(build, "cache-manifest.json"), JsonSerializer.Serialize(manifest, Json));
            var manifestBytes = File.ReadAllBytes(Path.Combine(build, "cache-manifest.json"));
            File.WriteAllBytes(Path.Combine(build, "cache-receipt.hmac"), HMACSHA256.HashData(ReceiptKey,
                Encoding.UTF8.GetBytes(key).Concat(manifestBytes).ToArray()));
            CopyTree(build, staging);
            PublishEntry(staging, directory);
            if (!held) UseEntry(directory);
            File.WriteAllText(record, key);
            // The published copy, not the build, is what the session reads.
            var published = HashedCacheEntry(directory, manifest)
                ?? throw new InvalidOperationException("Certified cache changed while copying");
            return new(directory, key, modules, manifest, published, Built: true);
        }
        finally
        {
            if (Directory.Exists(staging)) Directory.Delete(staging, true);
            if (Directory.Exists(build)) Directory.Delete(build, true);
        }
    }

    /// <summary>The modules each compiled module in `modules`, by path, imports directly.</summary>
    Dictionary<string, string[]> ConsumerModuleImports(string session, Dictionary<string, string> modules)
    {
        // Read Lean's compiled import headers, not a regex over source text. This
        // also handles public/private imports and transitive package dependencies.
        var input = Path.Combine(Path.GetTempPath(), "leancil-imports-" + Guid.NewGuid().ToString("N") + ".json");
        var output = Path.ChangeExtension(input, ".result.json");
        try
        {
            var paths = modules.Values.ToArray();
            File.WriteAllText(input, JsonSerializer.Serialize(paths));
            Run([CheckedAuditExecutable(), "--imports", input, output], session, environment: LeanEnvironment);
            var imports = File.ReadAllLines(output).Select(line => JsonSerializer.Deserialize<string[]>(line)).ToArray();
            if (imports.Length != paths.Length || imports.Any(items => items is null))
                throw new InvalidDataException("Incomplete consumer compiled import graph.");
            return modules.Keys.Zip(imports).ToDictionary(pair => pair.First, pair => pair.Second!);
        }
        finally { File.Delete(input); File.Delete(output); }
    }

    /// <summary>
    /// Fails unless every framework module that a module compiled below `directory` imports, by its compiled
    /// import header, is one the open closure entry holds. Source text is not consulted: Lean accepts import
    /// spellings a pattern over it misses, and a module's absence from the entry is not what refuses it.
    /// </summary>
    void RequireReplayedImports(string directory, string session)
    {
        if (libraryModules is null) return;
        var compiled = Directory.EnumerateFiles(directory, "*.olean", SearchOption.AllDirectories)
            .ToDictionary(path => path, path => path, StringComparer.Ordinal);
        RequireReplayedImports(ConsumerModuleImports(session, compiled).Values.SelectMany(imports => imports));
    }

    /// <summary>
    /// Fails unless each framework module in `imports` is one the open closure entry holds, and so one that
    /// was kernel-replayed under the key the certificate names. The whole library holds every module.
    /// </summary>
    void RequireReplayedImports(IEnumerable<string> imports)
    {
        if (libraryModules is null) return;
        foreach (var module in imports.Where(IsFrameworkModule))
            if (!libraryModules.Contains(module, StringComparer.Ordinal) ||
                !baseModules!.ContainsKey(module.Replace('.', '/') + ".olean"))
                throw new InvalidOperationException("The proof imports " + module + ", which the certified library " +
                    "entry " + libraryKey + " does not hold: it was not kernel-replayed under that key.");
    }

    /// <summary>
    /// The manifest of a supplied certified library, or null when its manifest digest, key or source
    /// binding disagrees. The producer hashed every file into that manifest; the files are not rehashed.
    /// </summary>
    static SortedDictionary<string, string>? SuppliedLibraryManifest(string directory, string? trustedDigest, string key,
        SortedDictionary<string, string> sources)
    {
        if (string.IsNullOrWhiteSpace(trustedDigest)) return null;
        try
        {
            var bytes = File.ReadAllBytes(Path.Combine(directory, "cache-manifest.json"));
            if (Convert.ToHexStringLower(SHA256.HashData(bytes)) != trustedDigest ||
                File.ReadAllText(Path.Combine(directory, "library-key.txt")) != key) return null;
            var manifest = JsonSerializer.Deserialize<SortedDictionary<string, string>>(bytes);
            return manifest is not null && manifest.ContainsKey(".lake/build/lib/lean/CIL.olean") &&
                Same(sources, LibrarySources(manifest)) ? manifest : null;
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException) { return null; }
    }

    static SortedDictionary<string, string>? ReadManifest(string directory)
    {
        try
        {
            return JsonSerializer.Deserialize<SortedDictionary<string, string>>(
                File.ReadAllBytes(Path.Combine(directory, "cache-manifest.json")));
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException) { return null; }
    }

    /// <summary>
    /// A fresh package holding the given checkout sources and every library of the checkout lakefile outside
    /// the certified library, with the base as a read-only path dependency. Lake writes only below this package.
    /// </summary>
    static string CreateSession(string certified, IEnumerable<string> extraSources)
    {
        var directory = Path.Combine(Path.GetTempPath(), "leancil-session-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        // The certified lakefile omits test libraries, so only the checkout's can declare them.
        File.WriteAllText(Path.Combine(directory, "lakefile.toml"), "name = \"leancil-session\"\n" +
            FrameworkRequirement(directory, certified) + LibraryDeclarations(At("lakefile.toml")));
        File.Copy(Path.Combine(certified, "lean-toolchain"), Path.Combine(directory, "lean-toolchain"));
        foreach (var name in extraSources)
        {
            var destination = Path.Combine(directory, name);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(At(name), destination, true);
        }
        return directory;
    }

    /// <summary>
    /// The base library's module artifacts: recorded ones from the validated manifest, which must be the files
    /// the library was opened with, plus any unrecorded output, which must be replayed: Lake builds an
    /// unrecorded source into a library this process owns, and a library read in place may arrive with one.
    /// </summary>
    SortedDictionary<string, string> BaseModuleArtifacts()
    {
        RequireUnchangedLibrary();
        var result = new SortedDictionary<string, string>(baseModules!, StringComparer.Ordinal);
        var compiled = Path.Combine(library!, ".lake/build/lib/lean");
        foreach (var path in Directory.EnumerateFiles(compiled, "*", SearchOption.AllDirectories))
        {
            var name = Path.GetRelativePath(compiled, path).Replace('\\', '/');
            if (Path.GetFileName(name).Contains(".olean", StringComparison.Ordinal) && !result.ContainsKey(name))
                result[name] = Sha(path);
        }
        return result;
    }

    /// <summary>The module artifacts of a session: the base's and this session's own outputs.</summary>
    SortedDictionary<string, string> SessionModules(string directory)
    {
        var result = BaseModuleArtifacts();
        foreach (var (name, hash) in ModuleArtifacts(directory)) result[name] = hash;
        return result;
    }

    /// <summary>The Lean search path of a session: its own outputs before the certified base.</summary>
    string SessionLeanPath(string directory) =>
        Path.Combine(directory, ".lake/build/lib/lean") + Path.PathSeparator + Path.Combine(library!, ".lake/build/lib/lean");

    /// <summary>
    /// A package named leancil whose only libraries are <see cref="CertifiedLibraryRoots"/>, read in place from
    /// the certified library, so no other target of the certified lakefile can claim a requiring package's own
    /// modules.
    /// `requirements` are further lakefile tables, such as a package this one brings into the workspace.
    /// </summary>
    // Lake's module traces name the package, so under another name it rebuilds every module into the library.
    static string FrameworkPackage(string owner, string certified, string requirements = "", bool pin = false)
    {
        var directory = Path.Combine(owner, ".lake", "leancil-framework");
        Directory.CreateDirectory(directory);
        // A package that outlives this process keeps its cache entry from removal for as long as it requires it.
        if (pin) PinEntry(certified, directory);
        var root = Path.GetFullPath(certified).Replace('\\', '/');
        WriteIfChanged(Path.Combine(directory, "lakefile.toml"),
            $"name = \"leancil\"\nsrcDir = {JsonSerializer.Serialize(root)}\nbuildDir = " +
            $"{JsonSerializer.Serialize(root + "/.lake/build")}\n" +
            string.Concat(CertifiedLibraryRoots.Select(name => $"\n[[lean_lib]]\nname = \"{name}\"\n")) + requirements);
        WriteIfChanged(Path.Combine(directory, "lean-toolchain"), File.ReadAllText(Path.Combine(certified, "lean-toolchain")));
        return directory;
    }

    /// <summary>
    /// The certified library a package that outlives this process may require by path: the machine's cache
    /// entry, built and published first when absent, or a supplied library, either one with every file hashed
    /// against its manifest. No process deletes a supplied library, and a cache entry stays while a package
    /// that pinned it still requires it.
    /// </summary>
    static string EditorLibrary()
    {
        if (editorLibraryDirectory is not null) return editorLibraryDirectory;
        using var verification = new Program { editorLibrary = true };
        verification.Library(Inputs(At("CIL.lean")));
        // This process runs Lake against the entry for as long as it lives, so the locks outlive this instance.
        editorLibraryUses.AddRange(verification.entryUses);
        verification.entryUses.Clear();
        // A cache entry was hashed when it was opened; a supplied library is not, and Lake may write into either.
        if (!verification.ownsLibrary && verification.libraryBuild == "certified-artifact" &&
            (ReadManifest(verification.library!) is not { } manifest ||
                !Same(manifest, CacheFiles(verification.library!))))
            throw new InvalidOperationException("The files of the supplied certified library " +
                verification.library + " do not match its manifest, so an editor package cannot require it in place.");
        return editorLibraryDirectory = !verification.ownsLibrary ? verification.library!
            : verification.publishedLibrary ?? throw new InvalidOperationException(
                "The supplied certified library holds framework sources it has not compiled, so an editor " +
                "package cannot require it in place. Unset LEANCIL_CERTIFIED_LIBRARY to use this machine's " +
                "library cache.");
    }

    /// <summary>The directory <see cref="EditorLibrary"/> resolved, once per process.</summary>
    static string? editorLibraryDirectory;

    /// <summary>The use locks of the entry <see cref="EditorLibrary"/> resolved, held until the process ends.</summary>
    static readonly List<FileStream> editorLibraryUses = [];

    /// <summary>
    /// Runs `build` in a package that requires the certified library at `library` by path, and fails unless
    /// every file there hashes as it did before: Lake rebuilds a stale required module in place.
    /// </summary>
    static void RequireUnwritten(string library, Action build)
    {
        var files = CacheFiles(library);
        build();
        if (!Same(files, CacheFiles(library)))
            throw new InvalidOperationException("Lake wrote into the certified library " + library +
                ", which this package requires by path: it found framework modules out of date there. " +
                "A cache entry is rehashed, and replaced if it changed, by the next leancil verify or workspace; " +
                "a supplied library is rehashed, and refused if it changed, by the next leancil workspace.");
    }

    /// <summary>The lakefile requirement of a package below owner on the certified framework.</summary>
    // Relative, so equal sessions have equal configurations wherever their directories are.
    static string FrameworkRequirement(string owner, string certified, bool pin = false) =>
        "\n[[require]]\nname = \"leancil\"\npath = " + JsonSerializer.Serialize(
            Path.GetRelativePath(owner, FrameworkPackage(owner, certified, pin: pin)).Replace('\\', '/')) + "\n";

    /// <summary>Declarations of every library in a lakefile except the certified library roots and the editor's.</summary>
    static string LibraryDeclarations(string lakefile) => string.Concat(
        Regex.Matches(File.ReadAllText(lakefile), @"^\[\[lean_lib\]\]\r?\nname = ""([^""]+)""", RegexOptions.Multiline)
            .Select(match => match.Groups[1].Value)
            .Where(name => name != EditorLibraryName && !IsCertifiedLibraryModule(name))
            .Select(name => $"\n[[lean_lib]]\nname = \"{name}\"\n"));

    // Rewriting an unchanged configuration would make Lake reconfigure packages that later builds reuse.
    // Concurrent fixtures share the checkout package, so a reader sees the old or new file, never a partial one.
    static void WriteIfChanged(string path, string contents)
    {
        if (File.Exists(path) && File.ReadAllText(path) == contents) return;
        var staging = path + "." + Guid.NewGuid().ToString("N");
        File.WriteAllText(staging, contents);
        File.Move(staging, path, overwrite: true);
    }

    /// <summary>
    /// The package in which checkout tests build: its sources are the checkout's own and its CIL is
    /// the certified library, read in place, so neither the library nor the checkout gets a CIL build.
    /// </summary>
    string CheckoutPackage()
    {
        Library(Inputs(At("CIL.lean")));
        var directory = At(".lake/leancil-checkout");
        Directory.CreateDirectory(directory);
        WriteIfChanged(Path.Combine(directory, "lakefile.toml"), "name = \"leancil-checkout\"\nsrcDir = \"../..\"\n" +
            FrameworkRequirement(directory, library!) + LibraryDeclarations(At("lakefile.toml")));
        WriteIfChanged(Path.Combine(directory, "lean-toolchain"), File.ReadAllText(At("lean-toolchain")));
        return directory;
    }

    /// <summary>The Lean search path of checkout tests: their own outputs, then the certified library.</summary>
    string CheckoutLeanPath() => SessionLeanPath(CheckoutPackage());

    static Program? fixtureVerification;

    /// <summary>The checkout package for static test helpers, created once per process.</summary>
    static string FixturePackage()
    {
        if (fixtureVerification is null)
        {
            var verification = fixtureVerification = new Program();
            AppDomain.CurrentDomain.ProcessExit += (_, _) => ((IDisposable)verification).Dispose();
        }
        return fixtureVerification.CheckoutPackage();
    }

    /// <summary>Builds Lean test libraries in the checkout package and fails when one depends on sorryAx.</summary>
    static void BuildLeanTestLibraries(string progress, params string[] modules)
    {
        if (Run(["lake", "build", .. modules], FixturePackage(), progress: progress)
            .Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidOperationException(
                "A Lean test library depends on sorryAx: " + string.Join(' ', modules));
    }

    /// <summary>The Lean search path for static test helpers: checkout outputs, then the certified library.</summary>
    static string FixtureLeanPath()
    {
        var package = FixturePackage();
        return fixtureVerification!.SessionLeanPath(package);
    }

    /// <summary>The compiled module on a Lean search path, as Lean resolves it: the first directory that has it.</summary>
    static string ResolveOlean(string leanPath, string module) =>
        leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(directory => Path.Combine(directory, module.Replace('.', '/') + ".olean"))
            .FirstOrDefault(File.Exists) ?? throw new FileNotFoundException("Missing compiled module: " + module);

    // Authenticate all donor bytes before Lake sees its traces. Lake checks source hashes and
    // transitive build dependencies; changed/deleted modules cannot retain a compiled output.
    void StageIncrementalLibrary(string destination, string donor, string? trustedDigest,
        SortedDictionary<string, string> sources)
    {
        var bytes = File.ReadAllBytes(Path.Combine(donor, "cache-manifest.json"));
        if (string.IsNullOrWhiteSpace(trustedDigest) ||
            Convert.ToHexStringLower(SHA256.HashData(bytes)) != trustedDigest)
            throw new InvalidDataException("Incremental donor manifest digest mismatch");
        var manifest = JsonSerializer.Deserialize<SortedDictionary<string, string>>(bytes)
            ?? throw new InvalidDataException("Missing incremental donor manifest");
        var donorSources = LibrarySources(manifest);
        var (donorKey, _) = LibraryIdentity(donorSources);
        static bool Configuration(string name) => !name.EndsWith(".lean", StringComparison.Ordinal);
        if (!Same(new(donorSources.Where(pair => Configuration(pair.Key)).ToDictionary(), StringComparer.Ordinal),
                new(sources.Where(pair => Configuration(pair.Key)).ToDictionary(), StringComparer.Ordinal)))
            throw new InvalidDataException("Incremental donor build configuration changed");
        if (!CopyCertifiedLibrary(donor, destination, trustedDigest, donorKey, donorSources) ||
            !ValidCertifiedLibrary(destination, trustedDigest, donorKey, donorSources))
            throw new InvalidDataException("Incremental donor identity or integrity mismatch");
        var changed = donorSources.Keys.Union(sources.Keys, StringComparer.Ordinal)
            .Where(name => donorSources.GetValueOrDefault(name) != sources.GetValueOrDefault(name)).ToArray();
        foreach (var source in changed)
        {
            if (!source.EndsWith(".lean", StringComparison.Ordinal))
                throw new InvalidDataException("Unsupported incremental source: " + source);
            if (!sources.ContainsKey(source)) File.Delete(Path.Combine(destination, source));
            var module = source[..^".lean".Length];
            foreach (var subtree in new[] { ".lake/build/lib/lean/", ".lake/build/ir/" })
            foreach (var artifact in manifest.Keys.Where(name => name.StartsWith(subtree + module + ".",
                         StringComparison.Ordinal)))
                File.Delete(Path.Combine(destination, artifact));
        }
        // Re-link the native auditor from current checked sources, and regenerate source-bound metadata.
        foreach (var artifact in manifest.Keys.Where(name => name.StartsWith(".lake/build/bin/",
                     StringComparison.Ordinal)))
            File.Delete(Path.Combine(destination, artifact));
        foreach (var name in new[] { CertifiedFingerprintsName, "cache-manifest.json", "cache-receipt.hmac",
                     "library-key.txt" })
            File.Delete(Path.Combine(destination, name));
        Console.WriteLine($"Incremental library: {changed.Length} changed, added or removed sources; " +
            "Lake will rebuild their dependent closure before full kernel replay.");
    }

    static string RequireEmptyLibraryDestination(string destination)
    {
        destination = Path.GetFullPath(destination);
        if (File.Exists(destination) ||
            Directory.Exists(destination) && Directory.EnumerateFileSystemEntries(destination).Any())
            throw new InvalidOperationException("Certified library destination must be empty");
        return destination;
    }

    /// <summary>
    /// Publishes a freshly built library, or authenticates one restored under a trusted digest. A restored
    /// library is also kernel-replayed unless its producer ran reviewed producer code.
    /// </summary>
    string PrepareLibrary(string destination, string? trustedDigest = null, bool producerReplayed = false)
    {
        if (trustedDigest is not null)
            return (producerReplayed ? ReusePreparedLibrary(destination, trustedDigest)
                    : ReplayPreparedLibrary(destination, trustedDigest)) ??
                throw new InvalidOperationException("Certified library identity or integrity mismatch; destination left unchanged");
        destination = RequireEmptyLibraryDestination(destination);
        Library(Inputs(At("CIL.lean")));
        var staging = destination.TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar) + "." + Guid.NewGuid().ToString("N");
        try
        {
            CopyTree(library!, staging);
            File.WriteAllText(Path.Combine(staging, "library-key.txt"), libraryKey);
            var files = CacheFiles(staging);
            if (certifiedFingerprintsSha is not null &&
                files.GetValueOrDefault(CertifiedFingerprintsName) != certifiedFingerprintsSha)
                throw new InvalidDataException("Certified library fingerprint metadata changed while publishing.");
            File.WriteAllText(Path.Combine(staging, "cache-manifest.json"), JsonSerializer.Serialize(files, Json));
            var digest = Sha(Path.Combine(staging, "cache-manifest.json"));
            if (!ValidCertifiedLibrary(staging, digest, libraryKey!, LibrarySources(libraryInputs!)))
                throw new InvalidOperationException("Certified library changed while copying");
            // Never recursively delete an existing destination, even if it changed during the build.
            if (Directory.Exists(destination)) Directory.Delete(destination);
            Directory.Move(staging, destination);
            return digest;
        }
        finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
    }

    // Extend only the source set, never the certified compiled closure. Added helpers
    // remain uncertified until the normal proof verifier compiles, replays and audits them.
    string ExtendPreparedLibrary(string destination, string certifiedBase, string trustedDigest)
    {
        destination = Path.GetFullPath(destination);
        certifiedBase = Path.GetFullPath(certifiedBase);
        if (Directory.Exists(destination) && Directory.EnumerateFileSystemEntries(destination).Any())
            throw new InvalidOperationException("Certified library destination must be empty");
        var manifestBytes = File.ReadAllBytes(Path.Combine(certifiedBase, "cache-manifest.json"));
        if (Convert.ToHexStringLower(SHA256.HashData(manifestBytes)) != trustedDigest)
            throw new InvalidOperationException("Certified base manifest digest mismatch");
        var manifest = JsonSerializer.Deserialize<SortedDictionary<string, string>>(manifestBytes)
            ?? throw new InvalidDataException("Missing certified base manifest");
        var oldSources = LibrarySources(manifest);
        var (oldKey, _) = LibraryIdentity(oldSources);
        var (newKey, newSources) = LibraryIdentity(CommonInputs(libraryOnly: true));
        if (oldSources.Any(pair => !newSources.TryGetValue(pair.Key, out var hash) || hash != pair.Value))
            throw new InvalidDataException("Source extension changed or removed an existing certified source");
        var additions = newSources.Where(pair => !oldSources.ContainsKey(pair.Key)).ToArray();
        if (additions.Any(pair => !Regex.IsMatch(pair.Key,
                @"\ACIL/(?:[A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.lean\z")))
            throw new InvalidDataException("Source extension accepts only new CIL modules");
        var staging = destination.TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar) +
            "." + Guid.NewGuid().ToString("N");
        Directory.CreateDirectory(staging);
        var started = DateTimeOffset.UtcNow;
        var elapsed = Stopwatch.StartNew();
        try
        {
            if (!CopyCertifiedLibrary(certifiedBase, staging, trustedDigest, oldKey, oldSources) ||
                !ValidCertifiedLibrary(staging, trustedDigest, oldKey, oldSources))
                throw new InvalidDataException("Certified base identity or integrity mismatch");
            foreach (var (name, hash) in additions)
            {
                var module = name[..^".lean".Length];
                // Reject an added source for any previously compiled module, even when
                // its source was absent from the authenticated producer's source set.
                if (manifest.Keys.Any(path => path.StartsWith(".lake/build/lib/lean/" + module + ".",
                        StringComparison.Ordinal) || path.StartsWith(".lake/build/ir/" + module + ".",
                        StringComparison.Ordinal)) ||
                    new[] { ".olean", ".olean.private", ".olean.server", ".ilean", ".trace" }.Any(suffix =>
                        File.Exists(Path.Combine(staging, ".lake/build/lib/lean", module + suffix))) ||
                    new[] { ".c", ".ir", ".setup.json" }.Any(suffix =>
                        File.Exists(Path.Combine(staging, ".lake/build/ir", module + suffix))))
                    throw new InvalidDataException("Source extension shadows a compiled module: " + name);
                var target = Path.Combine(staging, name);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(At(name), target);
                if (Sha(target) != hash)
                    throw new InvalidDataException("Added source changed while copying: " + name);
            }
            if (!Same(newSources, CommonInputs(libraryOnly: true)))
                throw new InvalidDataException("Source extension changed during preparation");
            // Carry the producer's authenticated hashes forward; rehashing here could
            // otherwise authorize an old artifact that changed after its private copy.
            var extendedManifest = new SortedDictionary<string, string>(manifest, StringComparer.Ordinal);
            foreach (var (name, hash) in additions) extendedManifest.Add(name, hash);
            extendedManifest["library-key.txt"] = ContentKey(newKey);
            File.WriteAllText(Path.Combine(staging, "library-key.txt"), newKey);
            File.WriteAllText(Path.Combine(staging, "cache-manifest.json"),
                JsonSerializer.Serialize(extendedManifest, Json));
            var digest = Sha(Path.Combine(staging, "cache-manifest.json"));
            if (!ValidCertifiedLibrary(staging, digest, newKey, newSources))
                throw new InvalidDataException("Source extension changed while certifying");
            if (Directory.Exists(destination)) Directory.Delete(destination);
            Directory.Move(staging, destination);
            Trace("Extending certified library sources", started, destination, elapsed.Elapsed, 0, "",
                ["added-sources", additions.Length.ToString(), "compiled-modules-added", "0"]);
            return digest;
        }
        finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
    }

    /// <summary>
    /// The trusted digest when every file of the library matches the manifest it names and the manifest
    /// binds the current sources, or null. The library is not replayed, so a caller relies on a producer
    /// that ran reviewed producer code and kernel-replayed every module.
    /// </summary>
    string? ReusePreparedLibrary(string directory, string? trustedDigest)
    {
        var manifest = Path.Combine(directory, "cache-manifest.json");
        if (string.IsNullOrWhiteSpace(trustedDigest) || !File.Exists(manifest) || Sha(manifest) != trustedDigest)
            return null;
        var (key, sources) = LibraryIdentity(CommonInputs(libraryOnly: true));
        return ValidCertifiedLibrary(directory, trustedDigest, key, sources) ? trustedDigest : null;
    }

    /// <summary>
    /// Like <see cref="ReusePreparedLibrary"/>, but also kernel-replays every module, for a library whose
    /// producer may have run other code, such as a release asset or a PR that changed CI scripts.
    /// </summary>
    string? ReplayPreparedLibrary(string directory, string trustedDigest)
    {
        if (ReusePreparedLibrary(directory, trustedDigest) is null) return null;
        ReplayLibrary(directory, "reused Lean verification library");
        return ReusePreparedLibrary(directory, trustedDigest);
    }

    /// <summary>
    /// Kernel-replays every compiled module of a library, including modules outside the CIL aggregate,
    /// and fails unless all of them replay.
    /// </summary>
    void ReplayLibrary(string directory, string description)
    {
        // Replay runs inside the library, so a relative Lean path would resolve below it.
        directory = Path.GetFullPath(directory);
        var compiled = Path.Combine(directory, ".lake/build/lib/lean");
        string[] modules = [.. ModuleArtifacts(directory).Keys.Select(ModuleName)
            .Distinct().Order(StringComparer.Ordinal)];
        if (!ReplayModulesJointly(directory, modules, compiled, "Joint kernel replay of " + description))
            Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"),
                .. modules], directory, compiled, streamOutput: true, progress: "Kernel replay of " + description);
    }

    SortedDictionary<string, string> SupportInputs(string session, string[] roots, SortedDictionary<string, string> snapshot)
    {
        var rootKey = string.Join("\n", roots.Order(StringComparer.Ordinal));
        if (supportSourceKeys.TryGetValue(rootKey, out var known)) return known;
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);
        var pending = new Queue<string>(roots);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        // Lean may spell a file through other links than these directories, so both sides are compared resolved.
        string[] compiled = [ResolvedPath(Path.Combine(session, ".lake/build/lib/lean")),
            ResolvedPath(Path.Combine(library!, ".lake/build/lib/lean"))];
        var toolchain = ResolvedPath(Toolchain);
        while (pending.TryDequeue(out var module))
        {
            if (!seen.Add(module)) continue;
            var relative = module.Replace('.', '/') + ".lean";
            if (!snapshot.TryGetValue(relative, out var hash))
                return Conservative();
            result[relative] = hash;
            var dependencies = Execute(["lean", "--deps", Path.Combine(session, relative)], session, SessionLeanPath(session));
            if (dependencies.Code != 0) return Conservative();
            foreach (var dependency in dependencies.Stdout.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
            {
                var path = ResolvedPath(dependency);
                if (RelativeBelow(toolchain, path) is not null) continue;
                var name = CompiledName(compiled, path);
                if (name is null || !name.EndsWith(".olean", StringComparison.Ordinal)) return Conservative();
                var imported = name[..^6].Replace('/', '.');
                // All certified library sources are already bound by libraryKey.
                if (!IsCertifiedLibraryModule(imported)) pending.Enqueue(imported);
                else if (!certifiedModules!.ContainsKey(name)) pending.Enqueue(imported);
            }
        }
        supportSourceKeys[rootKey] = result;
        return result;

        SortedDictionary<string, string> Conservative() => new(snapshot.Where(pair =>
            pair.Key.EndsWith(".lean", StringComparison.Ordinal) && !pair.Key.StartsWith("proof:", StringComparison.Ordinal)).ToDictionary(), StringComparer.Ordinal);
    }

    /// <summary>
    /// `path` relative to the first of the `compiled` directories that holds it, with `/` separators, or null when
    /// none does; all are taken as resolved.
    /// </summary>
    internal static string? CompiledName(string[] compiled, string path) =>
        compiled.Select(directory => RelativeBelow(directory, path))
            .FirstOrDefault(name => name is not (null or "."))?.Replace('\\', '/');

    static void CopySupportArtifacts(string session, string destination, SortedDictionary<string, string> sources)
    {
        var modules = sources.Keys.Where(name => name.EndsWith(".lean", StringComparison.Ordinal))
            .Select(name => name[..^5]).ToHashSet(StringComparer.Ordinal);
        // Lake checks the C/IR outputs as well as oleans before reusing a module's
        // trace. Keep the entire output family for exactly the bound source closure.
        foreach (var subtree in new[] { ".lake/build/lib/lean", ".lake/build/ir" })
        {
            var compiled = Path.Combine(session, subtree);
            if (!Directory.Exists(compiled)) continue;
            foreach (var path in Directory.EnumerateFiles(compiled, "*", SearchOption.AllDirectories))
            {
                var relative = Path.GetRelativePath(compiled, path).Replace('\\', '/');
                var extension = relative.IndexOf('.', relative.LastIndexOf('/') + 1);
                if (extension < 0 || !modules.Contains(relative[..extension])) continue;
                var target = Path.Combine(destination, subtree, relative);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(path, target);
            }
        }
    }

    /// <summary>The build's informational version: the package version, then `+` and the git commit.</summary>
    static string? InformationalVersion => System.Reflection.CustomAttributeExtensions
        .GetCustomAttribute<System.Reflection.AssemblyInformationalVersionAttribute>(typeof(Program).Assembly)
        ?.InformationalVersion;

    /// <summary>The LeanCIL commit this build was made from, or null when it was built outside git.</summary>
    // A build from a modified checkout still names its base commit; framework source checks catch the drift.
    internal static string? SourceRevision =>
        InformationalVersion is { } version && version.IndexOf('+') is var plus and >= 0 ? version[(plus + 1)..] : null;

}
