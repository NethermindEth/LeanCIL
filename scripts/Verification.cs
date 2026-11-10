using System.Buffers;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program : IDisposable
{
#if LEANCIL_TOOL
    static string Root { get; } = Path.Combine(AppContext.BaseDirectory, "verification");
#else
    static string Root { get; } = FixtureRoot() ??
        Path.GetFullPath(Path.Combine(Path.GetDirectoryName(Source())!, ".."));

    // Only relocated binaries need the producer's source path replaced. Source-built children
    // may belong to an isolated corpus and must retain their own Verification.cs location.
    static string? FixtureRoot()
    {
        var root = Environment.GetEnvironmentVariable("LEANCIL_FIXTURE_ROOT");
        var manifest = Environment.GetEnvironmentVariable("LEANCIL_FIXTURE_MANIFEST");
        if (string.IsNullOrEmpty(root) || string.IsNullOrEmpty(manifest)) return null;
        var directory = Path.GetDirectoryName(Path.GetFullPath(manifest))! + Path.DirectorySeparatorChar;
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        return typeof(Program).Assembly.Location.StartsWith(directory, comparison) ? Path.GetFullPath(root) : null;
    }
#endif

    static string Source([CallerFilePath] string path = "") => path;

    /// <summary>The certified library, read in place; deleted on disposal only when this process built it.</summary>
    string? library;
    bool ownsLibrary;
    /// <summary>The cache entry this process published from the library it built, which outlives the process.</summary>
    string? publishedLibrary;
    /// <summary>Length and write time of each file of a library read in place, as it was when opened.</summary>
    SortedDictionary<string, string>? libraryStamps;
    /// <summary>
    /// Every module of the open library when it is a closure entry, which holds only those; null for the
    /// whole library. <see cref="libraryKey"/> then names exactly this list.
    /// </summary>
    string[]? libraryModules;
    /// <summary>A result was reported against a closure entry, so disposal builds the whole library.</summary>
    bool completesLibrary;
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

#if !LEANCIL_TOOL
    const string FixtureManifestEnvironment = "LEANCIL_FIXTURE_MANIFEST";
    const string FixtureDigestEnvironment = "LEANCIL_FIXTURE_MANIFEST_SHA256";
    sealed record PreparedFixture(string Assembly, SortedDictionary<string, string> Inputs,
        SortedDictionary<string, string> Outputs);
    sealed record PreparedFixtures(string Sdk, string Runtime, Dictionary<string, PreparedFixture> Fixtures);
    static string? fixtureSdk;

    static SortedDictionary<string, string>? FixtureInputs(string script)
    {
        var inputs = new SortedDictionary<string, string>(StringComparer.Ordinal);
        var supported = true;
        void Add(string path)
        {
            path = Path.GetFullPath(path);
            var relative = Path.GetRelativePath(Root, path).Replace('\\', '/');
            if (relative.StartsWith("../", StringComparison.Ordinal) || Path.IsPathRooted(relative))
                throw new InvalidOperationException("Fixture input is outside the checkout: " + path);
            if (!inputs.TryAdd(relative, Sha(path))) return;
            if (Path.GetExtension(path) != ".cs") return;
            var source = File.ReadAllText(path);
            // Project references bring in an MSBuild graph not described by file-app includes.
            if (Regex.IsMatch(source, @"(?m)^[\t ]*#:project\b")) supported = false;
            foreach (Match include in Regex.Matches(source, @"(?m)^[\t ]*#:include\s+([^\r\n]+)"))
                Add(Path.Combine(Path.GetDirectoryName(path)!, include.Groups[1].Value.Trim()));
        }
        Add(At(script));
        var root = Path.TrimEndingDirectorySeparator(Root);
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        for (var directory = Path.GetDirectoryName(Path.GetFullPath(script, Root)); directory is not null;
             directory = Path.GetDirectoryName(directory))
        {
            foreach (var path in Directory.EnumerateFiles(directory))
                  if (Path.GetExtension(path).ToLowerInvariant() is ".props" or ".targets" ||
                      Path.GetFileName(path).ToLowerInvariant() is "global.json" or "nuget.config" or ".editorconfig")
                    Add(path);
            if (directory.Equals(root, comparison)) break;
        }
        return supported ? inputs : null;
    }

    // The workflow pins this manifest's digest separately from its downloadable artifact.
    static string[]? PreparedFixtureCommand(string script, string[] arguments)
    {
        var manifest = Environment.GetEnvironmentVariable(FixtureManifestEnvironment);
        if (string.IsNullOrEmpty(manifest)) return null;
        if (Sha(manifest) != Environment.GetEnvironmentVariable(FixtureDigestEnvironment))
            throw new InvalidOperationException("Prepared fixture manifest changed");
        var prepared = JsonSerializer.Deserialize<PreparedFixtures>(File.ReadAllText(manifest))!;
        var relative = Path.GetRelativePath(Root, Path.GetFullPath(script, Root)).Replace('\\', '/');
        if (!prepared.Fixtures.TryGetValue(relative, out var fixture)) return null;
        fixtureSdk ??= Run(["dotnet", "--version"]).Trim();
        if (prepared.Runtime != RuntimeInformation.RuntimeIdentifier || prepared.Sdk != fixtureSdk ||
            FixtureInputs(relative) is not { } inputs || !Same(fixture.Inputs, inputs)) return null;
        var directory = Path.GetDirectoryName(manifest)!;
        directory = Path.GetFullPath(directory);
        var assemblyDirectory = Path.GetDirectoryName(Path.GetFullPath(fixture.Assembly, directory))!;
        if (!Directory.Exists(assemblyDirectory) ||
            !fixture.Outputs.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                Directory.EnumerateFiles(assemblyDirectory, "*", SearchOption.AllDirectories)
                    .Select(path => Path.GetRelativePath(directory, path).Replace('\\', '/'))))
            throw new InvalidOperationException("Prepared fixture output set changed: " + relative);
        foreach (var (path, hash) in fixture.Outputs)
        {
            var full = Path.GetFullPath(path, directory);
            if (!full.StartsWith(directory + Path.DirectorySeparatorChar, StringComparison.OrdinalIgnoreCase) ||
                !File.Exists(full) || Sha(full) != hash)
                throw new InvalidOperationException("Prepared fixture output changed: " + path);
        }
        if (!fixture.Outputs.ContainsKey(fixture.Assembly))
            throw new InvalidOperationException("Prepared fixture assembly is missing from the manifest");
        return ["dotnet", Path.GetFullPath(fixture.Assembly, directory), .. arguments];
    }

    static string[] ReusePreparedFixture(string[] command, string cwd)
    {
        if (command.Length < 4 || command[0] != "dotnet" || command[1] != "run" || command[2] != "--file")
            return command;
        var separator = Array.IndexOf(command, "--", 4);
        var options = command[4..(separator < 0 ? command.Length : separator)];
        // Only the repository's standard Release build options match the producer.
        if (options.Length != 0 && !options.SequenceEqual(new[] { "-c", "Release", "--no-build",
                "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true" }) &&
            !options.SequenceEqual(new[] { "-c", "Release",
                "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true" })) return command;
        var arguments = separator < 0 ? [] : command[(separator + 1)..];
        // Nested fixtures share the parent's Release configuration but still rebuild changed sources.
        return PreparedFixtureCommand(Path.GetFullPath(command[3], cwd), arguments) ??
            (options.Length == 0 ? FixtureCommand(command[3], arguments, prepared: false) : command);
    }
#endif

    static string[] FixtureCommand(string script, string[] arguments, bool prepared)
    {
        string[] buildArguments = prepared
            ? ["-c", "Release", "--no-build", "-p:EnforceCodeStyleInBuild=true",
                "-p:GenerateDocumentationFile=true"]
            : ["-c", "Release", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"];
        return ["dotnet", "run", "--file", script, .. buildArguments, "--", .. arguments];
    }

    // A parent build can be reused only while its sources and complete output still match.
    static string ExtractorBuildIdentity()
    {
        if (!File.Exists(ExtractorPath)) return "";
        var inputs = CommonInputs();
        foreach (var path in Directory.EnumerateFiles(Root))
            inputs["root:" + Path.GetFileName(path)] = Sha(path);
        foreach (var path in Directory.EnumerateFiles(At("Extractor"), "*", SearchOption.AllDirectories))
        {
            var relative = Path.GetRelativePath(Root, path).Replace('\\', '/');
            if (!relative.Split('/').Any(part => part is "bin" or "obj"))
                inputs[relative] = Sha(path);
        }
        foreach (var path in Directory.EnumerateFiles(Path.GetDirectoryName(ExtractorPath)!, "*",
                     SearchOption.AllDirectories))
            inputs["output:" + Path.GetRelativePath(Root, path)] = Sha(path);
        return ContentKey(Root + JsonSerializer.Serialize(inputs));
    }

    static bool PreparedExtractorMatches()
    {
        var prepared = Environment.GetEnvironmentVariable(ExtractorBuildEnvironment);
        return !string.IsNullOrEmpty(prepared) && prepared == ExtractorBuildIdentity();
    }

    void EnsureExtractorBuilt()
    {
        if (extractorBuilt) return;
        if (!PreparedExtractorMatches())
            Run(["dotnet", "build", "Extractor", "-c", "Release",
                "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
        extractorBuilt = true;
    }
    int extractionCacheHits;
    int proofCacheHits;
    int supportCacheHits;
    SortedDictionary<string, string>? certifiedModules;

    byte[]? receiptKey;
    readonly HashSet<string> preparedSupport = new(StringComparer.Ordinal);
    string? verificationPolicy;
    string VerificationPolicy => verificationPolicy ??= Sha(typeof(Program).Assembly.Location);
    readonly Dictionary<string, SortedDictionary<string, string>> supportSourceKeys = new(StringComparer.Ordinal);

    bool forceFullVerification { get; init; }
    sealed record FullImportResult(string Theorem, string Audit, PublishedImport[] Imports,
        DeploymentDependency[] Dependencies);
    Func<string, string, string, string, FullImportResult>? fullImportAudit { get; set; }
    readonly AsyncLocal<bool> referenceOnlyContext = new();
    bool referenceOnlyAuthoring { get => referenceOnlyContext.Value; set => referenceOnlyContext.Value = value; }
    bool UseSuccessCache => !referenceOnlyAuthoring && !freshProofs && !freshLibrary &&
        !string.Equals(Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE"), "true", StringComparison.OrdinalIgnoreCase);

    static string SuccessCacheRoot => Path.Combine(Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
        Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries"), "success-v1");

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

    // The cache only saves work: a full disk warns instead of failing a verified result.
    void PublishSuccess(string key, string source, string? family = null)
    {
        if (!UseSuccessCache) return;
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
            TouchSuccess(cached);
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
                Directory.Move(staging, cached);
                return;
            }
            catch (IOException) when (Directory.Exists(cached)) { }
            if (AuthenticatedSuccess(key) is not null) return;
            // Replace a corrupt or unauthenticated entry; readers authenticate every file.
            var invalid = cached + ".invalid-" + Guid.NewGuid().ToString("N");
            try
            {
                Directory.Move(cached, invalid);
                Directory.Move(staging, cached);
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

    string LeanExecutable => Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean");

    // Pin the sysroot that `lake env` would supply, so direct Lean runs use the trusted toolchain.
    IReadOnlyDictionary<string, string> LeanEnvironment => new Dictionary<string, string> { ["LEAN_SYSROOT"] = Toolchain };

    readonly byte[] bootstrapReplaySource = File.ReadAllBytes(At("CIL/Replay.lean"));

    // Per-module replay re-imports each module's dependencies; one shared import of
    // everything outside the targets makes large sets several times cheaper.
    // Imported target declarations cannot be skipped as already-checked duplicate theorems.
    // False when the set is ineligible or any declaration is rejected; callers then replay per module.
    bool ReplayModulesJointly(string cwd, string[] targets, string leanPath, string progress)
    {
        var runner = Path.Combine(Path.GetTempPath(), "leancil-joint-replay-" + Guid.NewGuid().ToString("N") + ".lean");
        var targetsPath = Path.ChangeExtension(runner, ".json");
        try
        {
            File.WriteAllText(targetsPath, JsonSerializer.Serialize(targets));
            string[] command;
            if (auditExecutable is not null)
                command = [CheckedAuditExecutable(), "--replay", targetsPath];
            else
            {
                // Bootstrap certification cannot trust the native auditor before authenticating it.
                if (Convert.ToHexStringLower(SHA256.HashData(bootstrapReplaySource)) != Sha(At("CIL/Replay.lean")))
                    throw new InvalidDataException("Kernel replay source changed before certification.");
                File.WriteAllText(runner, Encoding.UTF8.GetString(bootstrapReplaySource) +
                    "\n#eval do\n  let json ← IO.FS.readFile (String.fromUTF8! (ByteArray.mk #[" +
                    string.Join(",", System.Text.Encoding.UTF8.GetBytes(targetsPath)) +
                    "]))\n  let args ← IO.ofExcept <| (Lean.Json.parse json).bind Lean.fromJson?\n" +
                    "  CIL.Replay.replayModulesJointly args\n");
                command = [LeanExecutable, runner];
            }
            var result = Execute(command, cwd, leanPath, progress: progress, environment: LeanEnvironment);
            if (auditExecutable is not null) CheckedAuditExecutable();
            if (result.Code != 0) return false;
            var replayed = new HashSet<string>(StringComparer.Ordinal);
            foreach (var line in result.Stdout.Split('\n', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
            {
                if (!line.StartsWith('{')) continue;
                try
                {
                    var record = JsonSerializer.Deserialize<JsonElement>(line);
                    if (record.ValueKind == JsonValueKind.Object && record.TryGetProperty("joint", out var joint) &&
                        joint.ValueKind == JsonValueKind.True && record.TryGetProperty("module", out var module) &&
                        module.ValueKind == JsonValueKind.String)
                        replayed.Add(module.GetString()!);
                }
                catch (JsonException) { }
            }
            return replayed.SetEquals(targets);
        }
        finally { File.Delete(runner); File.Delete(targetsPath); }
    }

    // Joint replay shares imported dependencies; rejected target sets retain the toolchain fallback.
    void ReplayCheckedModules(string[] targets, string leanPath, string progress)
    {
        if ((targets.Length > 1 || (targets.Length == 1 && auditExecutable is not null)) &&
            ReplayModulesJointly(Root, targets, leanPath, progress)) return;
        Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"),
            .. targets], leanPath: leanPath, progress: progress);
    }

    static SortedDictionary<string, string> ModuleArtifacts(string session) =>
        !Directory.Exists(Path.Combine(session, ".lake/build/lib/lean")) ? new(StringComparer.Ordinal) :
        HashFiles(Directory.EnumerateFiles(Path.Combine(session, ".lake/build/lib/lean"), "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
            .Select(path => (Path.GetRelativePath(Path.Combine(session, ".lake/build/lib/lean"), path)
                .Replace('\\', '/'), path)));

    // Publish a deterministic manifest only after every file has been hashed successfully.
    static SortedDictionary<string, string> HashFiles(IEnumerable<(string Name, string Path)> files)
    {
        var entries = files.ToArray();
        var hashes = new string[entries.Length];
        var failures = new ExceptionDispatchInfo?[entries.Length];
        const int maximumWorkers = 4;
        Parallel.For(0, entries.Length,
            new ParallelOptions { MaxDegreeOfParallelism = Math.Min(maximumWorkers, Environment.ProcessorCount) },
            index =>
            {
                try { hashes[index] = Sha(entries[index].Path); }
                catch (Exception error) { failures[index] = ExceptionDispatchInfo.Capture(error); }
            });
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);
        for (var index = 0; index < entries.Length; index++)
        {
            // Preserve ordinary I/O exceptions so invalid-cache handling still applies.
            failures[index]?.Throw();
            result.Add(entries[index].Name, hashes[index]);
        }
        return result;
    }

    static string ModuleName(string artifact) => artifact.Split(".olean", 2)[0].Replace('/', '.');

    string Toolchain => resolvedToolchain ??= Run(["lean", "--print-prefix"]).Trim();
    SortedDictionary<string, string>? libraryInputs;

    static string At(string path) => Path.Combine(Root, path);

    /// <summary>Deletes a tree that may hold git objects, which git marks read-only and Windows refuses to delete.</summary>
    static void DeleteTree(string directory)
    {
        EnumerationOptions ownFiles = new() { RecurseSubdirectories = true, AttributesToSkip = FileAttributes.ReparsePoint };
        foreach (var file in Directory.EnumerateFiles(directory, "*", ownFiles))
            File.SetAttributes(file, FileAttributes.Normal);
        Directory.Delete(directory, recursive: true);
    }

    static string Sha(string path)
    {
        const int bufferSize = 64 * 1024;
        using var file = File.OpenHandle(path, FileMode.Open, FileAccess.Read, FileShare.Read);
        var length = RandomAccess.GetLength(file);
        if (length > Array.MaxLength) throw new IOException("The file is too long to read.");
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        var buffer = ArrayPool<byte>.Shared.Rent(bufferSize);
        try
        {
            // A positive initial length bounds the read; premature EOF must fail.
            var offset = 0L;
            while (length == 0 || offset < length)
            {
                var count = length == 0 ? bufferSize : (int)Math.Min(bufferSize, length - offset);
                var read = RandomAccess.Read(file, buffer.AsSpan(0, count), offset);
                if (read == 0)
                {
                    if (length != 0) throw new EndOfStreamException();
                    break;
                }
                hash.AppendData(buffer, 0, read);
                offset += read;
            }
            return Convert.ToHexStringLower(hash.GetHashAndReset());
        }
        finally { ArrayPool<byte>.Shared.Return(buffer); }
    }

    static void CacheProgress(string message)
    {
#if !LEANCIL_TOOL
        Console.WriteLine("CACHE " + message);
#endif
    }

    static readonly JsonSerializerOptions Json = new() { WriteIndented = true };

    sealed class ProgressSummary(string label)
    {
        readonly object gate = new();
        string latest = "";
        int pending;

        public void Add(string line, TextWriter writer)
        {
            if (string.IsNullOrWhiteSpace(line)) return;
            lock (gate)
            {
                if (line.StartsWith("PASS ", StringComparison.Ordinal) || line.StartsWith("All ", StringComparison.Ordinal))
                    writer.WriteLine(line);
                else
                {
                    // Lake prints axiom details after its completed-target line.
                    // Keep the target count or proof phase as the summary instead.
                    if (latest.Length == 0 || (!line.StartsWith("info: ", StringComparison.Ordinal) &&
                        !line.Contains("depends on axioms:", StringComparison.Ordinal)))
                        latest = line.Length > 200 ? line[..200] + "…" : line;
                    pending++;
                }
            }
        }

        public void Report()
        {
            lock (gate)
            {
                if (pending == 0) return;
                Console.WriteLine($"PROGRESS {label}: {latest} ({pending} output lines since last update)");
                pending = 0;
            }
        }
    }

    /// <summary>The latest `[done/total]` job count that a Lake build printed, for progress lines.</summary>
    sealed partial class JobCount
    {
        string latest = "";

        public void Add(string line)
        {
            if (LakeJob().Match(line) is { Success: true } job)
                Volatile.Write(ref latest, $": {job.Groups[1].Value} of {job.Groups[2].Value} Lake jobs");
        }

        public override string ToString() => Volatile.Read(ref latest);

        [GeneratedRegex(@"\A(?:\S+ )?\[([0-9]+)/([0-9]+)\] ")]
        private static partial Regex LakeJob();
    }

    static async Task<string> CaptureOutput(StreamReader reader, TextWriter writer, ProgressSummary? summary = null,
        TextWriter? transcript = null, JobCount? jobs = null)
    {
        var captured = new StringBuilder();
        var line = new StringBuilder();
        var buffer = new char[4096];
        int count;
        while ((count = await reader.ReadAsync(buffer)) != 0)
        {
            captured.Append(buffer, 0, count);
            if (transcript is not null)
            {
                await transcript.WriteAsync(buffer.AsMemory(0, count));
                await transcript.FlushAsync();
            }
            if (summary is null)
            {
                await writer.WriteAsync(buffer.AsMemory(0, count));
                await writer.FlushAsync();
            }
            if (summary is null && jobs is null) continue;
            for (var i = 0; i < count; i++)
                if (buffer[i] == '\n')
                {
                    var text = line.ToString().TrimEnd('\r');
                    summary?.Add(text, writer);
                    jobs?.Add(text);
                    line.Clear();
                }
                else line.Append(buffer[i]);
        }
        if (summary is not null && line.Length > 0) summary.Add(line.ToString(), writer);
        return captured.ToString();
    }

    /// <summary>Milliseconds between progress lines of one stage on a terminal.</summary>
    const int InteractiveProgressInterval = 10_000;
    /// <summary>Milliseconds between progress lines when stderr is redirected; a shorter stage prints none.</summary>
    const int RedirectedProgressInterval = 20_000;

    /// <summary>
    /// Stderr without stage progress lines, which a run prints for any stage that outlasts an interval:
    /// what remains is the command's own diagnostics.
    /// </summary>
    internal static string WithoutStageProgress(string stderr) => StageProgressLine().Replace(stderr, "");

    [GeneratedRegex(@"^(?:START|PROGRESS|END) [^\n]*(?:\n|\z)", RegexOptions.Multiline)]
    private static partial Regex StageProgressLine();

    static readonly object TraceGate = new();
    // A reused process id must not append to an earlier process's trace, which a reader treats as old.
    static readonly string TraceFile = $"{Environment.ProcessId}-{Guid.NewGuid():N}.jsonl";

    static (int Code, string Output, string Stdout, string Stderr) Execute(IEnumerable<string> command, string? cwd = null, string? leanPath = null,
        bool streamOutput = false, string? progress = null, IReadOnlyDictionary<string, string>? environment = null)
    {
        var traceStage = progress;
#if LEANCIL_TOOL
        // Stdout stays the report. A redirected stderr names only a stage that outlasts one interval.
        var interactive = !Console.IsErrorRedirected;
        var announced = interactive && progress is not null;
        if (announced) Console.Error.WriteLine("START " + progress);
        var jobs = progress is null ? null : new JobCount();
        progress = null;
        streamOutput = false;
#else
        JobCount? jobs = null;
#endif
        // Aggregate at the suite boundary; nested build/proof phases feed this summary.
        var summary = streamOutput && progress is not null ? new ProgressSummary(progress) : null;
        streamOutput |= progress is not null;
        var args = command.ToArray();
#if !LEANCIL_TOOL
        args = ReusePreparedFixture(args, cwd ?? Root);
#endif
        var start = new ProcessStartInfo(args[0])
        {
            WorkingDirectory = cwd ?? Root,
            UseShellExecute = false,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            StandardOutputEncoding = Encoding.UTF8,
            StandardErrorEncoding = Encoding.UTF8,
            CreateNoWindow = true
        };

        foreach (var arg in args.Skip(1))
            start.ArgumentList.Add(arg);

        if (leanPath is not null)
            start.Environment["LEAN_PATH"] = leanPath;
#if !LEANCIL_TOOL
        if (!string.IsNullOrEmpty(Environment.GetEnvironmentVariable(FixtureManifestEnvironment)))
            start.Environment["LEANCIL_FIXTURE_ROOT"] = Root;
#endif
        foreach (var (name, value) in environment ?? new Dictionary<string, string>())
            start.Environment[name] = value;
        if (ChecksLeanEnvironment(args, leanPath is not null))
            RequireLeanEnvironmentFits(args, start.WorkingDirectory, start.Environment);

        if (progress is not null) Console.WriteLine("START " + progress);
        var startedAtUtc = DateTimeOffset.UtcNow;
        var elapsed = Stopwatch.StartNew();
        using var process = new Process { StartInfo = start };
        try
        {
            if (!process.Start())
                throw new InvalidOperationException("Process did not start");
        }
        catch (System.ComponentModel.Win32Exception exception) when (exception.NativeErrorCode is 2 or 3)
        {
            throw new InvalidOperationException("Required command not found: " + args[0], exception);
        }
        var traceDirectory = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
        var transcript = $"{Environment.ProcessId}-{Guid.NewGuid():N}.log";
        if (!string.IsNullOrWhiteSpace(traceDirectory)) Directory.CreateDirectory(traceDirectory);
        using var traceWriter = string.IsNullOrWhiteSpace(traceDirectory) ? null :
            TextWriter.Synchronized(new StreamWriter(Path.Combine(traceDirectory, transcript), false, Encoding.UTF8));
        var stdout = CaptureOutput(process.StandardOutput, streamOutput ? Console.Out : TextWriter.Null, summary,
            traceWriter, jobs);
        var stderr = CaptureOutput(process.StandardError, streamOutput ? Console.Error : TextWriter.Null, summary,
            traceWriter, jobs);
        if (summary is null)
        {
#if LEANCIL_TOOL
            if (traceStage is not null)
                while (!process.WaitForExit(interactive ? InteractiveProgressInterval : RedirectedProgressInterval))
                {
                    Console.Error.WriteLine($"PROGRESS {traceStage}{jobs} ({elapsed.Elapsed.TotalSeconds:F0}s)");
                    announced = true;
                }
            else
#endif
                process.WaitForExit();
        }
        else
            while (!process.WaitForExit(10_000)) summary.Report();

        var output = stdout.GetAwaiter().GetResult();
        var error = stderr.GetAwaiter().GetResult();
        if (progress is not null)
            Console.WriteLine($"END {progress} (exit {process.ExitCode}, {elapsed.Elapsed.TotalSeconds:F1}s)");
#if LEANCIL_TOOL
        if (announced)
            Console.Error.WriteLine($"END {traceStage} (exit {process.ExitCode}, {elapsed.Elapsed.TotalSeconds:F1}s)");
#endif
        Trace(traceStage ?? string.Join(" ", args.Take(2)), startedAtUtc, start.WorkingDirectory, elapsed.Elapsed, process.ExitCode, transcript, args);
        return (process.ExitCode, output + error, output, error);
    }

    static void Trace(string stage, DateTimeOffset startedAtUtc, string cwd, TimeSpan elapsed, int exitCode, string transcript, string[] command)
    {
        var traceDirectory = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
        if (string.IsNullOrWhiteSpace(traceDirectory)) return;
        Directory.CreateDirectory(traceDirectory);
        // Concurrent commands in one process append to the same trace file.
        lock (TraceGate)
            File.AppendAllText(Path.Combine(traceDirectory, TraceFile), JsonSerializer.Serialize(new {
            stage, startedAtUtc, processId = Environment.ProcessId, cwd, durationSeconds = elapsed.TotalSeconds,
            exitCode, transcript, command, suite = Environment.GetEnvironmentVariable("LEANCIL_SUITE")
        }) + "\n");
    }

    static string Run(IEnumerable<string> command, string? cwd = null, string? leanPath = null,
        bool streamOutput = false, string? progress = null, IReadOnlyDictionary<string, string>? environment = null)
    {
        var args = command.ToArray();
        var result = Execute(args, cwd, leanPath, streamOutput, progress, environment);

        if (result.Code != 0)
            throw new InvalidOperationException($"Command failed ({result.Code}): {string.Join(' ', args)}\n{result.Output}");

        return result.Output;
    }

    /// <summary>
    /// Lean on Windows builds a child's environment in one buffer of this many bytes: inherited entries are copied
    /// unchecked, and an override that no longer fits is dropped silently, with every override after it.
    /// </summary>
    const int LeanEnvironmentBuffer = 0x7fff;
    /// <summary>Lowers, never raises, the enforced block size; set on another OS, it enables the check.</summary>
    const string LeanEnvironmentLimitVariable = "LEANCIL_LEAN_ENVIRONMENT_LIMIT";
    const int LargestVariablesShown = 6;
    static readonly System.Collections.Concurrent.ConcurrentDictionary<string, KeyValuePair<string, string>[]?>
        LakeVariables = new(StringComparer.Ordinal);

    /// <summary>One `name=value` entry of an environment block, and whether Lake set it.</summary>
    sealed record EnvironmentEntry(string Name, string Value, bool SetByLake)
    {
        /// <summary>The entry's bytes with its terminator; Lean's executables use the UTF-8 code page.</summary>
        public int Bytes => Encoding.UTF8.GetByteCount(Name) + Encoding.UTF8.GetByteCount(Value) + 2;
    }

    /// <summary>The largest environment block a Lean process can pass on; null where Lean has no limit.</summary>
    static int? LeanEnvironmentLimit()
    {
        int? limit = OperatingSystem.IsWindows() ? LeanEnvironmentBuffer : null;
        var configured = Environment.GetEnvironmentVariable(LeanEnvironmentLimitVariable);
        if (string.IsNullOrEmpty(configured)) return limit;
        if (!int.TryParse(configured, System.Globalization.NumberStyles.None,
                System.Globalization.CultureInfo.InvariantCulture, out var lowered) || lowered <= 0)
            throw new ArgumentException(LeanEnvironmentLimitVariable + " must be a positive number of bytes.");
        return Math.Min(limit ?? lowered, lowered);
    }

    /// <summary>Whether `command` starts Lean processes that may start others with their own environment.</summary>
    static bool ChecksLeanEnvironment(string[] command, bool leanSearchPath) =>
        (leanSearchPath || Path.GetFileNameWithoutExtension(command[0]) == "lake") &&
        LeanEnvironmentLimit() is not null;

    /// <summary>
    /// Fails before `command` starts when the environment its Lean processes would hand their children exceeds the
    /// limit, naming the size and the largest variables, instead of letting Lean drop LEAN_PATH without an error.
    /// </summary>
    static void RequireLeanEnvironmentFits(string[] command, string cwd, IDictionary<string, string?> environment)
    {
        if (LeanEnvironmentLimit() is not { } limit ||
            PredictedLeanChildEnvironment(command, cwd, environment) is not { } entries) return;
        var size = EnvironmentBlockBytes(entries);
        if (size > limit)
            throw new InvalidOperationException(LeanEnvironmentOverflow(command, cwd, entries, size, limit));
    }

    /// <summary>
    /// The block a Lean process started by `command` builds for its own children: for Lake, its inherited
    /// environment after the elan proxy's changes plus the variables Lake sets; for another Lean program, the
    /// environment it is given. Null when the command starts no child with an environment of its own.
    /// </summary>
    static EnvironmentEntry[]? PredictedLeanChildEnvironment(string[] command, string cwd,
        IDictionary<string, string?> environment)
    {
        var inherited = environment.Where(entry => entry.Value is not null)
            .Select(entry => KeyValuePair.Create(entry.Key, entry.Value!)).ToList();
        if (Path.GetFileNameWithoutExtension(command[0]) != "lake") return LeanChildEnvironment(inherited, []);
        var subcommand = command.Skip(1).FirstOrDefault(argument => !argument.StartsWith('-'));
        // Printing its variables and updating dependencies start no Lean process with an environment.
        if (subcommand is null or "update" || subcommand == "env" && command[^1] == "env") return null;
        if (LakeEnvironment(cwd, inherited) is not { } lake) return LeanChildEnvironment(inherited, []);
        ApplyElanProxy(inherited, lake);
        // A build starts Lean with LEAN_PATH alone; the printed value also holds Lake's own library directory.
        return LeanChildEnvironment(inherited,
            subcommand == "build" ? [.. lake.Where(entry => entry.Key == "LEAN_PATH")] : lake);
    }

    /// <summary>
    /// The block Lean builds from `inherited` and `overrides`: the inherited entries whose name no override spells
    /// exactly, since Lean compares names case-sensitively even on Windows, then every override.
    /// </summary>
    static EnvironmentEntry[] LeanChildEnvironment(IEnumerable<KeyValuePair<string, string>> inherited,
        IReadOnlyCollection<KeyValuePair<string, string>> overrides)
    {
        var replaced = overrides.Select(entry => entry.Key).ToHashSet(StringComparer.Ordinal);
        return [.. inherited.Where(entry => !replaced.Contains(entry.Key))
                .Select(entry => new EnvironmentEntry(entry.Key, entry.Value, false)),
            .. overrides.Select(entry => new EnvironmentEntry(entry.Key, entry.Value, true))];
    }

    /// <summary>The block's size in bytes: every entry with its terminator, then the block's own terminator.</summary>
    static int EnvironmentBlockBytes(IEnumerable<EnvironmentEntry> entries) => entries.Sum(entry => entry.Bytes) + 1;

    /// <summary>
    /// The variables Lake sets for Lean in `cwd` under `environment`, as `lake env` prints them, or null when Lake
    /// cannot load the workspace. Lake prints a variable it unsets as empty, so counting it can only overcount.
    /// </summary>
    static KeyValuePair<string, string>[]? LakeEnvironment(string cwd,
        IReadOnlyCollection<KeyValuePair<string, string>> environment)
    {
        var given = environment.ToDictionary(entry => entry.Key, entry => entry.Value);
        // Lake's paths follow the package's libraries and dependencies, so an edited lakefile or manifest re-asks.
        var workspace = new[] { "lakefile.toml", "lakefile.lean", "lake-manifest.json" }
            .Select(name => Path.Combine(cwd, name)).Where(File.Exists).Select(path => path + "=" + Sha(path));
        var key = Path.GetFullPath(cwd) + "\n" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(
            string.Join('\0', given.OrderBy(entry => entry.Key, StringComparer.Ordinal)
                .Select(entry => entry.Key + "=" + entry.Value).Concat(workspace)))));
        return LakeVariables.GetOrAdd(key, _ =>
        {
            var printed = Execute(["lake", "env"], cwd, environment: given);
            // A workspace Lake cannot load fails the command itself, with Lake's own error.
            return printed.Code != 0 ? null : [.. printed.Stdout.Split('\n')
                .Select(line => line.TrimEnd('\r')).Where(line => line.Contains('='))
                .Select(line => KeyValuePair.Create(line[..line.IndexOf('=')], line[(line.IndexOf('=') + 1)..]))];
        });
    }

    /// <summary>
    /// Applies what elan's proxy sets before it starts the toolchain's Lake, when a bare `lake` resolves to it:
    /// elan's and (on Windows) the toolchain's bin directories ahead of PATH, a raised LEAN_RECURSION_COUNT, and
    /// ELAN_TOOLCHAIN and ELAN_HOME, each under the spelling the environment already uses.
    /// </summary>
    static void ApplyElanProxy(List<KeyValuePair<string, string>> inherited,
        IReadOnlyCollection<KeyValuePair<string, string>> lake)
    {
        string Printed(string name) => lake.FirstOrDefault(entry => entry.Key == name).Value ?? "";
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        var elanBin = Printed("ELAN_HOME") is { Length: > 0 } home ? Path.Combine(home, "bin") : null;
        if (elanBin is null || LakeOnPath() is not { } proxy ||
            !string.Equals(Path.GetDirectoryName(proxy), elanBin, comparison)) return;
        void Set(string name, Func<string?, string> value)
        {
            var index = inherited.FindIndex(entry => entry.Key.Equals(name, comparison));
            var entry = KeyValuePair.Create(index < 0 ? name : inherited[index].Key,
                value(index < 0 ? null : inherited[index].Value));
            if (index < 0) inherited.Add(entry);
            else inherited[index] = entry;
        }
        string[] prefix = OperatingSystem.IsWindows()
            ? [elanBin, Path.Combine(Printed("LEAN_SYSROOT"), "bin")] : [elanBin];
        Set("PATH", current => string.Join(Path.PathSeparator, current is null ? prefix : [.. prefix, current]));
        Set("LEAN_RECURSION_COUNT", current => ((uint.TryParse(current, System.Globalization.NumberStyles.None,
            System.Globalization.CultureInfo.InvariantCulture, out var count) ? count : 0) + 1)
            .ToString(System.Globalization.CultureInfo.InvariantCulture));
        Set("ELAN_TOOLCHAIN", _ => Printed("ELAN_TOOLCHAIN"));
        Set("ELAN_HOME", _ => Printed("ELAN_HOME"));
    }

    /// <summary>The executable a bare `lake` command starts: the first one on this process's PATH.</summary>
    static string? LakeOnPath() =>
        (Environment.GetEnvironmentVariable("PATH") ?? "")
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Select(directory => Path.Combine(directory.Trim('"'), OperatingSystem.IsWindows() ? "lake.exe" : "lake"))
            .FirstOrDefault(File.Exists);

    static string LeanEnvironmentOverflow(string[] command, string cwd, EnvironmentEntry[] entries, int size,
        int limit)
    {
        var invariant = System.Globalization.CultureInfo.InvariantCulture;
        var largest = entries.OrderByDescending(entry => entry.Bytes).Take(LargestVariablesShown)
            .Select(entry => string.Create(invariant,
                $"\n  {entry.Name} {entry.Bytes:N0}{(entry.SetByLake ? " (set by Lake)" : "")}"));
        var doubled = entries.GroupBy(entry => entry.Name, StringComparer.OrdinalIgnoreCase)
            .Where(group => group.Count() > 1).Select(group => string.Join(" and ", group.Select(entry => entry.Name)))
            .Select(names => "\n" + names + " are both passed: Lean keeps an inherited spelling beside Lake's.");
        return string.Create(invariant, $"`{string.Join(' ', command.Take(2))}` in {cwd} would start Lean ") +
            string.Create(invariant, $"processes that pass on a {size:N0}-byte environment, over the ") +
            string.Create(invariant, $"{limit:N0}-byte limit ") +
            "of the environment Lean on Windows can pass to a process. Lean would drop LEAN_PATH and the other " +
            "variables set for it without an error, so imports would not resolve.\n" +
            "Largest variables (bytes of name=value):" +
            string.Concat(largest) + string.Concat(doubled) +
            "\nRemove unneeded variables or PATH entries from the environment leancil runs in.";
    }

    static SortedDictionary<string, string> Inputs(string proof, string? settings = null)
        => Inputs(CommonInputs(), proof, settings);

    static SortedDictionary<string, string> CommonInputs()
    {
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);

        foreach (var name in new[] { "lean-toolchain", "lake-manifest.json", "CIL.lean" })
            result[name] = Sha(At(name));
        // Checkout identities see every declaration; the certified library sees only what builds it.
        var lakefile = File.ReadAllBytes(At("lakefile.toml"));
        result[CheckoutLakefileInput] = Convert.ToHexStringLower(SHA256.HashData(lakefile));
        result["lakefile.toml"] = ContentKey(LibraryLakefile(Encoding.UTF8.GetString(lakefile)));

        var folders = new List<(string, string[])> { ("CIL", [".lean"]) };
#if !LEANCIL_TOOL
        // The repository's examples and tests are checkout inputs; the tool ships only the framework.
        foreach (var name in new[] { "global.json", "Directory.Build.props", "Directory.Packages.props", ".editorconfig" })
            result[name] = Sha(At(name));
        folders.AddRange([("Examples", [".lean"]), ("Tests", [".lean"]), ("Extractor", [".cs", ".csproj"]),
            ("scripts", [".cs"])]);
#endif

        foreach (var (folder, extensions) in folders)
            foreach (var path in Directory.EnumerateFiles(At(folder), "*", SearchOption.AllDirectories))
            {
                var relative = Path.GetRelativePath(Root, path).Replace('\\', '/');

                if (extensions.Contains(Path.GetExtension(path)) && !relative.Split('/').Any(p => p is "bin" or "obj"))
                    result[relative] = Sha(path);
            }

        return result;
    }

    /// <summary>The snapshot key of the complete checkout lakefile, which no certified library contains.</summary>
    const string CheckoutLakefileInput = "checkout:lakefile.toml";

    /// <summary>
    /// The lakefile the certified library is built from: the checkout's, without blank lines, comments,
    /// the editor library, or any plain <c>[[lean_lib]]</c> table that declares only a library outside CIL.
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
            LibraryName().Match(declaration) is { Success: true } match && match.Groups[1].Value is var name &&
            name != "CIL" && !name.StartsWith("CIL.", StringComparison.Ordinal) ? name : null;
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
    private static partial Regex LibraryName();

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

    // A failed download never becomes a cache entry. The package-pinned archive digest is checked
    // before extraction, then the producer manifest and full kernel replay authorize local reuse.
    bool DownloadReleasedLibrary(string cached, string key)
    {
#if LEANCIL_TOOL
        var descriptor = Path.Combine(Root, $"certified-library-release.{RuntimeInformation.RuntimeIdentifier}.json");
        if (!File.Exists(descriptor)) return false;
        var staging = cached + ".download-" + Guid.NewGuid().ToString("N");
        var archive = staging + ".zip";
        try
        {
            var asset = JsonSerializer.Deserialize<CertifiedReleaseAsset>(File.ReadAllBytes(descriptor));
            if (asset is null || !ValidReleaseAsset(asset, key)) return false;
            Console.Error.WriteLine("Downloading certified Lean verification library");
            using var client = new System.Net.Http.HttpClient { Timeout = TimeSpan.FromMinutes(3) };
            using var timeout = new CancellationTokenSource(TimeSpan.FromMinutes(3));
            var uri = new Uri("https://github.com/NethermindEth/LeanCIL/releases/download/" +
                Uri.EscapeDataString(asset.Tag) + "/" + Uri.EscapeDataString(asset.Archive));
            using var response = client.GetAsync(uri, System.Net.Http.HttpCompletionOption.ResponseHeadersRead,
                    timeout.Token)
                .GetAwaiter().GetResult();
            response.EnsureSuccessStatusCode();
            using (var input = response.Content.ReadAsStream(timeout.Token))
            using (var output = File.Create(archive))
            {
                var buffer = new byte[1024 * 1024];
                int count;
                while ((count = input.ReadAsync(buffer, timeout.Token).AsTask().GetAwaiter().GetResult()) != 0)
                {
                    if (output.Length + count > asset.ArchiveBytes)
                        throw new InvalidDataException("Released archive exceeds its package-pinned size");
                    output.Write(buffer, 0, count);
                }
            }
            InstallReleasedLibrary(archive, staging, cached, asset);
            return true;
        }
        catch (Exception error) when (error is IOException or InvalidDataException or UnauthorizedAccessException or
            JsonException or InvalidOperationException or System.Net.Http.HttpRequestException or OperationCanceledException)
        {
            Console.Error.WriteLine("Certified library download unavailable; building from sources. " +
                error.Message);
            return false;
        }
        finally
        {
            try { File.Delete(archive); }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
            try { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
        }
#else
        return false;
#endif
    }

    void InstallReleasedLibrary(string archive, string staging, string cached, CertifiedReleaseAsset asset)
    {
        var (key, _) = LibraryIdentity(CommonInputs());
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
        if (Directory.Exists(cached)) Directory.Delete(cached, true);
        Directory.Move(staging, cached);
    }

    static SortedDictionary<string, string> LibrarySources(SortedDictionary<string, string> snapshot) =>
        new(snapshot.Where(p => p.Key.StartsWith("CIL/", StringComparison.Ordinal) ||
            p.Key is "CIL.lean" or "lakefile.toml" or "lake-manifest.json" or "lean-toolchain").ToDictionary(), StringComparer.Ordinal);

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
    /// Fails if any file of the library this process reads in place differs, by length or write time, from when
    /// the library was opened: a build that wrote into it would otherwise pass for the certified bytes.
    /// </summary>
    void RequireUnchangedLibrary()
    {
        if (libraryStamps is null) return;
        foreach (var (name, stamp) in libraryStamps)
        {
            var file = new FileInfo(Path.Combine(library!, name));
            if (!file.Exists || FileStamp(file) != stamp)
                throw new InvalidOperationException("The certified library changed on disk during verification: " +
                    file.FullName);
        }
    }

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

    // Recency is last use: restoring or republishing an entry renews it.
    static void TouchSuccess(string entry)
    {
        try { Directory.SetLastWriteTimeUtc(entry, DateTime.UtcNow); }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
    }

    static readonly Regex SupportGeneration = new(@"^[0-9a-f]{64}-[0-9a-f]{64}$");
    static readonly Regex AbandonedStaging = new(@"^[0-9a-f]{64}(?:-[0-9a-f]{64})?\.(?:(?:invalid|evicted)-)?[0-9a-f]{32}$");
    static int supportEvicted;

    static TimeSpan SupportRetention => TimeSpan.FromDays(double.TryParse(Environment.GetEnvironmentVariable("LEANCIL_SUPPORT_RETENTION_DAYS"),
        System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out var days) && days > 0 ? days : 7);

    // Once per process, removes support generations unused for the retention period and staging
    // left by killed publishers. Only exact cache entry names directly under the root are touched.
    static void EvictStaleSupport()
    {
        if (Interlocked.Exchange(ref supportEvicted, 1) != 0) return;
        var now = DateTime.UtcNow;
        var root = new DirectoryInfo(SuccessCacheRoot);
        foreach (var entry in root.EnumerateDirectories())
        {
            var age = now - entry.LastWriteTimeUtc;
            if (entry.Attributes.HasFlag(FileAttributes.ReparsePoint) ||
                !(SupportGeneration.IsMatch(entry.Name) && age > SupportRetention ||
                  AbandonedStaging.IsMatch(entry.Name) && age > TimeSpan.FromDays(1)))
                continue;
            try
            {
                // Readers skip dotted names, so a renamed generation is never restored half-deleted.
                var doomed = entry.Name.Contains('.') ? entry.FullName
                    : Path.Combine(root.FullName, entry.Name + ".evicted-" + Guid.NewGuid().ToString("N"));
                if (doomed != entry.FullName) entry.MoveTo(doomed);
                Directory.Delete(doomed, true);
            }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
        }
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
        static bool Set(string variable) => string.Equals(Environment.GetEnvironmentVariable(variable), "true",
            StringComparison.OrdinalIgnoreCase);
        var fresh = freshLibrary || !editorLibrary && (Set("CI") || Set("GITHUB_ACTIONS"));
        var cacheRoot = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
            Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries");
        var cached = Path.Combine(cacheRoot, libraryKey);
        SortedDictionary<string, string> manifest;
        FileStream? cacheLock = null;
        try
        {
            if (!fresh)
            {
                Directory.CreateDirectory(cacheRoot);
                // Serialize same-key builders. A lock is released even after a crashed process.
                var deadline = Stopwatch.StartNew();
                while (cacheLock is null)
                {
                    try { cacheLock = new FileStream(cached + ".lock", FileMode.OpenOrCreate, FileAccess.ReadWrite, FileShare.None); }
                    catch (IOException) when (deadline.Elapsed < TimeSpan.FromMinutes(10)) { Thread.Sleep(100); }
                }
            }
            var supplied = Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY");
            var suppliedDigest = Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY_SHA256");
            // A supplied certified library is not a local cache, so --rebuild-library still uses it.
            if (!string.IsNullOrWhiteSpace(supplied))
            {
                var openStarted = DateTimeOffset.UtcNow;
                var openElapsed = Stopwatch.StartNew();
                library = Path.GetFullPath(supplied);
                manifest = SuppliedLibraryManifest(library, suppliedDigest, libraryKey, sources)
                    ?? throw new InvalidOperationException("Certified library identity or integrity mismatch");
                certifiedFingerprintsSha = manifest.GetValueOrDefault(CertifiedFingerprintsName);
                libraryBuild = "certified-artifact";
                Trace("Opening certified Lean verification library", openStarted, library, openElapsed.Elapsed, 0, "", [library]);
            }
            else if (!fresh && CertifiedLocalLibrary(cached, libraryKey) &&
                ReadManifest(cached) is { } cachedManifest && Same(sources, LibrarySources(cachedManifest)) &&
                (libraryStamps = HashedCacheEntry(cached, cachedManifest)) is not null)
            {
                // The receipt binds this manifest, and the entry's files still hash to it.
                library = cached;
                manifest = cachedManifest;
                libraryBuild = "cache";
            }
            else if (!fresh && DownloadReleasedLibrary(cached, libraryKey))
            {
                library = cached;
                manifest = ReadManifest(cached) ?? throw new InvalidDataException("Missing downloaded library manifest");
                libraryBuild = "release";
            }
            else if (!fresh && closureRoots is not null &&
                ClosureLibrary(cacheRoot, libraryKey, sources, closureRoots) is { } closure)
            {
                // The certificate names the closure's own key, which states exactly the modules replayed.
                (library, manifest, libraryKey, libraryModules) =
                    (closure.Directory, closure.Manifest, closure.Key, closure.Modules);
                libraryStamps = closure.Stamps;
                libraryBuild = closure.Built ? "closure" : "closure-cache";
            }
            else
            {
                library = Path.Combine(Path.GetTempPath(), "leancil-library-" + Guid.NewGuid().ToString("N"));
                ownsLibrary = true;
                Directory.CreateDirectory(library);
                if (incrementalLibrary is not null)
                    StageIncrementalLibrary(library, incrementalLibrary, incrementalDigest, sources);
                // Lake reuses a closure entry's modules by trace; every module is replayed below all the same.
                else if (!fresh && CachedClosure(cacheRoot, libraryKey) is { } built)
                    CopyTree(Path.Combine(built, ".lake", "build"), Path.Combine(library, ".lake", "build"));
                foreach (var (name, hash) in sources)
                {
                    var destination = Path.Combine(library, name);
                    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                    CopyLibrarySource(name, destination);
                    if (Sha(destination) != hash)
                        throw new InvalidOperationException("Library source changed while copying: " + name);
                }
                // Modules outside the CIL aggregate are built here too, so importing one never builds into a shared library.
                var frameworkModules = sources.Keys.Where(name => name.StartsWith("CIL/", StringComparison.Ordinal) &&
                    name.EndsWith(".lean", StringComparison.Ordinal)).Select(name => "+" + name[..^".lean".Length].Replace('/', '.'));
#if LEANCIL_TOOL
                Console.Error.WriteLine("Building the certified Lean verification library from the framework sources " +
                    "and kernel-replaying it; this takes several minutes. " + (fresh
                        ? "This run does not cache it."
                        : "Later runs reuse it from " + cached + "."));
#endif
                Run(["lake", "build", "CIL", "leancil-audit", .. frameworkModules], library, streamOutput: true,
                    progress: "Building fresh Lean verification library");
                // An incremental build replays donor modules too: an unchanged olean may import changed ones.
                ReplayLibrary(library, (incrementalLibrary is null ? "fresh" : "incremental") +
                    " Lean verification library");
                if (!Same(sources, LibrarySources(CommonInputs())))
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
                        if (Directory.Exists(cached)) Directory.Delete(cached, true);
                        Directory.Move(staging, cached);
                        publishedLibrary = cached;
                        RemoveClosure(cacheRoot, libraryKey);
                    }
                    finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
                }
            }
        }
        finally { cacheLock?.Dispose(); }
        const string compiledPrefix = ".lake/build/lib/lean/";
        // Lake compiles a dependency's missing modules into its own build directory, so a library
        // extended with uncompiled sources is read from a private copy; a complete one is never written.
        var incomplete = manifest.Keys.Any(name => name.StartsWith("CIL/", StringComparison.Ordinal) &&
            name.EndsWith(".lean", StringComparison.Ordinal) &&
            !manifest.ContainsKey(compiledPrefix + name[..^".lean".Length] + ".olean"));
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
        // Lake rebuilds a module it finds stale into the library; no build of this process may have done so.
        libraryStamps = ownsLibrary ? null : libraryStamps ?? FileStamps(library);
        baseModules = new(manifest.Where(pair => pair.Key.StartsWith(compiledPrefix, StringComparison.Ordinal) &&
                Path.GetFileName(pair.Key).Contains(".olean", StringComparison.Ordinal))
            .ToDictionary(pair => pair.Key[compiledPrefix.Length..], pair => pair.Value), StringComparer.Ordinal);
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
            foreach (Match import in SourceImport().Matches(read(ModuleSource(module))))
                if (IsFrameworkModule(import.Groups[1].Value)) pending.Enqueue(import.Groups[1].Value);
        }
        return [.. closure];
    }

    /// <summary>The key of the closure entry of the library `libraryKey` that holds exactly `modules`.</summary>
    static string ClosureKey(string libraryKey, string[] modules) => ContentKey(
        "leancil-library-closure-v1-these-modules-kernel-replayed\n" + libraryKey + "\n" + string.Join("\n", modules));

    /// <summary>Beside a library's cache entry: the key of the one closure entry built before the whole.</summary>
    static string ClosureRecord(string cacheRoot, string libraryKey) =>
        Path.Combine(cacheRoot, libraryKey + ".closure");

    /// <summary>
    /// Whether `manifest` describes a closure entry of exactly `modules`: their sources and the build
    /// configuration as in `sources`, no other framework source, and compiled modules for those and no other.
    /// </summary>
    static bool ClosureManifest(SortedDictionary<string, string> manifest, SortedDictionary<string, string> sources,
        string[] modules)
    {
        const string compiledPrefix = ".lake/build/lib/lean/";
        var expected = modules.Select(ModuleSource).Concat(LibraryConfiguration).ToHashSet(StringComparer.Ordinal);
        var compiled = manifest.Keys.Where(name => name.StartsWith(compiledPrefix, StringComparison.Ordinal) &&
                Path.GetFileName(name).Contains(".olean", StringComparison.Ordinal))
            .Select(name => ModuleName(name[compiledPrefix.Length..])).ToHashSet(StringComparer.Ordinal);
        return expected.SetEquals(LibrarySources(manifest).Keys) && compiled.SetEquals(modules) &&
            expected.All(name => sources.TryGetValue(name, out var hash) && manifest[name] == hash);
    }

    /// <summary>
    /// The directory of the closure entry recorded for the library `libraryKey`, when its receipt and files
    /// still authenticate it; null otherwise.
    /// </summary>
    string? CachedClosure(string cacheRoot, string libraryKey)
    {
        try
        {
            var key = File.ReadAllText(ClosureRecord(cacheRoot, libraryKey)).Trim();
            var directory = Path.Combine(cacheRoot, key);
            return Regex.IsMatch(key, @"\A[0-9a-f]{64}\z") && CertifiedLocalLibrary(directory, key) &&
                ReadManifest(directory) is { } manifest && HashedCacheEntry(directory, manifest) is not null
                ? directory : null;
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return null; }
    }

    /// <summary>Removes the closure entry recorded for a library whose whole entry is published.</summary>
    static void RemoveClosure(string cacheRoot, string libraryKey)
    {
        try
        {
            var record = ClosureRecord(cacheRoot, libraryKey);
            if (!File.Exists(record)) return;
            var key = File.ReadAllText(record).Trim();
            File.Delete(record);
            var directory = Path.Combine(cacheRoot, key);
            if (!Regex.IsMatch(key, @"\A[0-9a-f]{64}\z") || !Directory.Exists(directory)) return;
            // Renamed first, so a delete that stops halfway leaves no entry under the key.
            var doomed = directory + ".evicted-" + Guid.NewGuid().ToString("N");
            Directory.Move(directory, doomed);
            Directory.Delete(doomed, true);
        }
        // Another process may still read it; the whole library is preferred from now on regardless.
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
        if (File.Exists(record))
        {
            if (File.ReadAllText(record).Trim() != key) return null;
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
            if (!ClosureManifest(manifest, LibrarySources(CommonInputs()), modules))
                throw new InvalidDataException("Library sources changed during preparation");
            File.WriteAllText(Path.Combine(build, "cache-manifest.json"), JsonSerializer.Serialize(manifest, Json));
            var manifestBytes = File.ReadAllBytes(Path.Combine(build, "cache-manifest.json"));
            File.WriteAllBytes(Path.Combine(build, "cache-receipt.hmac"), HMACSHA256.HashData(ReceiptKey,
                Encoding.UTF8.GetBytes(key).Concat(manifestBytes).ToArray()));
            CopyTree(build, staging);
            if (Directory.Exists(directory)) Directory.Delete(directory, true);
            Directory.Move(staging, directory);
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
    /// A fresh package holding the given checkout sources and every non-CIL library of the checkout
    /// lakefile, with the base as a read-only path dependency. Lake writes only below this package.
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
    /// the library was opened with, plus any unrecorded output, which Lake builds into the base from an
    /// unrecorded source and must be replayed.
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
    /// A package named leancil whose only library is CIL, read in place from the certified library,
    /// so no other target of the certified lakefile can claim a requiring package's own modules.
    /// `requirements` are further lakefile tables, such as a package this one brings into the workspace.
    /// </summary>
    // Lake's module traces name the package, so under another name it rebuilds every module into the library.
    static string FrameworkPackage(string owner, string certified, string requirements = "")
    {
        var directory = Path.Combine(owner, ".lake", "leancil-framework");
        Directory.CreateDirectory(directory);
        var root = Path.GetFullPath(certified).Replace('\\', '/');
        WriteIfChanged(Path.Combine(directory, "lakefile.toml"),
            $"name = \"leancil\"\nsrcDir = {JsonSerializer.Serialize(root)}\nbuildDir = " +
            $"{JsonSerializer.Serialize(root + "/.lake/build")}\n\n[[lean_lib]]\nname = \"CIL\"\n" + requirements);
        WriteIfChanged(Path.Combine(directory, "lean-toolchain"), File.ReadAllText(Path.Combine(certified, "lean-toolchain")));
        return directory;
    }

    /// <summary>
    /// The certified library a package that outlives this process may require by path: the machine's cache
    /// entry, built and published first when absent, or a supplied library. Never a directory a process deletes.
    /// </summary>
    static string EditorLibrary()
    {
        if (editorLibraryDirectory is not null) return editorLibraryDirectory;
        using var verification = new Program { editorLibrary = true };
        verification.Library(Inputs(At("CIL.lean")));
        return editorLibraryDirectory = !verification.ownsLibrary ? verification.library!
            : verification.publishedLibrary ?? throw new InvalidOperationException(
                "The supplied certified library holds framework sources it has not compiled, so an editor " +
                "package cannot require it in place. Unset LEANCIL_CERTIFIED_LIBRARY to use this machine's " +
                "library cache.");
    }

    /// <summary>The directory <see cref="EditorLibrary"/> resolved, once per process.</summary>
    static string? editorLibraryDirectory;

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
                "The next leancil verify or workspace rehashes the library and replaces it if it changed.");
    }

    /// <summary>The lakefile requirement of a package below owner on the certified framework.</summary>
    // Relative, so equal sessions have equal configurations wherever their directories are.
    static string FrameworkRequirement(string owner, string certified) =>
        "\n[[require]]\nname = \"leancil\"\npath = " +
        JsonSerializer.Serialize(Path.GetRelativePath(owner, FrameworkPackage(owner, certified)).Replace('\\', '/')) + "\n";

    /// <summary>Declarations of every library in a lakefile except the framework's CIL and editor libraries.</summary>
    static string LibraryDeclarations(string lakefile) => string.Concat(
        Regex.Matches(File.ReadAllText(lakefile), @"^\[\[lean_lib\]\]\r?\nname = ""([^""]+)""", RegexOptions.Multiline)
            .Select(match => match.Groups[1].Value).Where(name => name is not ("CIL" or EditorLibraryName))
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
        var snapshot = Inputs(At("CIL.lean"));
        var (newKey, newSources) = LibraryIdentity(snapshot);
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
            if (!Same(newSources, LibrarySources(Inputs(At("CIL.lean")))))
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
        var (key, sources) = LibraryIdentity(CommonInputs());
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
        string[] compiled = [Path.GetFullPath(Path.Combine(session, ".lake/build/lib/lean")),
            Path.GetFullPath(Path.Combine(library!, ".lake/build/lib/lean"))];
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
                var path = Path.GetFullPath(dependency);
                if (path.StartsWith(Path.GetFullPath(Toolchain) + Path.DirectorySeparatorChar, StringComparison.OrdinalIgnoreCase)) continue;
                var name = compiled.Select(directory => Path.GetRelativePath(directory, path).Replace('\\', '/'))
                    .FirstOrDefault(candidate => !candidate.StartsWith("../", StringComparison.Ordinal) && !Path.IsPathRooted(candidate));
                if (name is null || !name.EndsWith(".olean", StringComparison.Ordinal)) return Conservative();
                var imported = name[..^6].Replace('/', '.');
                // All certified CIL sources are already bound by libraryKey.
                if (imported != "CIL" && !imported.StartsWith("CIL.", StringComparison.Ordinal)) pending.Enqueue(imported);
                else if (!certifiedModules!.ContainsKey(name)) pending.Enqueue(imported);
            }
        }
        supportSourceKeys[rootKey] = result;
        return result;

        SortedDictionary<string, string> Conservative() => new(snapshot.Where(pair =>
            pair.Key.EndsWith(".lean", StringComparison.Ordinal) && !pair.Key.StartsWith("proof:", StringComparison.Ordinal)).ToDictionary(), StringComparer.Ordinal);
    }

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

    static string ExtractorPath =>
#if LEANCIL_TOOL
        typeof(Program).Assembly.Location;
#else
        At("Extractor/bin/Nethermind.LeanCIL.dll");
#endif

    // Read the module name, not the whole line: a trailing comment does not change an import.
    // Shared by standalone proofs and consumer dependency traversal.
    [GeneratedRegex(@"^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([A-Za-z_][A-Za-z0-9_'.]*)(?=[ \t]*(?:--|/-|\r?$))", RegexOptions.Multiline)]
    private static partial Regex SourceImport();

    // Proofs opt in to PDB names and locations with `import ExtractedSymbols` or its keyed form.
    static bool ImportsSymbols(string proof) => SourceImport().Matches(proof).Any(import =>
        import.Groups[1].Value is var module && (module == "ExtractedSymbols" || SelectionModules.IsSymbols(module)));

    static string SymbolsFor(string output) => Path.Combine(output, "Symbols.lean") is var path && File.Exists(path) ? path
        : throw new InvalidOperationException(MissingSymbols(output));

    static string MissingSymbols(string output)
    {
        var identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
        return "The proof imports ExtractedSymbols, but extraction found no matching portable PDB; build the assembly with its .pdb next to it and extract again, or remove the import.\n" +
            "  Assembly: " + Path.GetFullPath(identity.GetProperty("assemblyPath").GetString()!, output) + "\n" +
            "  Method: " + identity.GetProperty("entry").GetString();
    }

    // Inside the extractor, its own commands run in this process instead of starting another runtime.
    static void RunExtractor(string[] command)
    {
#if LEANCIL_TOOL
        if (command is ["dotnet", var path, .. var arguments] && path == ExtractorPath)
        {
            Nethermind.LeanCIL.Program.RunQuietly(arguments);
            return;
        }
#endif
        Run(command);
    }

    static string[] Extract(string mode, string assembly, string? identity, string entry, string output, string profile = "scalar") =>
        ["dotnet", ExtractorPath, mode, assembly, entry, output, profile,
            .. identity is null ? Array.Empty<string>() : ["--assembly", identity]];

    sealed record GeneratedExtraction(string Assembly, string Entry, string Output, string Profile = "scalar",
        string[]? InitializedTypes = null, string[]? TypeArguments = null);

    // Share immutable assembly bytes and signature validation, retaining fresh modules per request
    // and the extractor's final check that every assembly, symbol and profile input is unchanged.
    static void ExtractBatch(string mode, string? identity, IEnumerable<GeneratedExtraction> requests,
        string? extractor = null)
    {
        var path = Path.Combine(Path.GetTempPath(), "leancil-extractions-" + Guid.NewGuid().ToString("N") + ".json");
        try
        {
            File.WriteAllText(path, JsonSerializer.Serialize(requests.Select(request => new
            {
                assembly = request.Assembly, identity, entry = request.Entry, output = request.Output,
                profile = request.Profile, initializedTypes = request.InitializedTypes,
                typeArguments = request.TypeArguments
            })));
            Run(["dotnet", extractor ?? ExtractorPath, "generated-extraction-batch", mode, path]);
        }
        finally { File.Delete(path); }
    }

    // This module imports only the extracted program, never the user proof. The audit
    // checks its compiled theorem against the complete validator application for that
    // program; a declaration with the right name but type True is insufficient.
    const string ExtractionAuditSource = """
        import Extracted
        run_cmd do
          match (← Lean.getEnv).find? `Extracted.translation_valid with
          | some (.thmInfo _) => pure ()
          | _ => throwError "Expected extraction certificate theorem"
        theorem ExtractionAudit.valid :
            CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
              Extracted.methodEvidence Extracted.imports Extracted.program := Extracted.translation_valid
        #print Extracted.imports
        """;

    static readonly string[] ApprovedAxioms = ["propext", "Quot.sound", "Classical.choice"];

    sealed record AuditRequest(string name, object? type = null, string[]? axioms = null,
        bool statement = false, bool refutation = false, string[]? allowedModules = null);
    sealed record AuditRefutation(string contract, int line, int column);
    sealed record AuditedTheorem(string name, string? error, string[]? axioms, string? statement, AuditRefutation? refutes);
    sealed record AuditConstantRequest(string name, object value, object? type = null, string[]? axioms = null);
    sealed record AuditedInterfaces(string? error);
    sealed record AuditedClosure(string name, string? error, string? kind, string? canonical);
    sealed record AuditNamespaces(string[] prefixes, string[] axioms);
    sealed record AuditedNamespaces(int count, Dictionary<string, int> prefixes, Dictionary<string, int> modules, string[] axioms,
        AuditedTheorem[] rejected, string? error);
    sealed record AuditedOleans(Dictionary<string, string> modules, AuditedTheorem[] theorems, AuditedTheorem[] constants,
        AuditedInterfaces? interfaces = null, AuditedClosure[]? closures = null, AuditedNamespaces? namespaces = null,
        string[]? replayed = null, bool? fused = null);

    static readonly JsonSerializerOptions AuditJson = new() { DefaultIgnoreCondition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull };

    static object AuditConstant(string name) => new { @const = name };

    // The certificate must prove the validator for exactly the emitted tables and program.
    static AuditRequest ExtractionCertificate(string theorem, string prefix = "") => new(theorem,
        new { app = new[] { AuditConstant("CIL.Extraction.TranslationValid") }.Concat(
            new[] { "rawLayouts", "computedLayouts", "methodEvidence", "imports", "program" }.Select(name => AuditConstant(prefix + "Extracted." + name))) },
        ApprovedAxioms);

    static AuditRequest ProofTheorem(string theorem) => new(theorem, axioms: ApprovedAxioms, statement: true, refutation: true);

    string? auditExecutable;
    string? auditExecutableSha;

    string CheckedAuditExecutable()
    {
        // The manifest bound this executable's hash when the library was validated.
        if (auditExecutable is null || auditExecutableSha is null || !File.Exists(auditExecutable))
            throw new InvalidOperationException("Theorem audit executable is missing");
        return auditExecutable;
    }

    // Reads the kernel-replayed oleans only: no imported elaborator, notation, extension or initializer runs.
    AuditedOleans AuditOleans(string leanPath, string[] modules, AuditRequest[] theorems, AuditConstantRequest[]? constants = null,
        string[]? interfaces = null, string[]? closures = null, AuditNamespaces? namespaces = null,
        string[]? replayTargets = null, string? replayProgress = null)
    {
        var executable = CheckedAuditExecutable();
        var request = Path.Combine(Path.GetTempPath(), "leancil-audit-" + Guid.NewGuid().ToString("N") + ".json");
        var result = Path.ChangeExtension(request, ".result.json");
        try
        {
            constants ??= [];
            interfaces ??= [];
            closures ??= [];
            File.WriteAllText(request, JsonSerializer.Serialize(new { modules, theorems, constants, interfaces,
                closures = closures.Select(name => new { name }), namespaces, replayTargets }, AuditJson));
            Run([executable, request, result], leanPath: leanPath, environment: LeanEnvironment,
                progress: replayTargets is null ? null :
                    replayProgress ?? "Joint kernel replay of consumer proof and dependencies");
            CheckedAuditExecutable();
            var audited = JsonSerializer.Deserialize<AuditedOleans>(File.ReadAllText(result))
                ?? throw new InvalidDataException("Missing theorem audit result");
            if (audited.theorems.Length != theorems.Length || audited.theorems.Zip(theorems).Any(pair => pair.First.name != pair.Second.name) ||
                audited.constants.Length != constants.Length || audited.constants.Zip(constants).Any(pair => pair.First.name != pair.Second.name) ||
                modules.Any(module => !audited.modules.ContainsKey(module)) || audited.interfaces is null || audited.closures is null ||
                audited.closures.Length != closures.Length || audited.closures.Zip(closures).Any(pair => pair.First.name != pair.Second) ||
                (namespaces is not null && (audited.namespaces?.prefixes is null || audited.namespaces.modules is null ||
                    audited.namespaces.axioms is null || audited.namespaces.rejected is null)) ||
                (replayTargets is not null && (audited.replayed is null || audited.fused is null ||
                    !audited.replayed.SequenceEqual(replayTargets))))
                throw new InvalidDataException("Incomplete theorem audit result");
#if !LEANCIL_TOOL
            if (replayTargets is not null)
                Console.WriteLine(JsonSerializer.Serialize(new { auditFused = audited.fused, modules }));
#endif
            return audited;
        }
        finally { File.Delete(request); File.Delete(result); }
    }

    // The audited module must be the artifact that was hashed and replayed, not a shadow on the search path.
    static void RequireAuditedModule(AuditedOleans audited, string module, string path)
    {
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        if (!Path.GetFullPath(audited.modules[module]).Equals(Path.GetFullPath(path), comparison))
            throw new InvalidDataException($"Audited module {module} resolved to {audited.modules[module]}, not {path}");
    }

    static void RequireAuditedConstants(AuditedOleans audited)
    {
        foreach (AuditedTheorem constant in audited.constants)
            if (constant.error is not null) throw new InvalidOperationException(constant.error);
    }

    static string[] AuditedAxioms(AuditedTheorem audited)
    {
        if (audited.error is not null) throw new InvalidOperationException(audited.error);
        var axioms = audited.axioms ?? throw new InvalidDataException("Missing transitive theorem axiom audit");
        if (axioms.Any(a => !ApprovedAxioms.Contains(a)))
            throw new InvalidOperationException("Unapproved proof axioms: " + string.Join(", ", axioms));
        return axioms;
    }

    // Names the drivers generate or resolve from the toolchain and framework. Case variants collide on Windows and macOS.
    internal static class ContractModules
    {
        static readonly string[] ReservedRoots = ["CIL", "Lean", "Init", "Std", "Lake", "Extracted", "ExtractedImports", "Proof", "Audit",
            "ExtractionAudit", "ExtractedSymbols", "Symbols", "Examples", "Tests", "lakefile"];

        internal static bool Name(string? value) => value is not null && !value.Split('.').Contains("_root_", StringComparer.Ordinal) &&
            Regex.IsMatch(value, @"\A[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\z");

        internal static bool Interface(string? value) => Name(value) && value!.Split('.')[0] is var root &&
            !ReservedRoots.Contains(root, StringComparer.OrdinalIgnoreCase) && !root.StartsWith("LeanCIL", StringComparison.OrdinalIgnoreCase);
    }

    /// <summary>
    /// `Extracted.KEY` and `ExtractedSymbols.KEY` name one method's extraction, so proofs of different methods
    /// share a package. Verification builds each as a re-export of the extraction it checks: a key selects
    /// which extraction a proof expects, never what is certified.
    /// </summary>
    internal static class SelectionModules
    {
        const int DigestLength = 8;

        /// <summary>
        /// The key of the extraction `identity` describes: the method's type and name, then a digest of the
        /// assembly name, entry, profile name and initialization assumptions. Rebuilds and versions keep it.
        /// </summary>
        internal static string Key(JsonElement identity)
        {
            var assembly = identity.GetProperty("assemblyIdentity").GetString()!.Split(',')[0].Trim();
            var entry = identity.GetProperty("entry").GetString()!;
            var profile = identity.GetProperty("profile").GetProperty("Name").GetString()!;
            string[] initialized = identity.TryGetProperty("initializedTypes", out var types)
                ? [.. types.EnumerateArray().Select(type => type.GetString()!)] : [];
            var digest = ContentKey(string.Join("\n", [assembly, entry, profile, .. initialized]))[..DigestLength];
            var member = entry[..entry.IndexOf('(')];
            member = member[(member.LastIndexOf(' ') + 1)..];
            var type = member[..member.IndexOf("::", StringComparison.Ordinal)];
            type = type.Split('<')[0];
            type = type[(type.LastIndexOfAny(['.', '/']) + 1)..];
            var readable = Regex.Replace(type + "_" + member[(member.IndexOf("::", StringComparison.Ordinal) + 2)..],
                "[^A-Za-z0-9_]", "_");
            return (char.IsAsciiLetter(readable[0]) ? "" : "M") + readable + "_" + digest;
        }

        /// <summary>Whether `module` names a keyed extraction module rather than a source of the package.</summary>
        internal static bool Is(string module) =>
            module.StartsWith("Extracted.", StringComparison.Ordinal) ||
            module.StartsWith("ExtractedSymbols.", StringComparison.Ordinal);

        internal static bool IsSymbols(string module) =>
            module.StartsWith("ExtractedSymbols.", StringComparison.Ordinal);

        /// <summary>The source of a keyed module: the plain module it stands for, so it adds no declaration.</summary>
        internal static string Source(string module) =>
            "import " + (IsSymbols(module) ? "ExtractedSymbols" : "Extracted") + "\n";

        /// <summary>
        /// The keyed modules `imports` names, after rejecting a key of another extraction: a proof written for one
        /// method must not be checked against another one's program.
        /// </summary>
        internal static string[] Selected(IEnumerable<string> imports, JsonElement identity, string source)
        {
            var key = Key(identity);
            var selected = imports.Where(Is).Distinct(StringComparer.Ordinal).ToArray();
            foreach (var module in selected)
                if (module != "Extracted." + key && module != "ExtractedSymbols." + key)
                    throw new InvalidDataException(source + " imports " + module +
                        ", which names another extraction. This extraction of " +
                        identity.GetProperty("entry").GetString() + " under the " +
                        identity.GetProperty("profile").GetProperty("Name").GetString() + " profile is Extracted." +
                        key + "; import that, or select the method the proof was written for.");
            return selected;
        }
    }

    // One read of identity.json and of the import sources it pins; staging, keys and reports all derive from it.
    internal sealed record ExtractionIdentity(string Output, string Sha256, JsonElement Root, SortedDictionary<string, string> Sources)
    {
        internal JsonElement[] Imports => Root.TryGetProperty("imports", out JsonElement imports) ? [.. imports.EnumerateArray()] : [];
        internal JsonElement[] Graph => Root.TryGetProperty("importGraph", out JsonElement graph) ? [.. graph.EnumerateArray()] : [];

        internal static string Resolve(string output, string recorded) => Path.GetFullPath(recorded, output);

        internal static ExtractionIdentity Read(string output)
        {
            byte[] bytes = File.ReadAllBytes(Path.Combine(output, "identity.json"));
            JsonElement root = JsonSerializer.Deserialize<JsonElement>(bytes);
            SortedDictionary<string, string> sources = new(StringComparer.Ordinal);
            if (root.TryGetProperty("importModules", out JsonElement modules))
                foreach (JsonProperty module in modules.EnumerateObject())
                {
                    if ((module.Name != "ExtractedImports" && !ContractModules.Interface(module.Name)) ||
                        sources.Keys.Any(name => string.Equals(name, module.Name, StringComparison.OrdinalIgnoreCase)))
                        throw new InvalidDataException("Invalid imported interface module: " + module.Name);
                    string source = File.ReadAllText(Path.Combine(output, module.Name.Replace('.', Path.DirectorySeparatorChar) + ".lean"));
                    if (ContentKey(source) != module.Value.GetString()) throw new InvalidDataException("Imported interface source hash mismatch: " + module.Name);
                    sources.Add(module.Name, source);
                }
            return new(output, Convert.ToHexStringLower(SHA256.HashData(bytes)), root, sources);
        }
    }

    Dictionary<string, string[]> ContractModuleImports(string destination, SortedDictionary<string, string> sources)
    {
        string input = Path.Combine(destination, "LeanCILHeader" + Guid.NewGuid().ToString("N") + ".json");
        string runner = Path.ChangeExtension(input, ".lean");
        try
        {
            File.WriteAllText(input, JsonSerializer.Serialize(sources.Values));
            string result;
            if (auditExecutable is null)
            {
                // Editor workspaces parse headers before a certified library exists.
                File.WriteAllText(runner, File.ReadAllText(At("CIL/Interface/Headers.lean")) +
                    "\ndef main (args : List String) : IO Unit := do\n" +
                    "  let [input] := args | throw (IO.userError \"Expected source manifest\")\n" +
                    "  CIL.Interface.writeSourceHeaders input\n");
                result = Run([LeanExecutable, "--run", runner, input], destination, environment: LeanEnvironment);
            }
            else
            {
                var executable = CheckedAuditExecutable();
                result = Run([executable, "--headers", input], destination, environment: LeanEnvironment);
                CheckedAuditExecutable();
            }
            string[] lines = result.Split('\n', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
            if (lines.Length != sources.Count) throw new InvalidDataException("Incomplete contract interface import graph.");
            return sources.Keys.Zip(lines).ToDictionary(pair => pair.First,
                pair => JsonSerializer.Deserialize<string[]>(pair.Second) ?? throw new InvalidDataException("Invalid contract import graph."), StringComparer.Ordinal);
        }
        finally { File.Delete(input); File.Delete(runner); }
    }
    string[] StageImportSources(ExtractionIdentity extraction, string destination)
    {
        SortedDictionary<string, string> sources = extraction.Sources;
        if (sources.Count == 0) return [];
        Dictionary<string, string[]> dependencies = ContractModuleImports(destination, sources);
        foreach ((string module, string[] imports) in dependencies)
            if (module != "ExtractedImports")
                foreach (string dependency in imports)
                    if ((!sources.ContainsKey(dependency) || dependency == "ExtractedImports") && !TrustedContractModule(dependency))
                        throw new InvalidDataException("Undeclared contract interface dependency: " + dependency);
        List<string> ordered = [];
        HashSet<string> complete = new(StringComparer.Ordinal);
        HashSet<string> active = new(StringComparer.Ordinal);
        void Stage(string module)
        {
            if (complete.Contains(module)) return;
            if (!active.Add(module)) throw new InvalidDataException("Cyclic contract interface module imports: " + module);
            foreach (string dependency in dependencies[module])
                if (sources.ContainsKey(dependency)) Stage(dependency);
            string path = Path.Combine(destination, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
            if (File.Exists(path)) throw new InvalidDataException("Contract interface module shadows an existing source: " + module);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, sources[module], new UTF8Encoding(false));
            active.Remove(module);
            ordered.Add(module);
            complete.Add(module);
        }
        foreach (string module in sources.Keys) Stage(module);
        return ordered.ToArray();
    }

    static SortedDictionary<string, string> ContractInterfaceArtifacts(string directory, string[] modules)
    {
        if (modules.Length == 0) return new(StringComparer.Ordinal);
        HashSet<string> names = new(modules, StringComparer.Ordinal);
        var artifacts = HashFiles(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
            .Select(path => (Relative: Path.GetRelativePath(directory, path).Replace('\\', '/'), Path: path))
            .Where(artifact => names.Contains(ModuleName(artifact.Relative)))
            .Select(artifact => (artifact.Relative, artifact.Path)));
        foreach (string module in modules)
            if (!artifacts.ContainsKey(module.Replace('.', '/') + ".olean"))
                throw new InvalidDataException("Published contract interface artifact is missing: " + module);
        return artifacts;
    }

    static void RequireContractInterfaceArtifacts(string directory, string[] modules,
        SortedDictionary<string, string> accepted)
    {
        if (!Same(accepted, ContractInterfaceArtifacts(directory, modules)))
            throw new InvalidDataException("Published contract interface artifacts changed after their closure audit.");
    }

    bool TrustedContractModule(string module) =>
        ((module == "CIL" || module.StartsWith("CIL.", StringComparison.Ordinal)) && File.Exists(At(module.Replace('.', '/') + ".lean"))) ||
        File.Exists(Path.Combine(Toolchain, "lib/lean", module.Replace('.', '/') + ".olean"));

    // Validation and closures come from leancil-audit on replayed oleans, so interface code cannot forge them.
    bool TryReplayContractInterfaces(ExtractionIdentity extraction, string[] modules, string leanPath,
        Func<string, string> artifact)
    {
        if (!modules.Any(module => module != "ExtractedImports") ||
            Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") == "true") return false;
        try
        {
            CheckContractInterfaces(extraction, modules, leanPath, artifact, replayTargets: modules);
            return true;
        }
        // Duplicate declarations and replay failures retain the independent checker diagnostics.
        catch (InvalidOperationException) { return false; }
    }

    void CheckContractInterfaces(ExtractionIdentity extraction, string[] modules, string leanPath,
        Func<string, string> artifact, string[]? replayTargets = null)
    {
        string[] interfaces = modules.Where(module => module != "ExtractedImports").ToArray();
        JsonElement[] imports = extraction.Imports;
        if (interfaces.Length == 0 && imports.Length == 0) return;
        if (interfaces.Length == 0) throw new InvalidDataException("Contract imports without a published interface module");
        string[] constants = imports.Select(import => import.GetProperty("contractConstant").GetString()!).Distinct(StringComparer.Ordinal).ToArray();
        AuditedOleans audited = AuditOleans(leanPath, interfaces, [], interfaces: interfaces, closures: constants,
            replayTargets: replayTargets);
        foreach (string module in interfaces) RequireAuditedModule(audited, module, artifact(module));
        if (audited.interfaces?.error is { } invalid) throw new InvalidDataException(invalid);
        Dictionary<string, AuditedClosure> closures = audited.closures!.ToDictionary(closure => closure.name, StringComparer.Ordinal);
        foreach (JsonElement import in imports)
        {
            string constant = import.GetProperty("contractConstant").GetString()!;
            AuditedClosure closure = closures[constant];
            if (closure.error is not null) throw new InvalidDataException(closure.error);
            if (ContentKey(closure.canonical!) != import.GetProperty("closureDigest").GetString())
                throw new InvalidDataException("Published contract canonical closure digest mismatch: " + constant);
            if (closure.kind != import.GetProperty("contractKind").GetString())
                throw new InvalidDataException("Published contract canonical type mismatch: " + constant);
        }
    }

    static JsonElement[] ImportedBindings(string output) => ExtractionIdentity.Read(output).Imports;

    static JsonElement[] ImportGraph(string output) => ExtractionIdentity.Read(output).Graph;

    // acceptedVia and sourceBundleDigest name a node whose export forced full verification re-checked.
    sealed record DeploymentDependency(string assemblyIdentity, string implementationSha256, string interfaceDigest,
        string[] dependencies, bool conditional,
        [property: System.Text.Json.Serialization.JsonIgnore(
            Condition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull)]
        string? acceptedVia = null,
        [property: System.Text.Json.Serialization.JsonIgnore(
            Condition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull)]
        string? sourceBundleDigest = null);

    static DeploymentDependency[] DeploymentDependencies(JsonElement identity) =>
        identity.TryGetProperty("importGraph", out JsonElement graph) ? graph.EnumerateArray().Select(node =>
            new DeploymentDependency(node.GetProperty("assemblyIdentity").GetString()!,
                node.GetProperty("implementationSha256").GetString()!, node.GetProperty("interfaceDigest").GetString()!,
                node.GetProperty("dependencies").EnumerateArray().Select(dependency => dependency.GetProperty("assemblyIdentity").GetString()!).ToArray(),
                node.GetProperty("dependencies").GetArrayLength() > 0)).ToArray() : [];

    static bool ReferenceOnlyImports(ExtractionIdentity extraction) =>
        extraction.Imports.Any(import => import.GetProperty("isReferenceAssembly").GetBoolean()) ||
        extraction.Graph.Any(node => node.GetProperty("isReferenceAssembly").GetBoolean());

    static void RequireImplementationImports(ExtractionIdentity extraction)
    {
        if (ReferenceOnlyImports(extraction))
            throw new InvalidDataException("Reference-only contract input: caller proof checked for authoring only; no verification report or success receipt is certified.");
    }

    static string SemanticExtractionIdentity(ExtractionIdentity extraction)
    {
        JsonElement identity = extraction.Root;
        JsonElement[] graph = extraction.Graph;
        return ContentKey(JsonSerializer.Serialize(new
        {
            assembly = identity.GetProperty("assemblySha256"), generated = identity.GetProperty("generatedSha256"),
            profile = identity.GetProperty("profile"), interfaces = extraction.Sources,
            dependencyGraph = graph.Any(node => node.GetProperty("dependencies").GetArrayLength() > 0) ? graph.Select(node => new
            {
                assemblyIdentity = node.GetProperty("assemblyIdentity"), implementationSha256 = node.GetProperty("implementationSha256"),
                interfaceDigest = node.GetProperty("interfaceDigest"), dependencies = node.GetProperty("dependencies")
            }).ToArray() : [],
            imports = extraction.Imports.Select(import => new
            {
                slot = import.GetProperty("slot"), identity = import.GetProperty("identity"),
                profile = import.GetProperty("profile"), interfaceDigest = import.GetProperty("interfaceDigest"),
                closureDigest = import.GetProperty("closureDigest"), constant = import.GetProperty("contractConstant"),
                kind = import.GetProperty("contractKind"), staticIdentities = import.GetProperty("staticIdentities")
            })
        }));
    }

    // Certification fields are sidecar text outside every pinned digest; sidecarSha256 names the bytes they came from.
    sealed record PublishedImport(int slot, string identity, string profile, string implementationSha256,
        string interfaceDigest, string acceptedVia, string certificationTheorem, string certificationStatement,
        string certificationStatementDigest, JsonElement staticIdentities, string deploymentObligation,
        string? sidecarSha256 = null, bool certificationAuthenticated = false, string? sourceBundleDigest = null,
        JsonElement? typedSignature = null, JsonElement? layouts = null, string[]? typeArguments = null,
        JsonElement[]? initializationAssumptions = null);

    static PublishedImport[] PublishedImports(JsonElement extraction) => extraction.TryGetProperty("imports", out JsonElement imports)
        ? imports.EnumerateArray().Select(import => new PublishedImport(import.GetProperty("slot").GetInt32(),
            import.GetProperty("identity").GetString()!, import.GetProperty("profile").GetString()!,
            import.GetProperty("implementationSha256").GetString()!, import.GetProperty("interfaceDigest").GetString()!,
            "published-certification", import.GetProperty("certificationTheorem").GetString()!,
            import.GetProperty("certificationStatement").GetString()!, import.GetProperty("certificationStatementDigest").GetString()!,
            import.GetProperty("staticIdentities"),
            "This conditional caller proof is not a deployment guarantee: an unsatisfiable imported contract can make it vacuous. " +
            "Deployment must use these exact implementation bytes and discharge the published contract at this identity, signature and profile. " +
            "Published interface sources execute code with verifier permissions during compilation.",
            sidecarSha256: import.GetProperty("sidecarSha256").GetString()!,
            typedSignature: import.TryGetProperty("typedSignature", out JsonElement typed) ? typed : null,
            layouts: import.TryGetProperty("publishedLayouts", out JsonElement layouts) ? layouts : null,
            typeArguments: import.TryGetProperty("typeArguments", out JsonElement arguments) ? arguments.Deserialize<string[]>() : null,
            initializationAssumptions: InitializationAssumptions(import))).ToArray()
        : [];

    static bool HasContractImports(ExtractionIdentity extraction) =>
        extraction.Sources.ContainsKey("ExtractedImports") == (extraction.Imports.Length > 0) ? extraction.Imports.Length > 0
            : throw new InvalidDataException("Contract import slots and the generated import premise disagree");

    // With imports, only a claim conditional on exactly the generated import premise is certified.
    static AuditRequest ProofTheorem(string theorem, ExtractionIdentity extraction) => !HasContractImports(extraction) ? ProofTheorem(theorem)
        : ProofTheorem(theorem) with { type = new { app = new object[] { AuditConstant("CIL.Safety.HoldsGiven"),
            AuditConstant("Extracted.program"), AuditConstant("Extracted.ImportsHold"), "_" } } };

    // The premise is rebuilt from identity.json: each slot's root contract at its canonical numeral, so
    // interface instances, notation or shadowing namespaces cannot retarget or weaken it.
    static AuditConstantRequest[] ImportPremise(ExtractionIdentity extraction)
    {
        if (!HasContractImports(extraction)) return [];
        int methods = extraction.Root.GetProperty("methods").GetArrayLength();
        object[] slots = [.. extraction.Imports.Select(import => (object)new { app = new object[] {
            AuditConstant("CIL.Safety." + (import.GetProperty("contractKind").GetString() == "method" ? "MethodContract" : "OutcomeContract") + ".Holds"),
            "_", "_", AuditConstant(import.GetProperty("contractConstant").GetString()!), new { bvar = 0 },
            new { nat = methods + import.GetProperty("slot").GetInt32() } } })];
        object body = slots.Length == 0 ? AuditConstant("True")
            : slots.SkipLast(1).Reverse().Aggregate(slots[^1], (rest, slot) => new { app = new[] { AuditConstant("And"), slot, rest } });
        object program = AuditConstant("CIL.Program");
        return [new("Extracted.ImportsHold", new { lam = new[] { program, body } }, new { forall = new[] { program, new { sort = 0 } } })];
    }

    static string[] ContractImportAssumptions(JsonElement extraction) =>
        extraction.TryGetProperty("imports", out JsonElement imports) ? imports.EnumerateArray().Select(import =>
            "_root_.CIL.Safety." + (import.GetProperty("contractKind").GetString() == "method" ? "MethodContract" : "OutcomeContract") +
            ".Holds _root_." + import.GetProperty("contractConstant").GetString() + " linked " +
            (extraction.GetProperty("methods").GetArrayLength() + import.GetProperty("slot").GetInt32())).ToArray() : [];

    // Keeps the `#check` and `#print axioms` text shape that statement display and refutation reports read.
    static string AuditText(AuditedTheorem audited) => (audited.statement is null ? "" : audited.statement + "\n") +
        (audited.axioms is not { Length: > 0 } axioms ? $"'{audited.name}' does not depend on any axioms"
            : $"'{audited.name}' depends on axioms: [{string.Join(", ", axioms)}]") + "\n" +
        (audited.refutes is { } refutes ? $"LeanCIL refutes: {refutes.contract} at {refutes.line}:{refutes.column}\n" : "");

    /// <summary>An informational or warning message Lean reported while checking the selected proof.</summary>
    internal sealed record ProofMessage(string severity, int line, int column, string text);

    /// <summary>A method that a verified statement names through a framework predicate.</summary>
    internal sealed record StatementSubject(string role, string head, bool extracted, int? method, string? signature);

    /// <summary>A definition of the proof module as Lean prints it: `def name binders : type := body`.</summary>
    internal sealed record StatementDefinition(string name, string text);

    /// <summary>
    /// A verified statement as framework notation prints it, the methods it names and the proof module's
    /// definitions it is stated with, each before the ones its body uses; null when they were not read.
    /// </summary>
    internal sealed record StatementView(string statement, StatementSubject[] subjects,
        StatementDefinition[]? definitions = null);

    /// <summary>
    /// Set by callers that print <see cref="VerifiedStatement"/>; printing costs one Lean run beside the audit.
    /// </summary>
    bool viewsStatement { get; init; }

    /// <summary>
    /// Set by callers that read failure records: the proof is checked as <see cref="ObservedProof"/> with
    /// <see cref="DiagnosticsOption"/>, so each failure of a LeanCIL tactic is logged as a record after
    /// <see cref="FailureMarker"/>. The observer reads the elaborated proof and changes no proof term.
    /// </summary>
    bool structuredFailures { get; init; }

    /// <summary>The Lean option `cil.diagnostics`, which `CIL.Observe` reads.</summary>
    internal const string DiagnosticsOption = "-Dweak.cil.diagnostics=true";

    /// <summary>`CIL.Safety.failureMarker`, which starts each failure record the observer logs.</summary>
    internal const string FailureMarker = "[LeanCIL failure v1] ";

    /// <summary>
    /// Set by callers that print each step the proof takes: the proof is checked as <see cref="ObservedProof"/>
    /// with <see cref="TraceOption"/>.
    /// </summary>
    bool tracesSteps { get; init; }

    /// <summary>The Lean option tracing each step of the proof, as `[CIL.step]` messages of `CIL.Observe`.</summary>
    internal const string TraceOption = "-Dweak.trace.CIL.step=true";

    /// <summary>The start of a message of the `CIL.step` trace class.</summary>
    internal const string TraceHeader = "[CIL.step]";

    /// <summary>
    /// Set by callers that print open goals: the proof is checked as <see cref="ObservedProof"/> with
    /// <see cref="GoalsOption"/>, so the goal at each `sorry` and failing tactic is logged after
    /// <see cref="GoalMarker"/>.
    /// </summary>
    bool showsGoals { get; init; }

    /// <summary>The Lean option `cil.goals`, which `CIL.Observe` reads.</summary>
    internal const string GoalsOption = "-Dweak.cil.goals=true";

    /// <summary>`CIL.Safety.goalMarker`, which starts each open goal the observer logs.</summary>
    internal const string GoalMarker = "[LeanCIL goal v1] ";

    /// <summary>Whether the proof is checked as <see cref="ObservedProof"/>: records, a trace and goals need it.
    /// </summary>
    bool ObservesProof => structuredFailures || tracesSteps || showsGoals;

    /// <summary>The options the proof module is checked with: none unless asked for records, a trace or goals.
    /// </summary>
    string[] ProofOptions => [.. structuredFailures ? [DiagnosticsOption] : Array.Empty<string>(),
        .. tracesSteps ? [TraceOption] : Array.Empty<string>(), .. showsGoals ? [GoalsOption] : Array.Empty<string>()];

    /// <summary>The bytes the proof module is checked from: the developer's, or <see cref="ObservedProof"/>.</summary>
    byte[] CheckedProofBytes(byte[] source) => ObservesProof ? ObservedProof.Insert(source).Bytes : source;

    /// <summary>Binds a cached proof result to its options; empty for a default run, keeping its keys.</summary>
    string ProofOptionsKey => ProofOptions.Length == 0 ? "" : "\noptions " + string.Join(' ', ProofOptions);

    /// <summary>Messages from the last proof check, kept for display; no check reads them.</summary>
    internal ProofMessage[]? ProofMessages { get; private set; }

    /// <summary>The display form of the last verified statement; null when not printed.</summary>
    internal StatementView? VerifiedStatement { get; private set; }

    const string ProofMessagesFile = "Proof.messages.json";
    const string StatementViewFile = "Proof.statement.json";
    const string NamedErrorSuffix = "._namedError";

    /// <summary>
    /// Lean `--json` output rendered as Lean's plain text, with informational messages labelled
    /// `info:` at their position, and the non-error messages of `source`.
    /// </summary>
    static (string Text, ProofMessage[] Messages) LeanJsonMessages(string output, string source)
    {
        var text = new StringBuilder();
        var messages = new List<ProofMessage>();
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        foreach (var line in output.ReplaceLineEndings("\n").Split('\n'))
        {
            JsonElement message;
            try { message = line.StartsWith('{') ? JsonSerializer.Deserialize<JsonElement>(line) : default; }
            catch (JsonException) { message = default; }
            if (message.ValueKind != JsonValueKind.Object || !message.TryGetProperty("severity", out var severity))
            {
                if (line.Length > 0) text.Append(line).Append('\n');
                continue;
            }
            var file = message.GetProperty("fileName").GetString() ?? "";
            var located = message.TryGetProperty("pos", out var position) && position.ValueKind == JsonValueKind.Object;
            var row = located ? position.GetProperty("line").GetInt32() : 1;
            var column = located ? position.GetProperty("column").GetInt32() : 0;
            var caption = message.TryGetProperty("caption", out var title) ? title.GetString() ?? "" : "";
            var data = message.GetProperty("data").GetString() ?? "";
            if (caption.Length > 0) data = caption + ":\n" + data;
            var kind = message.TryGetProperty("kind", out var tag) ? tag.GetString() ?? "" : "";
            var name = kind.EndsWith(NamedErrorSuffix, StringComparison.Ordinal)
                ? $"({kind[..^NamedErrorSuffix.Length]})" : "";
            var label = severity.GetString() switch { "error" => "error", "warning" => "warning", _ => "info" };
            text.Append($"{file}:{row}:{column}: {label}{name}: {data}");
            if (!data.EndsWith('\n')) text.Append('\n');
            if (label != "error" && file.Length > 0 &&
                Path.GetFullPath(file, Path.GetDirectoryName(source)!).Equals(source, comparison))
                messages.Add(new(label, row, column, data.TrimEnd('\n')));
        }
        return (text.ToString(), [.. messages]);
    }

    /// <summary>
    /// The non-error messages of `source` in a Lake module trace: Lake checks the module with `lean --json`
    /// and logs each message as `file:line:column: text`, with `file` relative to `package`.
    /// </summary>
    static ProofMessage[] LakeTraceMessages(string trace, string package, string source)
    {
        JsonElement record;
        // Display only: an unreadable trace shows no messages rather than failing verification.
        try { record = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(trace)); }
        catch (Exception error) when (error is IOException or JsonException) { return []; }
        if (record.ValueKind != JsonValueKind.Object || !record.TryGetProperty("log", out var log) ||
            log.ValueKind != JsonValueKind.Array)
            return [];
        var entries = log.EnumerateArray()
            .Where(entry => entry.ValueKind == JsonValueKind.Object &&
                entry.TryGetProperty("level", out var level) && level.ValueKind == JsonValueKind.String &&
                entry.TryGetProperty("message", out var text) && text.ValueKind == JsonValueKind.String)
            .Select(entry => (entry.GetProperty("level").GetString()!, entry.GetProperty("message").GetString()!));
        return SourceMessages(entries, package, source);
    }

    /// <summary>The informational and warning entries located in `source`, in their logged order.</summary>
    static ProofMessage[] SourceMessages(IEnumerable<(string Level, string Message)> entries, string package,
        string source)
    {
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        var messages = new List<ProofMessage>();
        foreach (var (level, text) in entries)
        {
            var label = level switch { "info" => "info", "warning" => "warning", _ => null };
            var located = LocatedMessage().Match(text);
            if (label is null || !located.Success ||
                !Path.GetFullPath(located.Groups["file"].Value, package).Equals(source, comparison))
                continue;
            messages.Add(new(label, int.Parse(located.Groups["line"].Value),
                int.Parse(located.Groups["column"].Value), located.Groups["text"].Value.TrimEnd('\n')));
        }
        return [.. messages];
    }

    [GeneratedRegex(@"\A(?<file>[^\n]+?):(?<line>[0-9]+):(?<column>[0-9]+): (?<text>.*)\z", RegexOptions.Singleline)]
    private static partial Regex LocatedMessage();

    static string LeanString(string value) => "\"" + value.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\"";

    /// <summary>
    /// Prints `theorem` from the checked proof module `olean` with only its imports' notation, writing the
    /// view to `directory`: the proof's own declarations are added without its extensions, so proof code
    /// cannot change the text. Display only; returns null when Lean cannot print it.
    /// </summary>
    StatementView? ViewStatement(string directory, string olean, string leanPath, string proofSource, string theorem)
    {
        var imports = SourceImport().Matches(proofSource).Select(import => import.Groups[1].Value)
            .Concat(["Lean", "Extracted", StatementModule]).Distinct(StringComparer.Ordinal);
        var source = Path.Combine(directory, "LeanCILStatement.lean");
        var result = Path.Combine(directory, StatementViewFile);
        File.WriteAllText(source, string.Concat(imports.Select(module => "import " + module + "\n")) + $$"""

            open Lean Meta Elab Command

            /-- A proof declaration for display, without the proof's extensions or kernel checking. -/
            def LeanCILStatement.declaration : ConstantInfo -> Declaration
              | .defnInfo value => .defnDecl value
              | info => .axiomDecl
                  { name := info.name, levelParams := info.levelParams, type := info.type, isUnsafe := false }

            /-- Positions of the `program : CIL.Program` and `method : Nat` binders of a head's type. -/
            def LeanCILStatement.positions : Expr -> Nat -> Option Nat -> Option Nat -> Option (Prod Nat Nat)
              | .forallE name type body _, index, program, method =>
                LeanCILStatement.positions body (index + 1)
                  (if name == `program && type == mkConst ``CIL.Program then some index else program)
                  (if name == `method && type == mkConst ``Nat then some index else method)
              | _, _, some program, some method => some (program, method)
              | _, _, _, _ => none

            /-- Methods that `expression` names through a framework head taking a program and method. -/
            def LeanCILStatement.methods (role : String) (expression : Expr) (table : Array String)
                (proof : NameSet) : MetaM (Array Json) := do
              let found <- IO.mkRef (#[] : Array Json)
              Meta.forEachExpr expression fun sub => do
                let .const head _ := sub.getAppFn | return
                if proof.contains head then return
                let some info := (<- getEnv).find? head | return
                let some (programAt, methodAt) := LeanCILStatement.positions info.type 0 none none | return
                let args := sub.getAppArgs
                unless programAt < args.size && methodAt < args.size do return
                let method := args[methodAt]!
                let index <- if method.hasLooseBVars then pure none else do
                  match <- whnf method with
                  | .lit (.natVal n) => pure (some n)
                  | reduced => evalNat reduced
                let extracted := args[programAt]!.consumeMData == mkConst `Extracted.program
                let signature := if extracted then index.bind (fun position => table[position]?) else none
                found.modify (fun entries => entries.push (Json.mkObj [("role", toJson role),
                  ("head", toJson head.toString), ("extracted", toJson extracted),
                  ("method", toJson index), ("signature", toJson signature)]))
              found.get

            /-- How many leading binders of `type` a printed signature names before its colon. -/
            def LeanCILStatement.namedBinders : Expr -> Nat
              | .forallE name _ body info =>
                if name.hasMacroScopes && !info.isInstImplicit then 0
                else LeanCILStatement.namedBinders body + 1
              | _ => 0

            /-- Whether `value` only projects a field of its argument, as a structure's accessor does. -/
            def LeanCILStatement.projects : Expr -> Bool
              | .lam _ _ body _ => LeanCILStatement.projects body
              | .proj .. => true
              | _ => false

            /-- The proof's definitions that `root` is stated with, each before those its body uses,
                printed as `def name binders : type := body` from its elaborated value. A structure's
                accessors are not listed: the statement names the structure and its fields. -/
            partial def LeanCILStatement.definitions (root : Expr) (proof : NameSet) :
                MetaM (Array Json) := do
              let seen <- IO.mkRef ({} : NameSet)
              let found <- IO.mkRef (#[] : Array Json)
              let rec visit (expression : Expr) : MetaM Unit := do
                for name in expression.getUsedConstants do
                  unless proof.contains name && !(<- seen.get).contains name do continue
                  seen.modify (fun names => names.insert name)
                  let some (.defnInfo definition) := (<- getEnv).find? name | continue
                  if name.isInternalDetail || LeanCILStatement.projects definition.value then continue
                  let named := LeanCILStatement.namedBinders definition.type
                  let signature <- PrettyPrinter.ppSignature name
                  let printed <- lambdaBoundedTelescope definition.value named fun binders body => do
                    if binders.size == named then
                      return f!"def {signature.fmt} :=" ++ Format.nest 2 (Format.line ++ (<- ppExpr body))
                    return f!"def {name} : {<- ppExpr definition.type} :=" ++
                      Format.nest 2 (Format.line ++ (<- ppExpr definition.value))
                  found.modify (fun entries => entries.push (Json.mkObj
                    [("name", toJson name.toString), ("text", toJson (toString printed.group))]))
                  visit definition.value
              visit root
              found.get

            #eval show CommandElabM Unit from do
              let (data, _) <- readModuleData {{LeanString(olean.Replace('\\', '/'))}}
              let mut env <- getEnv
              let mut proof : NameSet := {}
              for info in data.constants do
                unless env.contains info.name do
                  proof := proof.insert info.name
                  if let .ok next := env.addDeclCore 0 0 (LeanCILStatement.declaration info) none
                      (doCheck := false) then
                    env := next
              setEnv env
              let target := {{LeanString(theorem)}}.toName
              let result <- liftTermElabM do
                let statement <- PrettyPrinter.ppSignature target
                let some info := (<- getEnv).find? target | throwError "missing {target}"
                let table <- CIL.MethodIdentity.strings (mkConst `Extracted.signatures)
                forallTelescope info.type fun binders body => do
                  let mut subjects := #[]
                  for binder in binders do
                    subjects := subjects ++
                      (<- LeanCILStatement.methods "premise" (<- inferType binder) table proof)
                  subjects := subjects ++ (<- LeanCILStatement.methods "conclusion" body table proof)
                  return Json.mkObj [("statement", toJson (toString statement.fmt)),
                    ("subjects", toJson subjects),
                    ("definitions", toJson (<- LeanCILStatement.definitions info.type proof))]
              IO.FS.writeFile {{LeanString(result.Replace('\\', '/'))}} result.compress

            """);
        try
        {
            var printed = Execute([LeanExecutable, source], directory, leanPath);
            return printed.Code == 0 && File.Exists(result) ? ReadStatementView(result) : null;
        }
        finally { File.Delete(source); }
    }

    static StatementView? ReadStatementView(string path)
    {
        try { return JsonSerializer.Deserialize<StatementView>(File.ReadAllText(path)); }
        catch (Exception error) when (error is IOException or JsonException) { return null; }
    }

    // Every olean an audit may load from the session library and the proof directory.
    static SortedDictionary<string, string> OleanHashes(string fresh, string session)
    {
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var (name, hash) in ModuleArtifacts(session)) result["library:" + name] = hash;
        foreach (var path in Directory.EnumerateFiles(fresh, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal)))
            result[Path.GetRelativePath(fresh, path).Replace('\\', '/')] = Sha(path);
        return result;
    }

    // An untrusted build may add only its own modules' oleans; any other change voids the replayed set.
    static void RequireOnlyAdded(SortedDictionary<string, string> bound, SortedDictionary<string, string> built,
        params string[] modules)
    {
        if (bound.Any(pair => !built.TryGetValue(pair.Key, out var hash) || hash != pair.Value) ||
            built.Keys.Any(name => !bound.ContainsKey(name) &&
                !modules.Any(module => name.StartsWith(module + ".olean", StringComparison.Ordinal))))
            throw new InvalidOperationException("Compiled artifacts changed during verification");
    }

    sealed record Report(int schema, string assemblySha256, string identitySha256, string theorem, string[] axioms,
        string theoremAudit, SortedDictionary<string, string> inputs, string? libraryKey = null, string? libraryBuild = null,
        string? extractionAudit = null, string[]? initializedTypes = null,
        string? batchSourceSha256 = null, string? batchTheorem = null, string? consumerSupportSha256 = null,
        string[]? staticValues = null, string[]? contractImports = null, PublishedImport[]? imports = null,
        DeploymentDependency[]? contractDependencies = null, string? compositionTheorem = null, string? compositionAudit = null,
        JsonElement[]? initializationAssumptions = null, string[]? opaqueStaticValues = null,
        StatementDefinition[]? specification = null, string[]? libraryModules = null);

    static JsonElement[] InitializationAssumptions(JsonElement extraction) =>
        extraction.TryGetProperty("initializationAssumptions", out var assumptions)
            ? assumptions.EnumerateArray().ToArray() : [];

    static string[] StaticValueAssumptions(JsonElement extraction) =>
        extraction.TryGetProperty("staticValues", out var values) ? values.Deserialize<string[]>() ?? [] : [];

    // Fields the theorem reads from the caller's static bindings instead of a computed constant.
    static string[] OpaqueStaticValues(JsonElement extraction) =>
        extraction.TryGetProperty("opaqueStaticValues", out var values) ? values.Deserialize<string[]>() ?? [] : [];

    /// <summary>The module the statement display imports beside the proof's own imports.</summary>
    const string StatementModule = "CIL.MethodIdentity";

    /// <summary>
    /// Every module that single-file verification of this proof compiles against or loads: the imports of the
    /// proof, of the extraction and of its symbols, the statement display's, and the observer, which the proof
    /// is checked against under `--goals`, so the closure is the same with it. Null when the proof needs the
    /// whole library: contract imports, a full-import audit, or an import that is neither the extraction nor
    /// a framework module.
    /// </summary>
    string[]? ClosureRoots(string proofSource, string output, string? symbolsSource, ExtractionIdentity extraction)
    {
        if (!importClosureFirst || fullImportAudit is not null || forceFullVerification ||
            extraction.Sources.Count > 0 || HasContractImports(extraction)) return null;
        static IEnumerable<string> Imports(string source) =>
            SourceImport().Matches(source).Select(import => import.Groups[1].Value);
        var proofImports = Imports(proofSource).ToArray();
        static bool Generated(string module) =>
            module is "Extracted" or "ExtractedSymbols" || SelectionModules.Is(module);
        if (proofImports.Any(module => !Generated(module) && !IsFrameworkModule(module) &&
                module.Split('.')[0] is not ("Init" or "Lean" or "Std")))
            return null;
        return [.. proofImports.Concat(Imports(File.ReadAllText(Path.Combine(output, "Extracted.lean"))))
            .Concat(symbolsSource is null ? [] : Imports(File.ReadAllText(symbolsSource)))
            .Concat([StatementModule, ObservedProof.Module]).Where(IsFrameworkModule).Distinct(StringComparer.Ordinal)];
    }

    Report Verify(string assembly, string identity, string entry, string proof, string output,
        string profile = "scalar", string theorem = "ExampleProof.correctness", bool check = false, bool existingArtifacts = false,
        string? settings = null, Action<string>? stage = null)
    {
        assembly = Path.GetFullPath(assembly);
        proof = Path.GetFullPath(proof);
        output = Path.GetFullPath(output);

        if (!Regex.IsMatch(theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
            throw new ArgumentException("Invalid theorem name");

        Directory.CreateDirectory(output);

        var reportPath = Path.Combine(output, "verified.json");

        if (check)
        {
            var old = JsonSerializer.Deserialize<Report>(File.ReadAllText(reportPath)) ?? throw new InvalidOperationException("Missing report");
            RunExtractor(Extract("check", assembly, identity, entry, output, profile));

            if (old.schema != 4 || string.IsNullOrWhiteSpace(old.extractionAudit) || !Same(old.inputs, Inputs(proof, settings)) || old.identitySha256 != Sha(Path.Combine(output, "identity.json")) ||
                old.theorem != theorem || old.assemblySha256 != Sha(assembly) ||
                (old.batchSourceSha256 is not null && (string.IsNullOrWhiteSpace(old.batchTheorem) ||
                    old.batchSourceSha256 != Sha(Path.Combine(output, "Batch.lean")))))
                throw new InvalidOperationException("Stale verification report or changed proof inputs");

            return old;
        }

        // A failed attempt must not leave an earlier successful report behind.
        File.Delete(reportPath);
        ProofMessages = null;
        VerifiedStatement = null;
        stage?.Invoke("extraction integrity");
        if (existingArtifacts)
            RunExtractor(["dotnet", ExtractorPath, "check", output]);
        else EnsureExtractorBuilt();

        if (!existingArtifacts)
            Run(Extract("extract", assembly, identity, entry, output, profile));
        byte[] proofSourceBytes = File.ReadAllBytes(proof);
        string proofSourceHash = Convert.ToHexStringLower(SHA256.HashData(proofSourceBytes));
        string proofSource;
        using (StreamReader reader = new(new MemoryStream(proofSourceBytes)))
        {
            proofSource = reader.ReadToEnd();
        }
        bool symbols = ImportsSymbols(proofSource);
        string? symbolsSource = symbols ? SymbolsFor(output) : null;
        byte[]? symbolsSourceBytes = symbolsSource is null ? null : File.ReadAllBytes(symbolsSource);
        string? symbolsSourceHash = symbolsSourceBytes is null ? null : Convert.ToHexStringLower(SHA256.HashData(symbolsSourceBytes));
        var before = Inputs(proof, settings);
        if (before["proof:" + proof] != proofSourceHash)
            throw new InvalidOperationException("Proof inputs changed before their source snapshot");
        ExtractionIdentity extraction = ExtractionIdentity.Read(output);
        referenceOnlyAuthoring = ReferenceOnlyImports(extraction);
        string[] selected = SelectionModules.Selected(
            SourceImport().Matches(proofSource).Select(import => import.Groups[1].Value), extraction.Root, proof);

        // Retain the selected bytes before support or interface builds can run code.
        void RequireOriginalProofSources()
        {
            if (!File.Exists(proof) || Sha(proof) != proofSourceHash ||
                symbolsSource is not null && (!File.Exists(symbolsSource) || Sha(symbolsSource) != symbolsSourceHash))
                throw new InvalidOperationException("Proof inputs changed during verification");
        }

        // Use a source-bound build; CI and --rebuild-library bypass the local library cache.
        stage?.Invoke("Lean library build");
        var closureRoots = ClosureRoots(proofSource, output, symbolsSource, extraction);
        var session = Library(before, closureRoots: closureRoots);
        RequireReplayedImports(closureRoots ?? []);
        HashSet<string> importSourceNames = extraction.Sources.Keys.ToHashSet(StringComparer.Ordinal);
        var support = Regex.Matches(proofSource, @"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", RegexOptions.Multiline)
            .Select(m => m.Groups[1].Value)
            .Where(n => n is not ("Extracted" or "ExtractedSymbols") && !SelectionModules.Is(n) &&
                !importSourceNames.Contains(n) && n.Split('.')[0] is not ("Init" or "Lean" or "Std")).ToArray();

        if (support.Length > 0)
        {
            // Lean's dependency query supplies the import closure. When dependencies
            // are not built yet, a conservative source snapshot safely widens the key.
            var supportSources = SupportInputs(session, support, before);
            var supportKey = ContentKey("support-audit-v1\n" + VerificationPolicy + "\n" + libraryKey + "\n" +
                string.Join("\n", support.Order(StringComparer.Ordinal)) + "\n" + JsonSerializer.Serialize(supportSources));
            if (!preparedSupport.Contains(supportKey))
            {
                var staging = Path.Combine(Path.GetTempPath(), "leancil-support-" + Guid.NewGuid().ToString("N"));
                Directory.CreateDirectory(staging);
                try
                {
                    if (RestoreSuccess(supportKey, staging))
                    {
                        var restored = ModuleArtifacts(staging);
                        CopyTree(staging, session);
                        foreach (var (name, hash) in restored) certifiedModules![name] = hash;
                        supportCacheHits++;
                        CacheProgress("certified dependencies: " + entry);
                    }
                    else
                    {
                        Run(["lake", "build", .. support], session, progress: "Building proof dependencies: " + entry);
                        var current = SessionModules(session);
                        var altered = certifiedModules!.Any(pair => !current.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
                        var changed = (altered ? current : current.Where(pair => !certifiedModules!.ContainsKey(pair.Key)))
                            .Select(pair => ModuleName(pair.Key)).Distinct().ToArray();
                        if (changed.Length > 0)
                        {
                            stage?.Invoke("kernel replay");
                            Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"), .. changed],
                                leanPath: SessionLeanPath(session), progress: "Kernel replay of proof dependencies: " + entry);
                        }
                        certifiedModules = current;
                        CopySupportArtifacts(session, staging, supportSources);
                        PublishSuccess(supportKey, staging);
                    }
                }
                finally { Directory.Delete(staging, true); }
                preparedSupport.Add(supportKey);
            }
        }

        RequireOriginalProofSources();
        var identityHash = extraction.Sha256;

        // Isolate generated code and the selected proof, then audit the named theorem.
        var fresh = Path.Combine(output, "proof-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(fresh);
        string audit;
        string extractionAudit = "";
        string[] axioms;
        FullImportResult? fullResult = null;
        string stagedProof = Path.Combine(fresh, "Proof.lean");
        string stagedSymbols = Path.Combine(fresh, "ExtractedSymbols.lean");
        // Diagnostics in these copies cite the files they were copied from.
        var copies = new SourceCopies(fresh);
        byte[] stagedProofBytes = CheckedProofBytes(proofSourceBytes);
        string stagedProofHash = Convert.ToHexStringLower(SHA256.HashData(stagedProofBytes));
        void RequireStagedProofSources()
        {
            if (!File.Exists(stagedProof) || Sha(stagedProof) != stagedProofHash)
                throw new InvalidOperationException("Proof sources changed during verification: Proof.lean");
            if (symbols && (!File.Exists(stagedSymbols) || Sha(stagedSymbols) != symbolsSourceHash))
                throw new InvalidOperationException("Proof sources changed during verification: ExtractedSymbols.lean");
        }

        try
        {
            File.Copy(Path.Combine(output, "Extracted.lean"), Path.Combine(fresh, "Extracted.lean"));
            if (Sha(Path.Combine(fresh, "Extracted.lean")) != extraction.Root.GetProperty("generatedSha256").GetString())
                throw new InvalidOperationException("Inputs changed during verification");
            copies.Add(Path.Combine(fresh, "Extracted.lean"), Path.Combine(output, "Extracted.lean"));
            string[] importModules = StageImportSources(extraction, fresh);
            var leanPath = fresh + Path.PathSeparator + SessionLeanPath(session);

            var currentModules = SessionModules(session);
            var alteredExisting = certifiedModules!.Any(pair => !currentModules.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
            var changedModules = (alteredExisting ? currentModules.Keys : currentModules.Keys.Where(name => !certifiedModules!.ContainsKey(name)))
                .Select(ModuleName).Distinct().ToArray();
            if (changedModules.Length > 0)
            {
                stage?.Invoke("kernel replay");
                ReplayCheckedModules(changedModules, leanPath, "Kernel replay of proof dependencies: " + entry);
                certifiedModules = currentModules;
            }
            // Full artifact identities include transitive support dependencies and every
            // olean part. Cached success is never inferred from an unsigned manifest.
            var environmentKey = ContentKey("certified-modules-v1\n" + VerificationPolicy + "\n" + libraryKey + "\n" + JsonSerializer.Serialize(currentModules));
            var extractedKey = ContentKey("extraction-audit-v3-direct-certificate\n" + environmentKey + "\n" +
                Sha(Path.Combine(fresh, "Extracted.lean")));
            string? extractionPublication = null;
            if (RestoreSuccess(extractedKey, fresh))
            {
                extractionCacheHits++;
                CacheProgress("certified extraction: " + entry);
            }
            else
            {
                // The native audit checks this theorem's exact type after independent kernel replay.
                stage?.Invoke("proof checking");
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.Combine(fresh, "Extracted.olean"),
                    Path.Combine(fresh, "Extracted.lean")], leanPath: leanPath, progress: "Checking Extracted: " + entry);
                var publication = Path.Combine(fresh, "extraction-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path =>
                    Path.GetFileName(path).StartsWith("Extracted.olean", StringComparison.Ordinal)))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                extractionPublication = publication;
            }
            // Interfaces, symbols and the proof each run code when built: each build may add only its own oleans.
            var bound = OleanHashes(fresh, session);
            // A keyed module only re-exports its plain one, which is what the audits below read.
            void BuildSelected(bool symbolsModules)
            {
                foreach (var module in selected.Where(module => SelectionModules.IsSymbols(module) == symbolsModules))
                {
                    var path = Path.Combine(fresh, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
                    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                    File.WriteAllText(path, SelectionModules.Source(module));
                    Run([LeanExecutable, "--root=" + fresh, "-o", Path.ChangeExtension(path, ".olean"), path],
                        leanPath: leanPath, progress: "Checking " + module);
                    var next = OleanHashes(fresh, session);
                    RequireOnlyAdded(bound, next, module.Replace('.', '/'));
                    bound = next;
                }
            }
            BuildSelected(symbolsModules: false);
            foreach (string module in importModules.Where(module => module != "ExtractedImports"))
            {
                string source = Path.Combine(fresh, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.ChangeExtension(source, ".olean"), source], leanPath: leanPath,
                    progress: "Checking contract interface: " + module);
                var next = OleanHashes(fresh, session);
                RequireOnlyAdded(bound, next, module.Replace('.', '/'));
                bound = next;
            }
            if (importModules.Contains("ExtractedImports", StringComparer.Ordinal))
            {
                string assumptionsSource = Path.Combine(fresh, "ExtractedImports.lean");
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.ChangeExtension(assumptionsSource, ".olean"), assumptionsSource],
                    leanPath: leanPath, progress: "Checking App import assumptions");
                var next = OleanHashes(fresh, session);
                RequireOnlyAdded(bound, next, "ExtractedImports");
                bound = next;
            }
            // The audit, the replay and the proof must all read the bytes compiled here.
            SortedDictionary<string, string> acceptedInterfaceArtifacts = ContractInterfaceArtifacts(fresh, importModules);
            if (importModules.Length > 0)
            {
                stage?.Invoke("kernel replay");
                string InterfaceArtifact(string module) => Path.Combine(fresh, module.Replace('.', '/') + ".olean");
                if (!TryReplayContractInterfaces(extraction, importModules, leanPath, InterfaceArtifact))
                {
                    ReplayCheckedModules(importModules, leanPath,
                        "Kernel replay of published contract interfaces and App import assumptions");
                    CheckContractInterfaces(extraction, importModules, leanPath, InterfaceArtifact);
                }
                if (!Same(bound, OleanHashes(fresh, session)))
                    throw new InvalidOperationException("Compiled artifacts changed during verification");
                RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            }
            if (File.Exists(stagedProof))
                throw new InvalidOperationException("Proof sources changed during verification: Proof.lean");
            if (File.Exists(stagedSymbols))
                throw new InvalidOperationException("Proof sources changed during verification: ExtractedSymbols.lean");
            RequireOriginalProofSources();
            File.WriteAllBytes(stagedProof, stagedProofBytes);
            if (symbols) File.WriteAllBytes(stagedSymbols, symbolsSourceBytes!);
            RequireStagedProofSources();
            if (ObservesProof) copies.AddObserved(stagedProof, proof);
            else copies.Add(stagedProof, proof);
            if (symbols) copies.Add(stagedSymbols, symbolsSource!);
            if (symbols)
            {
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.Combine(fresh, "ExtractedSymbols.olean"), stagedSymbols],
                    leanPath: leanPath, progress: "Checking ExtractedSymbols: " + entry);
                var next = OleanHashes(fresh, session);
                RequireOnlyAdded(bound, next, "ExtractedSymbols");
                bound = next;
                BuildSelected(symbolsModules: true);
                RequireStagedProofSources();
            }
            RequireStagedProofSources();
            // Cached proofs carry their Lean messages and statement display.
            var proofKey = ContentKey("theorem-audit-v3\n" + extractedKey + "\n" + proofSourceHash + "\n" +
                (symbols ? symbolsSourceHash + "\n" : "") +
                SemanticExtractionIdentity(extraction) + "\n" + JsonSerializer.Serialize(extraction.Sources) + "\n" +
                JsonSerializer.Serialize(acceptedInterfaceArtifacts) + "\n" + theorem + ProofOptionsKey);
            var proofRestored = RestoreSuccess(proofKey, fresh);
            if (proofRestored)
            {
                proofCacheHits++;
                CacheProgress("certified proof: " + entry);
                var cachedMessages = Path.Combine(fresh, ProofMessagesFile);
                ProofMessages = copies.Relocate(proof, File.Exists(cachedMessages)
                    ? JsonSerializer.Deserialize<ProofMessage[]>(File.ReadAllText(cachedMessages)) : null);
            }
            else
            {
                stage?.Invoke("proof checking");
                RequireStagedProofSources();
                string[] command = [LeanExecutable, "--json", .. ProofOptions, "--root=" + fresh, "-o",
                    Path.Combine(fresh, "Proof.olean"), stagedProof];
                var checkedProof = Execute(command, leanPath: leanPath, progress: "Checking Proof: " + entry);
                var (transcript, messages) = LeanJsonMessages(checkedProof.Output, stagedProof);
                ProofMessages = copies.Relocate(proof, messages);
                if (checkedProof.Code != 0)
                    throw new InvalidOperationException(
                        $"Command failed ({checkedProof.Code}): {string.Join(' ', command)}\n{transcript}");
                File.WriteAllText(Path.Combine(fresh, ProofMessagesFile), JsonSerializer.Serialize(messages));
            }
            RequireStagedProofSources();
            var built = OleanHashes(fresh, session);
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            RequireOnlyAdded(bound, built, "Proof");
            // Interface oleans were replayed above and RequireOnlyAdded kept them unchanged since.
            string[] unreplayed = [.. extractionPublication is null ? Array.Empty<string>() : ["Extracted"],
                .. symbols && !proofRestored ? ["ExtractedSymbols"] : Array.Empty<string>(),
                .. proofRestored ? Array.Empty<string>() : ["Proof"]];
            // Replaying every module from the extraction to the proof lets the audit read that environment without a
            // second import. ExtractedImports imports Extracted from outside the set, which a joint replay rejects.
            string[] replay = unreplayed.Length == 0 || importModules.Length > 0 ? unreplayed :
                ["Extracted", .. selected.Where(module => !SelectionModules.IsSymbols(module)),
                    .. symbols ? ["ExtractedSymbols", .. selected.Where(SelectionModules.IsSymbols)]
                        : Array.Empty<string>(),
                    "Proof"];
            string[] auditModules = ["Proof", "Extracted",
                .. HasContractImports(extraction) ? ["ExtractedImports"] : Array.Empty<string>()];
            AuditRequest[] proofAudits =
                [ProofTheorem(theorem, extraction), ExtractionCertificate("Extracted.translation_valid")];
            AuditedOleans? audited = null;
            // A caller that ends the run at the stage after the proof check must do so before the display starts.
            var replays = replay.Length > 0;
            stage?.Invoke(replays ? "kernel replay" : "theorem audit");
            // The display runs beside replay and audit; it feeds no check and is read only after all of them.
            var statementView = Path.Combine(fresh, StatementViewFile);
            var statementCached = proofRestored && File.Exists(statementView);
            var proofOlean = Path.Combine(fresh, "Proof.olean");
            var viewing = viewsStatement && !statementCached
                ? Task.Run(() => ViewStatement(fresh, proofOlean, leanPath, proofSource, theorem)) : null;
            StatementView? viewed;
            try
            {
                if (replays)
                {
                    RequireStagedProofSources();
                    if (Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") != "true")
                    {
                        try
                        {
                            audited = AuditOleans(leanPath, auditModules, proofAudits,
                                ImportPremise(extraction), replayTargets: replay);
                        }
                        catch (InvalidOperationException) { }
                    }
                    // A rejected combined replay retains the original checker diagnostics.
                    if (audited is null)
                        ReplayCheckedModules(replay, leanPath,
                            (proofRestored ? "Kernel replay of extraction: " : "Kernel replay: ") + entry);
                    stage?.Invoke("theorem audit");
                }
                // The audit reads the replayed bytes; all source and artifact guards still follow it.
                RequireStagedProofSources();
                audited ??= AuditOleans(leanPath, auditModules, proofAudits, ImportPremise(extraction));
            }
            finally
            {
                // The display process must exit before the artifact guard below and before its files are deleted.
                try { viewing?.Wait(); }
                catch (AggregateException) { }
            }
            viewed = viewing?.GetAwaiter().GetResult();
            RequireStagedProofSources();
            if (!Same(built, OleanHashes(fresh, session)))
                throw new InvalidOperationException("Compiled artifacts changed during verification");
            RequireAuditedModule(audited, "Proof", Path.Combine(fresh, "Proof.olean"));
            RequireAuditedModule(audited, "Extracted", Path.Combine(fresh, "Extracted.olean"));
            if (HasContractImports(extraction))
                RequireAuditedModule(audited, "ExtractedImports", Path.Combine(fresh, "ExtractedImports.olean"));
            RequireAuditedConstants(audited);
            stage?.Invoke("extraction certificate audit");
            AuditedAxioms(audited.theorems[1]);
            extractionAudit = AuditText(audited.theorems[1]);
            stage?.Invoke("theorem audit");
            axioms = AuditedAxioms(audited.theorems[0]);
            audit = AuditText(audited.theorems[0]);
            RequireOriginalProofSources();
            RequireStagedProofSources();
            RequireOriginalProofSources();
            if (!Same(before, Inputs(proof, settings)) || identityHash != Sha(Path.Combine(output, "identity.json")))
                throw new InvalidOperationException("Inputs changed during verification");
            // The display is published only here, after every check above, and never feeds a check.
            if (viewsStatement)
                VerifiedStatement = statementCached ? ReadStatementView(statementView) : viewed;
            if (!proofRestored)
            {
                var publication = Path.Combine(fresh, "proof-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path =>
                    Path.GetFileName(path).StartsWith("Proof.olean", StringComparison.Ordinal) ||
                    Path.GetFileName(path) is ProofMessagesFile or StatementViewFile))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
                PublishSuccess(proofKey, publication);
            }
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            if (extractionPublication is not null)
            {
                PublishSuccess(extractedKey, extractionPublication);
            }
            fullResult = fullImportAudit?.Invoke(output, fresh, "Proof", leanPath);

            // Bind the report only after confirming inputs stayed unchanged.
            stage?.Invoke("extraction integrity");
            RunExtractor(existingArtifacts ? ["dotnet", ExtractorPath, "check", output]
                : Extract("check", assembly, identity, entry, output, profile));

            RequireOriginalProofSources();
            if (!Same(before, Inputs(proof, settings)) || identityHash != Sha(Path.Combine(output, "identity.json")))
                throw new InvalidOperationException("Inputs changed during verification");
            // An editor package requires the same library by path and may have built into it meanwhile.
            RequireUnchangedLibrary();

            var initializedTypes = extraction.Root.TryGetProperty("initializedTypes", out var assumptions)
                ? assumptions.Deserialize<string[]>() : [];
            RequireImplementationImports(extraction);
            var report = new Report(4, Sha(assembly), identityHash, theorem, axioms, audit, before, libraryKey, libraryBuild, extractionAudit, initializedTypes,
                staticValues: StaticValueAssumptions(extraction.Root),
                opaqueStaticValues: OpaqueStaticValues(extraction.Root),
                contractImports: ContractImportAssumptions(extraction.Root),
                imports: fullResult?.Imports ?? PublishedImports(extraction.Root),
                contractDependencies: fullResult?.Dependencies ?? DeploymentDependencies(extraction.Root),
                compositionTheorem: fullResult?.Theorem, compositionAudit: fullResult?.Audit,
                initializationAssumptions: InitializationAssumptions(extraction.Root), libraryModules: libraryModules);
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");
            completesLibrary = libraryModules is not null;

            return report;
        }
        catch (Exception error)
        {
            error.Data[SourceCopies.Key] = copies;
            throw;
        }
        finally
        {
            Directory.Delete(fresh, true);
        }
    }

    void IDisposable.Dispose()
    {
        if (session is not null && Directory.Exists(session))
            Directory.Delete(session, true);
        if (ownsLibrary && library is not null && Directory.Exists(library))
            Directory.Delete(library, true);
        if (completesLibrary) CompleteLibrary();
    }

    /// <summary>
    /// Builds, kernel-replays and caches the whole library after a result was reported against a closure
    /// entry, so later runs and editor packages use it. A failure here leaves the reported result standing.
    /// </summary>
    void CompleteLibrary()
    {
        completesLibrary = false;
        Console.Out.Flush();
        Console.Error.WriteLine($"The result above was checked against the {libraryModules!.Length} framework " +
            "modules the proof imports. Building the whole certified library for later runs.");
        try
        {
            using var whole = new Program();
            whole.Library(Inputs(At("CIL.lean")));
        }
        catch (Exception error) when (error is InvalidOperationException or InvalidDataException or IOException or
            UnauthorizedAccessException)
        {
            Console.Error.WriteLine("The whole certified library was not built; the next run builds it. " +
                error.Message);
        }
    }
}

/// <summary>
/// The developer's files a verification session copied, by the path of each copy, so diagnostics cite the file
/// the developer edits. Only byte-identical copies are recorded, so a copy's lines and columns are the original's.
/// </summary>
internal sealed partial class SourceCopies(string directory)
{
    /// <summary>Exception.Data key holding the session's copies when verification fails.</summary>
    internal const string Key = "LeanCIL.SourceCopies";

    static readonly StringComparer PathComparer =
        OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;
    readonly Dictionary<string, string> originals = new(PathComparer);
    readonly Dictionary<string, string> modules = new(StringComparer.Ordinal);
    // An observed copy's line holding the inserted import, by the copy's path.
    readonly Dictionary<string, int> observedLines = new(PathComparer);

    [GeneratedRegex(@"\A(?<file>.+?\.lean):(?<line>\d+):(?<column>\d+)\z")]
    private static partial Regex Location();

    /// <summary>
    /// Records `copy` as a copy of `original` when their bytes are equal; a copy that differs keeps its own path,
    /// since its locations would point elsewhere in the original.
    /// </summary>
    internal bool Add(string copy, string original)
    {
        if (!File.Exists(copy) || !File.Exists(original) ||
            !File.ReadAllBytes(copy).AsSpan().SequenceEqual(File.ReadAllBytes(original)))
            return false;
        originals[Path.GetFullPath(copy, directory)] = Path.GetFullPath(original);
        return true;
    }

    /// <summary>
    /// <see cref="Add(string, string)"/> for a copy built as module `copyModule`, which Lake's progress lines name,
    /// of the original's module `originalModule`.
    /// </summary>
    internal bool Add(string copy, string original, string copyModule, string originalModule)
    {
        if (!Add(copy, original)) return false;
        modules[copyModule] = originalModule;
        return true;
    }

    /// <summary>
    /// Records `copy` as <see cref="ObservedProof"/> of `original` when its bytes are exactly that; positions on the
    /// line of the inserted import are read back past it, and every other position is the original's.
    /// </summary>
    internal bool AddObserved(string copy, string original)
    {
        if (!File.Exists(copy) || !File.Exists(original)) return false;
        var (observed, line) = ObservedProof.Insert(File.ReadAllBytes(original));
        if (!File.ReadAllBytes(copy).AsSpan().SequenceEqual(observed)) return false;
        var key = Path.GetFullPath(copy, directory);
        originals[key] = Path.GetFullPath(original);
        observedLines[key] = line;
        return true;
    }

    /// <summary><see cref="AddObserved(string, string)"/> for a copy Lake builds as module `copyModule`.</summary>
    internal bool AddObserved(string copy, string original, string copyModule, string originalModule)
    {
        if (!AddObserved(copy, original)) return false;
        modules[copyModule] = originalModule;
        return true;
    }

    /// <summary>
    /// The file, line and column in the original of a position Lean printed in `file`, or the position as printed
    /// when `file` is no copy. A column inside an inserted import reads as the start of its line.
    /// </summary>
    internal (string File, int Line, int Column) Position(string file, int line, int column)
    {
        var key = Path.GetFullPath(file, directory);
        if (!originals.TryGetValue(key, out var original)) return (file, line, column);
        var shifted = observedLines.TryGetValue(key, out var observed) && observed == line;
        return (original, line, shifted ? Math.Max(0, column - ObservedProof.Import.Length) : column);
    }

    /// <summary>
    /// `messages` Lean reported for the copy of `original`, each at its position in the original, with the error a
    /// failure record cites read the same way; unchanged when `original` has no observed copy.
    /// </summary>
    internal Program.ProofMessage[]? Relocate(string original, Program.ProofMessage[]? messages)
    {
        var full = Path.GetFullPath(original);
        var copy = observedLines.Keys.FirstOrDefault(key => PathComparer.Equals(originals[key], full));
        if (messages is null || copy is null) return messages;
        int Column(int line, int column) => Position(copy, line, column).Column;
        return [.. messages.Select(message => message with
        {
            column = Column(message.line, message.column),
            text = message.text.StartsWith(Program.FailureMarker, StringComparison.Ordinal) &&
                System.Text.Json.Nodes.JsonNode.Parse(message.text[Program.FailureMarker.Length..]) is
                    System.Text.Json.Nodes.JsonObject { } record &&
                record["error"] is System.Text.Json.Nodes.JsonObject { } error &&
                error["line"]?.GetValue<int>() is { } line && error["column"]?.GetValue<int>() is { } column
                    ? Program.FailureMarker + Relocated(record, line, Column(line, column)) : message.text
        })];
    }

    // The record with the error it cites moved to `column`.
    static string Relocated(System.Text.Json.Nodes.JsonObject record, int line, int column)
    {
        record["error"] = new System.Text.Json.Nodes.JsonObject { ["line"] = line, ["column"] = column };
        return record.ToJsonString();
    }

    /// <summary>
    /// `text` with each copy's path read as its original and the workspace's other paths shown as
    /// <see cref="Workspace"/>, its `--root` argument left out: the workspace is deleted when verification ends.
    /// </summary>
    internal string Displayed(string text, Func<string, string>? display = null)
    {
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        // Longer paths first, so a copy inside another copy's directory keeps its own original.
        foreach (var (copy, original) in originals.OrderByDescending(pair => pair.Key.Length))
            text = text.Replace(copy, display?.Invoke(original) ?? original, comparison);
        var workspace = Path.GetFullPath(directory)
            .TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
        return text.Replace(" --root=" + workspace, "", comparison).Replace(workspace, Workspace, comparison);
    }

    /// <summary>How <see cref="Displayed"/> shows the deleted verification workspace.</summary>
    internal const string Workspace = "<verification workspace>";

    /// <summary>The original module of `module`, a copy's module as Lake named it, or `module` itself.</summary>
    internal string ModuleOf(string module) => modules.GetValueOrDefault(module, module);

    /// <summary>The original of `file`, a path as Lean or Lake printed it, or null when it is no copy.</summary>
    internal string? OriginalOf(string file) => originals.GetValueOrDefault(Path.GetFullPath(file, directory));

    /// <summary>`location`, a `file:line:column`, citing through `display` the original of a copied file.</summary>
    internal string Locate(string location, Func<string, string>? display = null)
    {
        var match = Location().Match(location);
        if (!match.Success || OriginalOf(match.Groups["file"].Value) is not { } original) return location;
        var (_, line, column) = Position(match.Groups["file"].Value, int.Parse(match.Groups["line"].Value),
            int.Parse(match.Groups["column"].Value));
        return $"{display?.Invoke(original) ?? original}:{line}:{column}";
    }
}

/// <summary>
/// The proof `verify` checks when asked for failure records or a trace: the developer's proof with
/// <see cref="Import"/> inserted at the start of its first import line, so the observer runs on it and every
/// other line and column is the original's.
/// </summary>
internal static partial class ObservedProof
{
    /// <summary>The observer module, which a proof asked for records, a trace or goals is checked against.</summary>
    internal const string Module = "CIL.Observe";
    /// <summary>The text inserted, which imports the observer ahead of the proof's own imports.</summary>
    internal const string Import = "import " + Module + " ";

    // An import command, plain or with module-system modifiers, at the start of a line.
    [GeneratedRegex(@"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b", RegexOptions.Multiline)]
    private static partial Regex ImportLine();

    /// <summary>`source` with <see cref="Import"/> inserted, and the 1-based line it was inserted on.</summary>
    internal static (byte[] Bytes, int Line) Insert(byte[] source)
    {
        var preamble = source.AsSpan().StartsWith(Encoding.UTF8.Preamble) ? Encoding.UTF8.Preamble.Length : 0;
        var text = Encoding.UTF8.GetString(source, preamble, source.Length - preamble);
        var match = ImportLine().Match(text);
        // A multiline `^` matches at a line start, so the match starts the import's line.
        var start = match.Success ? match.Index : 0;
        var at = preamble + Encoding.UTF8.GetByteCount(text.AsSpan(0, start));
        var line = 1 + text.AsSpan(0, start).Count('\n');
        return ([.. source.AsSpan(0, at), .. Encoding.UTF8.GetBytes(Import), .. source.AsSpan(at)], line);
    }
}
