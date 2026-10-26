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
    static string Root { get; } = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(Source())!, ".."));
#endif

    static string Source([CallerFilePath] string path = "") => path;

    string? library;
    const string CertifiedFingerprintsName = "canonical-fingerprints.json";
    string? certifiedFingerprintsSha;
    string? resolvedToolchain;
    bool extractorBuilt;

    const string ExtractorBuildEnvironment = "LEANCIL_PREPARED_EXTRACTOR";

    static string[] FixtureCommand(string script, string[] arguments, bool prepared)
    {
        string[] buildArguments = prepared
            ? ["-c", "Release", "--no-build", "-p:EnforceCodeStyleInBuild=true",
                "-p:GenerateDocumentationFile=true"]
            : [];
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
    bool UseSuccessCache => !referenceOnlyAuthoring && !freshLibrary &&
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
        if (targets.Length > 1 && ReplayModulesJointly(Root, targets, leanPath, progress)) return;
        Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"),
            .. targets], leanPath: leanPath, progress: progress);
    }

    static SortedDictionary<string, string> ModuleArtifacts(string session) =>
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

    static async Task<string> CaptureOutput(StreamReader reader, TextWriter writer, ProgressSummary? summary = null, TextWriter? transcript = null)
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
            else
                for (var i = 0; i < count; i++)
                    if (buffer[i] == '\n')
                    {
                        summary.Add(line.ToString().TrimEnd('\r'), writer);
                        line.Clear();
                    }
                    else line.Append(buffer[i]);
        }
        if (summary is not null && line.Length > 0) summary.Add(line.ToString(), writer);
        return captured.ToString();
    }

    static readonly object TraceGate = new();

    static (int Code, string Output, string Stdout, string Stderr) Execute(IEnumerable<string> command, string? cwd = null, string? leanPath = null,
        bool streamOutput = false, string? progress = null, IReadOnlyDictionary<string, string>? environment = null)
    {
        var traceStage = progress;
#if LEANCIL_TOOL
        // CLI output is a stable interface; progress belongs to the repository runner.
        progress = null;
        streamOutput = false;
#endif
        // Aggregate at the suite boundary; nested build/proof phases feed this summary.
        var summary = streamOutput && progress is not null ? new ProgressSummary(progress) : null;
        streamOutput |= progress is not null;
        var args = command.ToArray();
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
        foreach (var (name, value) in environment ?? new Dictionary<string, string>())
            start.Environment[name] = value;

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
        var stdout = CaptureOutput(process.StandardOutput, streamOutput ? Console.Out : TextWriter.Null, summary, traceWriter);
        var stderr = CaptureOutput(process.StandardError, streamOutput ? Console.Error : TextWriter.Null, summary, traceWriter);
        if (summary is null) process.WaitForExit();
        else
            while (!process.WaitForExit(10_000)) summary.Report();

        var output = stdout.GetAwaiter().GetResult();
        var error = stderr.GetAwaiter().GetResult();
        if (progress is not null)
            Console.WriteLine($"END {progress} (exit {process.ExitCode}, {elapsed.Elapsed.TotalSeconds:F1}s)");
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
            File.AppendAllText(Path.Combine(traceDirectory, $"{Environment.ProcessId}.jsonl"), JsonSerializer.Serialize(new {
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

    static SortedDictionary<string, string> Inputs(string proof, string? settings = null)
        => Inputs(CommonInputs(), proof, settings);

    static SortedDictionary<string, string> CommonInputs()
    {
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);

        foreach (var name in new[] { "lean-toolchain", "lakefile.toml", "lake-manifest.json", "CIL.lean" })
            result[name] = Sha(At(name));

        var folders = new List<(string, string[])> { ("CIL", [".lean"]), ("Examples", [".lean"]), ("Tests", [".lean"]) };
#if !LEANCIL_TOOL
        foreach (var name in new[] { "global.json", "Directory.Build.props", "Directory.Packages.props", ".editorconfig" })
            result[name] = Sha(At(name));
        folders.AddRange([("Extractor", [".cs", ".csproj"]), ("scripts", [".cs"])]);
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
    string? libraryKey;
    string? libraryBuild;

    static SortedDictionary<string, string> LibrarySources(SortedDictionary<string, string> snapshot) =>
        new(snapshot.Where(p => p.Key.StartsWith("CIL/", StringComparison.Ordinal) ||
            p.Key is "CIL.lean" or "lakefile.toml" or "lake-manifest.json" or "lean-toolchain").ToDictionary(), StringComparer.Ordinal);

    static SortedDictionary<string, string> CacheFiles(string directory) =>
        HashFiles(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path) is not ("cache-manifest.json" or "cache-receipt.hmac"))
            .Select(path => (Path.GetRelativePath(directory, path).Replace('\\', '/'), path)));

    static bool ValidCache(string directory)
    {
        try
        {
            var manifest = JsonSerializer.Deserialize<SortedDictionary<string, string>>(
                File.ReadAllText(Path.Combine(directory, "cache-manifest.json")));
            return manifest is not null && manifest.ContainsKey(".lake/build/lib/lean/CIL.olean") && Same(manifest, CacheFiles(directory));
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException)
        {
            return false;
        }
    }

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
        return (Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(
            "leancil-library-v3-kernel-replayed\n" + System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier + "\n" +
            Sha(Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker")) + "\n" + Sha(compiler) + "\n" + JsonSerializer.Serialize(sources)))),
            sources);
    }

    string Library(SortedDictionary<string, string> snapshot)
    {
        var common = new SortedDictionary<string, string>(snapshot.Where(p =>
            !p.Key.StartsWith("proof:", StringComparison.Ordinal) && !p.Key.StartsWith("settings:", StringComparison.Ordinal)).ToDictionary(), StringComparer.Ordinal);
        if (library is not null)
        {
            if (!Same(common, libraryInputs!))
                throw new InvalidOperationException("Proof session source inputs changed");
            return library;
        }

        (libraryKey, var sources) = LibraryIdentity(common);
        var toolchain = Toolchain;
        library = Path.Combine(Path.GetTempPath(), "leancil-library-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(library);
        var fresh = freshLibrary ||
            string.Equals(Environment.GetEnvironmentVariable("CI"), "true", StringComparison.OrdinalIgnoreCase) ||
            string.Equals(Environment.GetEnvironmentVariable("GITHUB_ACTIONS"), "true", StringComparison.OrdinalIgnoreCase);
        var cacheRoot = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
            Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries");
        var cached = Path.Combine(cacheRoot, libraryKey);
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
            // A supplied certified library is not a local cache, so --fresh still uses it.
            if (!string.IsNullOrWhiteSpace(supplied))
            {
                var copyStarted = DateTimeOffset.UtcNow;
                var copyElapsed = Stopwatch.StartNew();
                if (!CopyCertifiedLibrary(supplied, library, suppliedDigest, libraryKey, sources))
                    throw new InvalidOperationException("Certified library identity or integrity mismatch");
                if (!ValidCertifiedLibrary(library, suppliedDigest, libraryKey, sources))
                    throw new InvalidOperationException("Certified library changed while copying");
                var manifestBytes = File.ReadAllBytes(Path.Combine(library, "cache-manifest.json"));
                if (Convert.ToHexStringLower(SHA256.HashData(manifestBytes)) != suppliedDigest)
                    throw new InvalidDataException("Certified library manifest changed before metadata binding.");
                certifiedFingerprintsSha = JsonSerializer.Deserialize<SortedDictionary<string, string>>(manifestBytes)?
                    .GetValueOrDefault(CertifiedFingerprintsName);
                libraryBuild = "certified-artifact";
                Trace("Copying certified Lean verification library", copyStarted, library, copyElapsed.Elapsed, 0, "", [supplied, library]);
            }
            else if (!fresh && CertifiedLocalLibrary(cached, libraryKey) && ValidCache(cached) && Same(sources, LibrarySources(CacheFiles(cached))))
            {
                CopyTree(cached, library);
                if (!ValidCache(library))
                    throw new InvalidOperationException("Library cache changed while copying");
                libraryBuild = "cache";
            }
            else
            {
                foreach (var (name, hash) in sources)
                {
                    var destination = Path.Combine(library, name);
                    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                    File.Copy(At(name), destination);
                    if (Sha(destination) != hash)
                        throw new InvalidOperationException("Library source changed while copying: " + name);
                }
                Run(["lake", "build", "CIL", "leancil-audit"], library, streamOutput: true, progress: "Building fresh Lean verification library");
                var checker = Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
                var compiledLibrary = Path.Combine(library, ".lake/build/lib/lean");
                if (!ReplayModulesJointly(library, [.. ModuleArtifacts(library).Keys.Select(ModuleName).Distinct().Order(StringComparer.Ordinal)],
                    compiledLibrary, "Joint kernel replay of fresh Lean verification library"))
                    Run([checker, "CIL"], library, compiledLibrary, streamOutput: true,
                        progress: "Kernel replay of fresh Lean verification library");
                libraryBuild = "fresh";
                if (!fresh)
                {
                    File.WriteAllText(Path.Combine(library, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(library), Json));
                    File.WriteAllBytes(Path.Combine(library, "cache-receipt.hmac"), HMACSHA256.HashData(ReceiptKey,
                        Encoding.UTF8.GetBytes(libraryKey).Concat(File.ReadAllBytes(Path.Combine(library, "cache-manifest.json"))).ToArray()));
                    var staging = cached + "." + Guid.NewGuid().ToString("N");
                    try
                    {
                        CopyTree(library, staging);
                        if (Directory.Exists(cached)) Directory.Delete(cached, true);
                        Directory.Move(staging, cached);
                    }
                    finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
                }
            }
        }
        finally { cacheLock?.Dispose(); }
        // Support builds mutate only this private session, never the shared base cache.
        foreach (var name in common.Keys.Where(name => name.EndsWith(".lean", StringComparison.Ordinal) && !sources.ContainsKey(name)))
        {
            var destination = Path.Combine(library, name);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(At(name), destination, true);
        }
        certifiedModules = ModuleArtifacts(library);
        libraryInputs = common;
        // Bound before any proof or support build can run code in this session.
        auditExecutable = Path.Combine(library, ".lake/build/bin", OperatingSystem.IsWindows() ? "leancil-audit.exe" : "leancil-audit");
        auditExecutableSha = File.Exists(auditExecutable) ? Sha(auditExecutable) : null;
        // Workflow artifacts drop the mode bits that the cache manifest does not cover.
        if (!OperatingSystem.IsWindows() && auditExecutableSha is not null)
            File.SetUnixFileMode(auditExecutable, File.GetUnixFileMode(auditExecutable) | UnixFileMode.UserExecute);
        return library;
    }

    string PrepareLibrary(string destination, string? trustedDigest = null)
    {
        if (trustedDigest is not null)
            return ReusePreparedLibrary(destination, trustedDigest) ??
                throw new InvalidOperationException("Certified library identity or integrity mismatch; destination left unchanged");
        destination = Path.GetFullPath(destination);
        if (Directory.Exists(destination) && Directory.EnumerateFileSystemEntries(destination).Any())
            throw new InvalidOperationException("Certified library destination must be empty");
        var session = Library(Inputs(At("CIL.lean")));
        var staging = destination.TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar) + "." + Guid.NewGuid().ToString("N");
        try
        {
            CopyTree(session, staging);
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

    // A manifest authenticates contents only when its digest comes independently from a trusted producer.
    // Kernel replay cannot authenticate the native auditor or establish compiled-to-source correspondence.
    string? ReusePreparedLibrary(string directory, string? trustedDigest)
    {
        // Replay runs inside the library, so a relative Lean path would resolve below it.
        directory = Path.GetFullPath(directory);
        var manifest = Path.Combine(directory, "cache-manifest.json");
        if (string.IsNullOrWhiteSpace(trustedDigest) || !File.Exists(manifest) || Sha(manifest) != trustedDigest) return null;
        var snapshot = Inputs(At("CIL.lean"));
        var (key, sources) = LibraryIdentity(new(snapshot.Where(p => !p.Key.StartsWith("proof:", StringComparison.Ordinal) &&
            !p.Key.StartsWith("settings:", StringComparison.Ordinal)).ToDictionary(), StringComparer.Ordinal));
        if (!ValidCertifiedLibrary(directory, trustedDigest, key, sources)) return null;
        var compiled = Path.Combine(directory, ".lake/build/lib/lean");
        if (!ReplayModulesJointly(directory, [.. ModuleArtifacts(directory).Keys.Select(ModuleName).Distinct().Order(StringComparer.Ordinal)],
            compiled, "Joint kernel replay of reused Lean verification library"))
            Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"), "CIL"], directory, compiled,
                streamOutput: true, progress: "Kernel replay of reused Lean verification library");
        return ValidCertifiedLibrary(directory, trustedDigest, key, sources) ? trustedDigest : null;
    }

    SortedDictionary<string, string> SupportInputs(string session, string[] roots, SortedDictionary<string, string> snapshot)
    {
        var rootKey = string.Join("\n", roots.Order(StringComparer.Ordinal));
        if (supportSourceKeys.TryGetValue(rootKey, out var known)) return known;
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);
        var pending = new Queue<string>(roots);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var compiled = Path.GetFullPath(Path.Combine(session, ".lake/build/lib/lean"));
        while (pending.TryDequeue(out var module))
        {
            if (!seen.Add(module)) continue;
            var relative = module.Replace('.', '/') + ".lean";
            if (!snapshot.TryGetValue(relative, out var hash))
                return Conservative();
            result[relative] = hash;
            var dependencies = Execute(["lean", "--deps", Path.Combine(session, relative)], session, compiled);
            if (dependencies.Code != 0) return Conservative();
            foreach (var dependency in dependencies.Stdout.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
            {
                var path = Path.GetFullPath(dependency);
                if (path.StartsWith(Path.GetFullPath(Toolchain) + Path.DirectorySeparatorChar, StringComparison.OrdinalIgnoreCase)) continue;
                var name = Path.GetRelativePath(compiled, path).Replace('\\', '/');
                if (name.StartsWith("../", StringComparison.Ordinal) || !name.EndsWith(".olean", StringComparison.Ordinal)) return Conservative();
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

    // Proofs opt in to PDB names and locations with `import ExtractedSymbols`.
    static bool ImportsSymbols(string proof) => SourceImport().Matches(proof).Any(import => import.Groups[1].Value == "ExtractedSymbols");

    static string SymbolsFor(string output) => Path.Combine(output, "Symbols.lean") is var path && File.Exists(path) ? path
        : throw new InvalidOperationException(MissingSymbols(output));

    static string MissingSymbols(string output)
    {
        var identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
        return "The proof imports ExtractedSymbols, but extraction found no matching portable PDB; build the assembly with its .pdb next to it and extract again, or remove the import.\n" +
            "  Assembly: " + Path.GetFullPath(identity.GetProperty("assemblyPath").GetString()!, output) + "\n" +
            "  Method: " + identity.GetProperty("entry").GetString();
    }

    static string[] Extract(string mode, string assembly, string? identity, string entry, string output, string profile = "scalar") =>
        ["dotnet", ExtractorPath, mode, assembly, entry, output, profile,
            .. identity is null ? Array.Empty<string>() : ["--assembly", identity]];

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

    sealed record AuditRequest(string name, object? type = null, string[]? axioms = null, bool statement = false, bool refutation = false);
    sealed record AuditRefutation(string contract, int line, int column);
    sealed record AuditedTheorem(string name, string? error, string[]? axioms, string? statement, AuditRefutation? refutes);
    sealed record AuditConstantRequest(string name, object value, object? type = null, string[]? axioms = null);
    sealed record AuditedInterfaces(string? error);
    sealed record AuditedClosure(string name, string? error, string? kind, string? canonical);
    sealed record AuditNamespaces(string[] prefixes, string[] axioms);
    sealed record AuditedNamespaces(int count, Dictionary<string, int> prefixes, Dictionary<string, int> modules, string[] axioms,
        AuditedTheorem[] rejected, string? error);
    sealed record AuditedOleans(Dictionary<string, string> modules, AuditedTheorem[] theorems, AuditedTheorem[] constants,
        AuditedInterfaces? interfaces = null, AuditedClosure[]? closures = null, AuditedNamespaces? namespaces = null);

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
        if (auditExecutable is null || !File.Exists(auditExecutable) || Sha(auditExecutable) != auditExecutableSha)
            throw new InvalidOperationException("Theorem audit executable is missing or changed during verification");
        return auditExecutable;
    }

    // Reads the kernel-replayed oleans only: no imported elaborator, notation, extension or initializer runs.
    AuditedOleans AuditOleans(string leanPath, string[] modules, AuditRequest[] theorems, AuditConstantRequest[]? constants = null,
        string[]? interfaces = null, string[]? closures = null, AuditNamespaces? namespaces = null)
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
                closures = closures.Select(name => new { name }), namespaces }, AuditJson));
            Run([executable, request, result], leanPath: leanPath, environment: LeanEnvironment);
            var audited = JsonSerializer.Deserialize<AuditedOleans>(File.ReadAllText(result))
                ?? throw new InvalidDataException("Missing theorem audit result");
            if (audited.theorems.Length != theorems.Length || audited.theorems.Zip(theorems).Any(pair => pair.First.name != pair.Second.name) ||
                audited.constants.Length != constants.Length || audited.constants.Zip(constants).Any(pair => pair.First.name != pair.Second.name) ||
                modules.Any(module => !audited.modules.ContainsKey(module)) || audited.interfaces is null || audited.closures is null ||
                audited.closures.Length != closures.Length || audited.closures.Zip(closures).Any(pair => pair.First.name != pair.Second) ||
                (namespaces is not null && (audited.namespaces?.prefixes is null || audited.namespaces.modules is null ||
                    audited.namespaces.axioms is null || audited.namespaces.rejected is null)))
                throw new InvalidDataException("Incomplete theorem audit result");
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
    void CheckContractInterfaces(ExtractionIdentity extraction, string[] modules, string leanPath, Func<string, string> artifact)
    {
        string[] interfaces = modules.Where(module => module != "ExtractedImports").ToArray();
        JsonElement[] imports = extraction.Imports;
        if (interfaces.Length == 0 && imports.Length == 0) return;
        if (interfaces.Length == 0) throw new InvalidDataException("Contract imports without a published interface module");
        string[] constants = imports.Select(import => import.GetProperty("contractConstant").GetString()!).Distinct(StringComparer.Ordinal).ToArray();
        AuditedOleans audited = AuditOleans(leanPath, interfaces, [], interfaces: interfaces, closures: constants);
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

    // An untrusted build may add only its own module's oleans; any other change voids the replayed set.
    static void RequireOnlyAdded(SortedDictionary<string, string> bound, SortedDictionary<string, string> built, string module)
    {
        if (bound.Any(pair => !built.TryGetValue(pair.Key, out var hash) || hash != pair.Value) ||
            built.Keys.Any(name => !bound.ContainsKey(name) && !name.StartsWith(module + ".olean", StringComparison.Ordinal)))
            throw new InvalidOperationException("Compiled artifacts changed during verification");
    }

    sealed record Report(int schema, string assemblySha256, string identitySha256, string theorem, string[] axioms,
        string theoremAudit, SortedDictionary<string, string> inputs, string? libraryKey = null, string? libraryBuild = null,
        string? extractionAudit = null, string[]? initializedTypes = null,
        string? batchSourceSha256 = null, string? batchTheorem = null, string? consumerSupportSha256 = null,
        string[]? staticValues = null, string[]? contractImports = null, PublishedImport[]? imports = null,
        DeploymentDependency[]? contractDependencies = null, string? compositionTheorem = null, string? compositionAudit = null,
        JsonElement[]? initializationAssumptions = null);

    static JsonElement[] InitializationAssumptions(JsonElement extraction) =>
        extraction.TryGetProperty("initializationAssumptions", out var assumptions)
            ? assumptions.EnumerateArray().ToArray() : [];

    static string[] StaticValueAssumptions(JsonElement extraction) =>
        extraction.TryGetProperty("staticValues", out var values) ? values.Deserialize<string[]>() ?? [] : [];

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
            Run(Extract("check", assembly, identity, entry, output, profile));

            if (old.schema != 4 || string.IsNullOrWhiteSpace(old.extractionAudit) || !Same(old.inputs, Inputs(proof, settings)) || old.identitySha256 != Sha(Path.Combine(output, "identity.json")) ||
                old.theorem != theorem || old.assemblySha256 != Sha(assembly) ||
                (old.batchSourceSha256 is not null && (string.IsNullOrWhiteSpace(old.batchTheorem) ||
                    old.batchSourceSha256 != Sha(Path.Combine(output, "Batch.lean")))))
                throw new InvalidOperationException("Stale verification report or changed proof inputs");

            return old;
        }

        // A failed attempt must not leave an earlier successful report behind.
        File.Delete(reportPath);
        stage?.Invoke("extraction integrity");
        if (existingArtifacts)
            Run(["dotnet", ExtractorPath, "check", output]);
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

        // Retain the selected bytes before support or interface builds can run code.
        void RequireOriginalProofSources()
        {
            if (!File.Exists(proof) || Sha(proof) != proofSourceHash ||
                symbolsSource is not null && (!File.Exists(symbolsSource) || Sha(symbolsSource) != symbolsSourceHash))
                throw new InvalidOperationException("Proof inputs changed during verification");
        }

        // Use a source-bound build; CI and --fresh bypass the local library cache.
        stage?.Invoke("Lean library build");
        var session = Library(before);
        HashSet<string> importSourceNames = extraction.Sources.Keys.ToHashSet(StringComparer.Ordinal);
        var support = Regex.Matches(proofSource, @"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", RegexOptions.Multiline)
            .Select(m => m.Groups[1].Value).Where(n => n is not ("Extracted" or "ExtractedSymbols") && !importSourceNames.Contains(n) && n.Split('.')[0] is not ("Init" or "Lean" or "Std")).ToArray();

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
                        var current = ModuleArtifacts(session);
                        var altered = certifiedModules!.Any(pair => !current.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
                        var changed = (altered ? current : current.Where(pair => !certifiedModules!.ContainsKey(pair.Key)))
                            .Select(pair => ModuleName(pair.Key)).Distinct().ToArray();
                        if (changed.Length > 0)
                        {
                            stage?.Invoke("kernel replay");
                            Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"), .. changed],
                                leanPath: Path.Combine(session, ".lake/build/lib/lean"), progress: "Kernel replay of proof dependencies: " + entry);
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
        void RequireStagedProofSources()
        {
            if (!File.Exists(stagedProof) || Sha(stagedProof) != proofSourceHash)
                throw new InvalidOperationException("Proof sources changed during verification: Proof.lean");
            if (symbols && (!File.Exists(stagedSymbols) || Sha(stagedSymbols) != symbolsSourceHash))
                throw new InvalidOperationException("Proof sources changed during verification: ExtractedSymbols.lean");
        }

        try
        {
            File.Copy(Path.Combine(output, "Extracted.lean"), Path.Combine(fresh, "Extracted.lean"));
            if (Sha(Path.Combine(fresh, "Extracted.lean")) != extraction.Root.GetProperty("generatedSha256").GetString())
                throw new InvalidOperationException("Inputs changed during verification");
            string[] importModules = StageImportSources(extraction, fresh);
            File.WriteAllText(Path.Combine(fresh, "ExtractionAudit.lean"), ExtractionAuditSource);
            var leanPath = fresh + Path.PathSeparator + Path.Combine(session, ".lake/build/lib/lean");

            var currentModules = ModuleArtifacts(session);
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
            var extractedKey = ContentKey("extraction-audit-v2\n" + environmentKey + "\n" +
                Sha(Path.Combine(fresh, "Extracted.lean")) + "\n" + ExtractionAuditSource);
            string? extractionPublication = null;
            if (RestoreSuccess(extractedKey, fresh))
            {
                extractionAudit = File.ReadAllText(Path.Combine(fresh, "extraction-audit.txt"));
                extractionCacheHits++;
                CacheProgress("certified extraction: " + entry);
            }
            else
            {
                foreach (var name in new[] { "Extracted", "ExtractionAudit" })
                {
                    stage?.Invoke(name == "ExtractionAudit" ? "extraction certificate audit" : "proof checking");
                    var checkedOutput = Run([LeanExecutable, "--root=" + fresh, "-o", Path.Combine(fresh, name + ".olean"), Path.Combine(fresh, name + ".lean")],
                        leanPath: leanPath, progress: $"Checking {name}: {entry}");
                    if (name == "ExtractionAudit") extractionAudit = checkedOutput;
                }
                var publication = Path.Combine(fresh, "extraction-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path =>
                    Path.GetFileName(path).StartsWith("Extracted.olean", StringComparison.Ordinal) ||
                    Path.GetFileName(path).StartsWith("ExtractionAudit.olean", StringComparison.Ordinal)))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                extractionPublication = publication;
            }
            // Interfaces, symbols and the proof each run code when built: each build may add only its own oleans.
            var bound = OleanHashes(fresh, session);
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
                ReplayCheckedModules(importModules, leanPath,
                    "Kernel replay of published contract interfaces and App import assumptions");
                CheckContractInterfaces(extraction, importModules, leanPath, module => Path.Combine(fresh, module.Replace('.', '/') + ".olean"));
                if (!Same(bound, OleanHashes(fresh, session)))
                    throw new InvalidOperationException("Compiled artifacts changed during verification");
                RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            }
            if (File.Exists(stagedProof))
                throw new InvalidOperationException("Proof sources changed during verification: Proof.lean");
            if (File.Exists(stagedSymbols))
                throw new InvalidOperationException("Proof sources changed during verification: ExtractedSymbols.lean");
            RequireOriginalProofSources();
            File.WriteAllBytes(stagedProof, proofSourceBytes);
            if (symbols) File.WriteAllBytes(stagedSymbols, symbolsSourceBytes!);
            RequireStagedProofSources();
            if (symbols)
            {
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.Combine(fresh, "ExtractedSymbols.olean"), stagedSymbols],
                    leanPath: leanPath, progress: "Checking ExtractedSymbols: " + entry);
                var next = OleanHashes(fresh, session);
                RequireOnlyAdded(bound, next, "ExtractedSymbols");
                bound = next;
                RequireStagedProofSources();
            }
            RequireStagedProofSources();
            var proofKey = ContentKey("theorem-audit-v2\n" + extractedKey + "\n" + proofSourceHash + "\n" +
                (symbols ? symbolsSourceHash + "\n" : "") +
                SemanticExtractionIdentity(extraction) + "\n" + JsonSerializer.Serialize(extraction.Sources) + "\n" +
                JsonSerializer.Serialize(acceptedInterfaceArtifacts) + "\n" + theorem);
            var proofRestored = RestoreSuccess(proofKey, fresh);
            if (proofRestored)
            {
                proofCacheHits++;
                CacheProgress("certified proof: " + entry);
            }
            else
            {
                stage?.Invoke("proof checking");
                RequireStagedProofSources();
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.Combine(fresh, "Proof.olean"), stagedProof],
                    leanPath: leanPath, progress: "Checking Proof: " + entry);
            }
            RequireStagedProofSources();
            var built = OleanHashes(fresh, session);
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            RequireOnlyAdded(bound, built, "Proof");
            // Interface oleans were replayed above and RequireOnlyAdded kept them unchanged since.
            string[] replay = [.. extractionPublication is null ? Array.Empty<string>() : ["Extracted", "ExtractionAudit"],
                .. symbols && !proofRestored ? ["ExtractedSymbols"] : Array.Empty<string>(), .. proofRestored ? Array.Empty<string>() : ["Proof"]];
            if (replay.Length > 0)
            {
                stage?.Invoke("kernel replay");
                ReplayCheckedModules(replay, leanPath,
                    (proofRestored ? "Kernel replay of extraction: " : "Kernel replay: ") + entry);
            }
            // The audit reads the bytes leanchecker replayed: nothing may change until it finishes.
            stage?.Invoke("theorem audit");
            string[] auditModules = ["Proof", "ExtractionAudit", .. HasContractImports(extraction) ? ["ExtractedImports"] : Array.Empty<string>()];
            RequireStagedProofSources();
            var audited = AuditOleans(leanPath, auditModules, [ProofTheorem(theorem, extraction), ExtractionCertificate("ExtractionAudit.valid")], ImportPremise(extraction));
            RequireStagedProofSources();
            if (!Same(built, OleanHashes(fresh, session)))
                throw new InvalidOperationException("Compiled artifacts changed during verification");
            RequireAuditedModule(audited, "Proof", Path.Combine(fresh, "Proof.olean"));
            RequireAuditedModule(audited, "ExtractionAudit", Path.Combine(fresh, "ExtractionAudit.olean"));
            if (HasContractImports(extraction))
                RequireAuditedModule(audited, "ExtractedImports", Path.Combine(fresh, "ExtractedImports.olean"));
            RequireAuditedConstants(audited);
            stage?.Invoke("extraction certificate audit");
            AuditedAxioms(audited.theorems[1]);
            stage?.Invoke("theorem audit");
            axioms = AuditedAxioms(audited.theorems[0]);
            audit = AuditText(audited.theorems[0]);
            RequireOriginalProofSources();
            RequireStagedProofSources();
            RequireOriginalProofSources();
            if (!Same(before, Inputs(proof, settings)) || identityHash != Sha(Path.Combine(output, "identity.json")))
                throw new InvalidOperationException("Inputs changed during verification");
            if (!proofRestored)
            {
                var publication = Path.Combine(fresh, "proof-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path => Path.GetFileName(path).StartsWith("Proof.olean", StringComparison.Ordinal)))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
                PublishSuccess(proofKey, publication);
            }
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            if (extractionPublication is not null)
            {
                extractionAudit += AuditText(audited.theorems[1]);
                File.WriteAllText(Path.Combine(extractionPublication, "extraction-audit.txt"), extractionAudit);
                PublishSuccess(extractedKey, extractionPublication);
            }
            fullResult = fullImportAudit?.Invoke(output, fresh, "Proof", leanPath);

            // Bind the report only after confirming inputs stayed unchanged.
            stage?.Invoke("extraction integrity");
            Run(existingArtifacts ? ["dotnet", ExtractorPath, "check", output] : Extract("check", assembly, identity, entry, output, profile));

            RequireOriginalProofSources();
            if (!Same(before, Inputs(proof, settings)) || identityHash != Sha(Path.Combine(output, "identity.json")))
                throw new InvalidOperationException("Inputs changed during verification");

            var initializedTypes = extraction.Root.TryGetProperty("initializedTypes", out var assumptions)
                ? assumptions.Deserialize<string[]>() : [];
            RequireImplementationImports(extraction);
            var report = new Report(4, Sha(assembly), identityHash, theorem, axioms, audit, before, libraryKey, libraryBuild, extractionAudit, initializedTypes,
                staticValues: StaticValueAssumptions(extraction.Root), contractImports: ContractImportAssumptions(extraction.Root),
                imports: fullResult?.Imports ?? PublishedImports(extraction.Root),
                contractDependencies: fullResult?.Dependencies ?? DeploymentDependencies(extraction.Root),
                compositionTheorem: fullResult?.Theorem, compositionAudit: fullResult?.Audit,
                initializationAssumptions: InitializationAssumptions(extraction.Root));
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");

            return report;
        }
        finally
        {
            Directory.Delete(fresh, true);
        }
    }

    void IDisposable.Dispose()
    {
        if (library is not null && Directory.Exists(library))
            Directory.Delete(library, true);
    }
}
