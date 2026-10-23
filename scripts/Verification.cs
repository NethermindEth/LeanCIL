using System.Diagnostics;
using System.Runtime.CompilerServices;
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
    string? resolvedToolchain;
    bool extractorBuilt;
    int extractionCacheHits;
    int proofCacheHits;
    int supportCacheHits;
    SortedDictionary<string, string>? certifiedModules;

    byte[]? receiptKey;
    readonly HashSet<string> preparedSupport = new(StringComparer.Ordinal);
    string? verificationPolicy;
    string VerificationPolicy => verificationPolicy ??= Sha(typeof(Program).Assembly.Location);
    readonly Dictionary<string, SortedDictionary<string, string>> supportSourceKeys = new(StringComparer.Ordinal);

    bool UseSuccessCache => !freshLibrary &&
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

    // Per-module replay re-imports each module's dependencies; one shared import of
    // everything outside the targets makes large sets several times cheaper.
    // No target constant may preexist, since Replay skips matching theorems unchecked.
    const string JointReplaySource = """
import LeanChecker
unsafe def readReplayParts (module : Lean.Name) : IO (Lean.ModuleData × Lean.ModuleData) := do
  let mFile ← Lean.findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := Lean.OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := Lean.OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← Lean.readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  return (parts[0].1, parts[parts.size-1].1)
-- The duplicate rule of `finalizeImport` and `Replay`: on-demand equation lemmas recur across modules.
def sameReplayTheorem : Lean.ConstantInfo → Lean.ConstantInfo → Bool
  | .thmInfo a, .thmInfo b => a.name == b.name && a.type == b.type && a.levelParams == b.levelParams && a.all == b.all
  | _, _ => false
unsafe def replayModulesJointly (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let started ← IO.monoMsNow
  let names := args.map String.toName
  let targets : Lean.NameSet := names.foldl (·.insert ·) {}
  let mut imports : Std.HashMap Lean.Name Lean.Import := {}
  let mut constants : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for module in names do
    let (exported, complete) ← readReplayParts module
    for i in exported.imports do
      unless targets.contains i.module do
        imports := imports.insert i.module <| match imports[i.module]? with
          | some j => { j with importAll := j.importAll || i.importAll, isExported := j.isExported || i.isExported, isMeta := j.isMeta || i.isMeta }
          | none => i
    -- The most private part subsumes the others.
    for name in complete.constNames, ci in complete.constants do
      match constants[name]? with
      | some prior =>
        unless sameReplayTheorem prior ci do
          throw <| IO.userError s!"Constant {name} is declared by more than one replay target"
      | none => constants := constants.insert name ci
  let external := imports.toArray.map (·.2) |>.qsort (·.module.toString < ·.module.toString)
  let (_, s) ← Lean.importModulesCore external |>.run
  let env ← Lean.finalizeImport s external {} 0 false false (isModule := true)
  let imported := env.allImportedModuleNames
  for (name, ci) in constants do
    if let some prior := env.find? name then
      -- Only an identical theorem from an untargeted module may be skipped, as per-module replay would.
      let owner := (env.getModuleIdxFor? name).bind (imported[·.toNat]?)
      unless owner.any (!targets.contains ·) && sameReplayTheorem prior ci do
        throw <| IO.userError s!"Replay target constant {name} is already imported"
  discard <| env.toKernelEnv.replay constants
  env.freeRegions
  let elapsed := (← IO.monoMsNow) - started
  for name in args do
    IO.println (Lean.Json.mkObj [("module", Lean.toJson name), ("joint", Lean.toJson true), ("milliseconds", Lean.toJson elapsed)]).compress
""";

    // False when the set is ineligible or any declaration is rejected; callers then replay per module.
    bool ReplayModulesJointly(string cwd, string[] targets, string leanPath, string progress)
    {
        var runner = Path.Combine(Path.GetTempPath(), "leancil-joint-replay-" + Guid.NewGuid().ToString("N") + ".lean");
        var targetsPath = Path.ChangeExtension(runner, ".json");
        try
        {
            File.WriteAllText(targetsPath, JsonSerializer.Serialize(targets));
            File.WriteAllText(runner, JointReplaySource + "\n#eval do\n  let json ← IO.FS.readFile (String.fromUTF8! (ByteArray.mk #[" +
                string.Join(",", System.Text.Encoding.UTF8.GetBytes(targetsPath)) +
                "]))\n  let args ← IO.ofExcept <| (Lean.Json.parse json).bind Lean.fromJson?\n  replayModulesJointly args\n");
            var result = Execute([LeanExecutable, runner], cwd, leanPath, progress: progress, environment: LeanEnvironment);
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

    static SortedDictionary<string, string> ModuleArtifacts(string session) =>
        new(Directory.EnumerateFiles(Path.Combine(session, ".lake/build/lib/lean"), "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
            .ToDictionary(path => Path.GetRelativePath(Path.Combine(session, ".lake/build/lib/lean"), path).Replace('\\', '/'), Sha), StringComparer.Ordinal);

    static string ModuleName(string artifact) => artifact.Split(".olean", 2)[0].Replace('/', '.');

    string Toolchain => resolvedToolchain ??= Run(["lean", "--print-prefix"]).Trim();
    SortedDictionary<string, string>? libraryInputs;

    static string At(string path) => Path.Combine(Root, path);

    static string Sha(string path) => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));

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
        if (!string.IsNullOrWhiteSpace(traceDirectory))
        {
            // Concurrent commands in one process append to the same trace file.
            lock (TraceGate)
                File.AppendAllText(Path.Combine(traceDirectory, $"{Environment.ProcessId}.jsonl"), JsonSerializer.Serialize(new {
                stage = traceStage ?? string.Join(" ", args.Take(2)), startedAtUtc, processId = Environment.ProcessId,
                cwd = start.WorkingDirectory, durationSeconds = elapsed.Elapsed.TotalSeconds,
                exitCode = process.ExitCode, transcript, command = args,
                suite = Environment.GetEnvironmentVariable("LEANCIL_SUITE")
            }) + "\n");
        }
        return (process.ExitCode, output + error, output, error);
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
        new(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path) is not ("cache-manifest.json" or "cache-receipt.hmac"))
            .ToDictionary(path => Path.GetRelativePath(directory, path).Replace('\\', '/'), Sha), StringComparer.Ordinal);

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
            return !string.IsNullOrWhiteSpace(trustedDigest) &&
                Sha(Path.Combine(directory, "cache-manifest.json")) == trustedDigest && ValidCache(directory) &&
                File.ReadAllText(Path.Combine(directory, "library-key.txt")) == key &&
                Same(sources, LibrarySources(CacheFiles(directory)));
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return false; }
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

        var sources = LibrarySources(common);
        // Include the resolved toolchain, platform and cache format, not the selected proof.
        var toolchain = Toolchain;
        var compiler = Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean");
        libraryKey = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(
            "leancil-library-v3-kernel-replayed\n" + System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier + "\n" +
            Sha(Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker")) + "\n" + Sha(compiler) + "\n" + JsonSerializer.Serialize(sources))));
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
            if (!freshLibrary && !string.IsNullOrWhiteSpace(supplied))
            {
                if (!ValidCertifiedLibrary(supplied, suppliedDigest, libraryKey, sources))
                    throw new InvalidOperationException("Certified library identity or integrity mismatch");
                CopyTree(supplied, library);
                if (!ValidCertifiedLibrary(library, suppliedDigest, libraryKey, sources))
                    throw new InvalidOperationException("Certified library changed while copying");
                libraryBuild = "certified-artifact";
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

    string PrepareLibrary(string destination)
    {
        var session = Library(Inputs(At("CIL.lean")));
        if (Directory.Exists(destination) && Directory.EnumerateFileSystemEntries(destination).Any())
            throw new InvalidOperationException("Certified library destination must be empty");
        Directory.CreateDirectory(destination);
        CopyTree(session, destination);
        File.WriteAllText(Path.Combine(destination, "library-key.txt"), libraryKey);
        File.WriteAllText(Path.Combine(destination, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(destination), Json));
        return Sha(Path.Combine(destination, "cache-manifest.json"));
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

    // Proofs opt in to PDB names and locations with `import ExtractedSymbols`.
    static bool ImportsSymbols(string proof) => Regex.IsMatch(proof,
        @"^(?:(?:public|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?ExtractedSymbols[ \t]*\r?$", RegexOptions.Multiline);

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
    sealed record AuditedOleans(Dictionary<string, string> modules, AuditedTheorem[] theorems, AuditedTheorem[] constants);

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

    // Reads the kernel-replayed oleans only: no imported elaborator, notation, extension or initializer runs.
    AuditedOleans AuditOleans(string leanPath, string[] modules, AuditRequest[] theorems, AuditConstantRequest[]? constants = null)
    {
        if (auditExecutable is null || !File.Exists(auditExecutable) || Sha(auditExecutable) != auditExecutableSha)
            throw new InvalidOperationException("Theorem audit executable is missing or changed during verification");
        var request = Path.Combine(Path.GetTempPath(), "leancil-audit-" + Guid.NewGuid().ToString("N") + ".json");
        var result = Path.ChangeExtension(request, ".result.json");
        try
        {
            constants ??= [];
            File.WriteAllText(request, JsonSerializer.Serialize(new { modules, theorems, constants }, AuditJson));
            Run([auditExecutable, request, result], leanPath: leanPath, environment: LeanEnvironment);
            var audited = JsonSerializer.Deserialize<AuditedOleans>(File.ReadAllText(result))
                ?? throw new InvalidDataException("Missing theorem audit result");
            if (audited.theorems.Length != theorems.Length || audited.theorems.Zip(theorems).Any(pair => pair.First.name != pair.Second.name) ||
                audited.constants.Length != constants.Length || audited.constants.Zip(constants).Any(pair => pair.First.name != pair.Second.name) ||
                modules.Any(module => !audited.modules.ContainsKey(module)))
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

    static string[] AuditedAxioms(AuditedTheorem audited)
    {
        if (audited.error is not null) throw new InvalidOperationException(audited.error);
        var axioms = audited.axioms ?? throw new InvalidDataException("Missing transitive theorem axiom audit");
        if (axioms.Any(a => !ApprovedAxioms.Contains(a)))
            throw new InvalidOperationException("Unapproved proof axioms: " + string.Join(", ", axioms));
        return axioms;
    }

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
        string[]? staticValues = null);

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

            if (old.schema != 3 || string.IsNullOrWhiteSpace(old.extractionAudit) || !Same(old.inputs, Inputs(proof, settings)) || old.identitySha256 != Sha(Path.Combine(output, "identity.json")) ||
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
        else if (!extractorBuilt)
        {
            Run(["dotnet", "build", "Extractor", "-c", "Release", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
            extractorBuilt = true;
        }

        // Use a source-bound build; CI and --fresh bypass the local library cache.
        stage?.Invoke("Lean library build");
        var before = Inputs(proof, settings);
        var session = Library(before);
        var support = Regex.Matches(File.ReadAllText(proof), @"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", RegexOptions.Multiline)
            .Select(m => m.Groups[1].Value).Where(n => n is not ("Extracted" or "ExtractedSymbols") && n.Split('.')[0] is not ("Init" or "Lean" or "Std")).ToArray();

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

        if (!existingArtifacts)
            Run(Extract("extract", assembly, identity, entry, output, profile));
        var identityHash = Sha(Path.Combine(output, "identity.json"));

        // Isolate generated code and the selected proof, then audit the named theorem.
        var fresh = Path.Combine(output, "proof-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(fresh);
        string audit;
        string extractionAudit = "";
        string[] axioms;

        try
        {
            File.Copy(Path.Combine(output, "Extracted.lean"), Path.Combine(fresh, "Extracted.lean"));
            File.Copy(proof, Path.Combine(fresh, "Proof.lean"));
            var symbols = ImportsSymbols(File.ReadAllText(proof));
            if (symbols) File.Copy(SymbolsFor(output), Path.Combine(fresh, "ExtractedSymbols.lean"));
            File.WriteAllText(Path.Combine(fresh, "ExtractionAudit.lean"), ExtractionAuditSource);
            var leanPath = fresh + Path.PathSeparator + Path.Combine(session, ".lake/build/lib/lean");

            var checker = Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
            var currentModules = ModuleArtifacts(session);
            var alteredExisting = certifiedModules!.Any(pair => !currentModules.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
            var changedModules = (alteredExisting ? currentModules.Keys : currentModules.Keys.Where(name => !certifiedModules!.ContainsKey(name)))
                .Select(ModuleName).Distinct().ToArray();
            if (changedModules.Length > 0)
            {
                stage?.Invoke("kernel replay");
                Run([checker, .. changedModules], leanPath: leanPath, progress: "Kernel replay of proof dependencies: " + entry);
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
                    var checkedOutput = Run(["lean", "--root=" + fresh, "-o", Path.Combine(fresh, name + ".olean"), Path.Combine(fresh, name + ".lean")],
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
            if (symbols)
                Run(["lean", "--root=" + fresh, "-o", Path.Combine(fresh, "ExtractedSymbols.olean"), Path.Combine(fresh, "ExtractedSymbols.lean")],
                    leanPath: leanPath, progress: "Checking ExtractedSymbols: " + entry);
            var proofKey = ContentKey("theorem-audit-v2\n" + extractedKey + "\n" + Sha(Path.Combine(fresh, "Proof.lean")) + "\n" +
                (symbols ? Sha(Path.Combine(fresh, "ExtractedSymbols.lean")) + "\n" : "") + theorem);
            // Building the proof runs its code; every olean but its own must survive that build unchanged.
            var bound = OleanHashes(fresh, session);
            var proofRestored = RestoreSuccess(proofKey, fresh);
            if (proofRestored)
            {
                proofCacheHits++;
                CacheProgress("certified proof: " + entry);
            }
            else
            {
                stage?.Invoke("proof checking");
                Run(["lean", "--root=" + fresh, "-o", Path.Combine(fresh, "Proof.olean"), Path.Combine(fresh, "Proof.lean")],
                    leanPath: leanPath, progress: "Checking Proof: " + entry);
            }
            var built = OleanHashes(fresh, session);
            RequireOnlyAdded(bound, built, "Proof");
            string[] replay = [.. extractionPublication is null ? Array.Empty<string>() : ["Extracted", "ExtractionAudit"],
                .. symbols && !proofRestored ? ["ExtractedSymbols"] : Array.Empty<string>(), .. proofRestored ? Array.Empty<string>() : ["Proof"]];
            if (replay.Length > 0)
            {
                stage?.Invoke("kernel replay");
                Run([checker, .. replay], leanPath: leanPath, progress: (proofRestored ? "Kernel replay of extraction: " : "Kernel replay: ") + entry);
            }
            // The audit reads the bytes leanchecker replayed: nothing may change until it finishes.
            stage?.Invoke("theorem audit");
            var audited = AuditOleans(leanPath, ["Proof", "ExtractionAudit"], [ProofTheorem(theorem), ExtractionCertificate("ExtractionAudit.valid")]);
            if (!Same(built, OleanHashes(fresh, session)))
                throw new InvalidOperationException("Compiled artifacts changed during verification");
            RequireAuditedModule(audited, "Proof", Path.Combine(fresh, "Proof.olean"));
            RequireAuditedModule(audited, "ExtractionAudit", Path.Combine(fresh, "ExtractionAudit.olean"));
            stage?.Invoke("extraction certificate audit");
            AuditedAxioms(audited.theorems[1]);
            stage?.Invoke("theorem audit");
            axioms = AuditedAxioms(audited.theorems[0]);
            audit = AuditText(audited.theorems[0]);
            if (!proofRestored)
            {
                var publication = Path.Combine(fresh, "proof-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path => Path.GetFileName(path).StartsWith("Proof.olean", StringComparison.Ordinal)))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                PublishSuccess(proofKey, publication);
            }
            if (extractionPublication is not null)
            {
                extractionAudit += AuditText(audited.theorems[1]);
                File.WriteAllText(Path.Combine(extractionPublication, "extraction-audit.txt"), extractionAudit);
                PublishSuccess(extractedKey, extractionPublication);
            }
        }
        finally
        {
            Directory.Delete(fresh, true);
        }

        // Bind the report only after confirming inputs stayed unchanged.
        stage?.Invoke("extraction integrity");
        Run(existingArtifacts ? ["dotnet", ExtractorPath, "check", output] : Extract("check", assembly, identity, entry, output, profile));

        if (!Same(before, Inputs(proof, settings)) || identityHash != Sha(Path.Combine(output, "identity.json")))
            throw new InvalidOperationException("Inputs changed during verification");

        var extraction = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
        var initializedTypes = extraction.TryGetProperty("initializedTypes", out var assumptions)
            ? assumptions.Deserialize<string[]>() : [];
        var report = new Report(3, Sha(assembly), identityHash, theorem, axioms, audit, before, libraryKey, libraryBuild, extractionAudit, initializedTypes,
            staticValues: StaticValueAssumptions(extraction));
        File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");

        return report;
    }

    void IDisposable.Dispose()
    {
        if (library is not null && Directory.Exists(library))
            Directory.Delete(library, true);
    }
}
