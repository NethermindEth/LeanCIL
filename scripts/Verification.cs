using System.Diagnostics;
using System.Runtime.CompilerServices;
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

    bool RestoreSuccess(string key, string destination)
    {
        if (!UseSuccessCache) return false;
        var cached = Path.Combine(SuccessCacheRoot, key);
        try
        {
            var manifest = File.ReadAllBytes(Path.Combine(cached, "receipt.json"));
            var signature = File.ReadAllBytes(Path.Combine(cached, "receipt.hmac"));
            if (!CryptographicOperations.FixedTimeEquals(HMACSHA256.HashData(ReceiptKey, Encoding.UTF8.GetBytes(key).Concat(manifest).ToArray()), signature)) return false;
            var expected = JsonSerializer.Deserialize<SortedDictionary<string, string>>(manifest);
            var files = Path.Combine(cached, "files");
            if (expected is null || !Same(expected, CacheFiles(files))) return false;
            CopyTree(files, destination);
            foreach (var (name, hash) in expected)
                if (Sha(Path.Combine(destination, name)) != hash)
                    throw new InvalidOperationException("Certified cache changed while copying");
            return true;
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException) { return false; }
    }

    void PublishSuccess(string key, string source)
    {
        if (!UseSuccessCache) return;
        Directory.CreateDirectory(SuccessCacheRoot);
        var cached = Path.Combine(SuccessCacheRoot, key);
        var staging = cached + "." + Guid.NewGuid().ToString("N");
        try
        {
            var files = Path.Combine(staging, "files");
            Directory.CreateDirectory(files);
            CopyTree(source, files);
            var manifest = JsonSerializer.SerializeToUtf8Bytes(CacheFiles(files));
            File.WriteAllBytes(Path.Combine(staging, "receipt.json"), manifest);
            File.WriteAllBytes(Path.Combine(staging, "receipt.hmac"), HMACSHA256.HashData(ReceiptKey, Encoding.UTF8.GetBytes(key).Concat(manifest).ToArray()));
            try { Directory.Move(staging, cached); }
            catch (IOException) when (Directory.Exists(cached)) { }
        }
        finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
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

    static (int Code, string Output, string Stdout, string Stderr) Execute(IEnumerable<string> command, string? cwd = null, string? leanPath = null,
        bool streamOutput = false, string? progress = null)
    {
        var traceStage = progress;
#if LEANCIL_TOOL
        // CLI output is a stable interface; progress belongs to the repository runner.
        progress = null;
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
        bool streamOutput = false, string? progress = null)
    {
        var args = command.ToArray();
        var result = Execute(args, cwd, leanPath, streamOutput, progress);

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
                Run(["lake", "build", "CIL"], library, streamOutput: true, progress: "Building fresh Lean verification library");
                var checker = Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
                Run([checker, "CIL"], library, Path.Combine(library, ".lake/build/lib/lean"), streamOutput: true,
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

    static string[] Extract(string mode, string assembly, string? identity, string entry, string output, string profile = "scalar") =>
        ["dotnet", ExtractorPath, mode, assembly, entry, output, profile,
            .. identity is null ? Array.Empty<string>() : ["--assembly", identity]];

    // This module imports only the extracted program, never the user proof. The
    // certificate must prove the complete validator application for that program;
    // a declaration with the right name but type True is insufficient.
    const string ExtractionAuditSource = """
        import Extracted
        run_cmd do
          match (← Lean.getEnv).find? `Extracted.translation_valid with
          | some (.thmInfo _) => pure ()
          | _ => throwError "Expected extraction certificate theorem"
        theorem ExtractionAudit.valid :
            CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
              Extracted.methodEvidence Extracted.program := Extracted.translation_valid
        #print axioms ExtractionAudit.valid
        """;

    static string[] AuditedAxioms(string audit, string theorem)
    {
        var matches = Regex.Matches(audit, "'" + Regex.Escape(theorem) + @"' depends on axioms:\s*\[([^\]]*)\]");
        if (matches.Count > 1)
            throw new InvalidOperationException("Ambiguous theorem axiom audit");
        if (matches.Count == 0 && !audit.Contains($"'{theorem}' does not depend on any axioms"))
            throw new InvalidOperationException("Missing transitive theorem axiom audit");
        var axioms = matches.Count == 0 ? [] : matches[0].Groups[1].Value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
        if (axioms.Any(a => a is not ("propext" or "Quot.sound" or "Classical.choice")))
            throw new InvalidOperationException("Unapproved proof axioms: " + string.Join(", ", axioms));
        return axioms;
    }

    sealed record Report(int schema, string assemblySha256, string identitySha256, string theorem, string[] axioms,
        string theoremAudit, SortedDictionary<string, string> inputs, string? libraryKey = null, string? libraryBuild = null,
        string? extractionAudit = null, string[]? initializedTypes = null,
        string? batchSourceSha256 = null, string? batchTheorem = null);

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
            .Select(m => m.Groups[1].Value).Where(n => n != "Extracted" && n.Split('.')[0] is not ("Init" or "Lean" or "Std")).ToArray();

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
                            Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"), .. changed],
                                leanPath: Path.Combine(session, ".lake/build/lib/lean"), progress: "Kernel replay of proof dependencies: " + entry);
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
            File.WriteAllText(Path.Combine(fresh, "Audit.lean"), $"import Proof\nrun_cmd do\n  match (← Lean.getEnv).find? `{theorem} with\n  | some (.thmInfo _) => pure ()\n  | _ => throwError \"Expected a theorem\"\n#check {theorem}\n#print axioms {theorem}\n");
            File.WriteAllText(Path.Combine(fresh, "ExtractionAudit.lean"), ExtractionAuditSource);
            var leanPath = fresh + Path.PathSeparator + Path.Combine(session, ".lake/build/lib/lean");

            var checker = Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
            var currentModules = ModuleArtifacts(session);
            var alteredExisting = certifiedModules!.Any(pair => !currentModules.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
            var changedModules = (alteredExisting ? currentModules.Keys : currentModules.Keys.Where(name => !certifiedModules!.ContainsKey(name)))
                .Select(ModuleName).Distinct().ToArray();
            if (changedModules.Length > 0)
            {
                Run([checker, .. changedModules], leanPath: leanPath, progress: "Kernel replay of proof dependencies: " + entry);
                certifiedModules = currentModules;
            }
            // Full artifact identities include transitive support dependencies and every
            // olean part. Cached success is never inferred from an unsigned manifest.
            var environmentKey = ContentKey("certified-modules-v1\n" + VerificationPolicy + "\n" + libraryKey + "\n" + JsonSerializer.Serialize(currentModules));
            var extractedKey = ContentKey("extraction-audit-v1\n" + environmentKey + "\n" +
                Sha(Path.Combine(fresh, "Extracted.lean")) + "\n" + ExtractionAuditSource);
            string? extractionPublication = null;
            if (RestoreSuccess(extractedKey, fresh))
            {
                extractionAudit = File.ReadAllText(Path.Combine(fresh, "extraction-audit.txt"));
                AuditedAxioms(extractionAudit, "ExtractionAudit.valid");
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
                    if (name == "ExtractionAudit")
                    {
                        extractionAudit = checkedOutput;
                        AuditedAxioms(extractionAudit, "ExtractionAudit.valid");
                    }
                }
                var publication = Path.Combine(fresh, "extraction-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path =>
                    Path.GetFileName(path).StartsWith("Extracted.olean", StringComparison.Ordinal) ||
                    Path.GetFileName(path).StartsWith("ExtractionAudit.olean", StringComparison.Ordinal)))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                File.WriteAllText(Path.Combine(publication, "extraction-audit.txt"), extractionAudit);
                extractionPublication = publication;
            }
            var proofKey = ContentKey("theorem-audit-v1\n" + extractedKey + "\n" + Sha(Path.Combine(fresh, "Proof.lean")) + "\n" + theorem);
            if (RestoreSuccess(proofKey, fresh))
            {
                if (extractionPublication is not null)
                {
                    stage?.Invoke("kernel replay");
                    Run([checker, "Extracted", "ExtractionAudit"], leanPath: leanPath, progress: "Kernel replay of extraction: " + entry);
                }
                audit = File.ReadAllText(Path.Combine(fresh, "theorem-audit.txt"));
                axioms = AuditedAxioms(audit, theorem);
                proofCacheHits++;
                CacheProgress("certified proof: " + entry);
            }
            else
            {
                stage?.Invoke("proof checking");
                Run(["lean", "--root=" + fresh, "-o", Path.Combine(fresh, "Proof.olean"), Path.Combine(fresh, "Proof.lean")],
                    leanPath: leanPath, progress: "Checking Proof: " + entry);
                stage?.Invoke("kernel replay");
                Run([checker, .. extractionPublication is null ? Array.Empty<string>() : ["Extracted", "ExtractionAudit"], "Proof"],
                    leanPath: leanPath, progress: "Kernel replay: " + entry);
                stage?.Invoke("theorem audit");
                audit = Run(["lean", "--root=" + fresh, Path.Combine(fresh, "Audit.lean")], leanPath: leanPath);
                axioms = AuditedAxioms(audit, theorem);
                var publication = Path.Combine(fresh, "proof-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path => Path.GetFileName(path).StartsWith("Proof.olean", StringComparison.Ordinal)))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                File.WriteAllText(Path.Combine(publication, "theorem-audit.txt"), audit);
                PublishSuccess(proofKey, publication);
            }
            if (extractionPublication is not null) PublishSuccess(extractedKey, extractionPublication);
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
        var report = new Report(3, Sha(assembly), identityHash, theorem, axioms, audit, before, libraryKey, libraryBuild, extractionAudit, initializedTypes);
        File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");

        return report;
    }

    void IDisposable.Dispose()
    {
        if (library is not null && Directory.Exists(library))
            Directory.Delete(library, true);
    }
}
