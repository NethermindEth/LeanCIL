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
    SortedDictionary<string, string>? libraryInputs;

    static string At(string path) => Path.Combine(Root, path);

    static string Sha(string path) => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));

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

    static async Task<string> CaptureOutput(StreamReader reader, TextWriter writer, ProgressSummary? summary = null)
    {
        var captured = new StringBuilder();
        var line = new StringBuilder();
        var buffer = new char[4096];
        int count;
        while ((count = await reader.ReadAsync(buffer)) != 0)
        {
            captured.Append(buffer, 0, count);
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
        var stdout = streamOutput ? CaptureOutput(process.StandardOutput, Console.Out, summary) : process.StandardOutput.ReadToEndAsync();
        var stderr = streamOutput ? CaptureOutput(process.StandardError, Console.Error, summary) : process.StandardError.ReadToEndAsync();
        if (summary is null) process.WaitForExit();
        else
            while (!process.WaitForExit(10_000)) summary.Report();

        var output = stdout.GetAwaiter().GetResult();
        var error = stderr.GetAwaiter().GetResult();
        if (progress is not null)
            Console.WriteLine($"END {progress} (exit {process.ExitCode}, {elapsed.Elapsed.TotalSeconds:F1}s)");
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
    SortedDictionary<string, string>? certifiedCil;

    static SortedDictionary<string, string> LibrarySources(SortedDictionary<string, string> snapshot) =>
        new(snapshot.Where(p => p.Key.StartsWith("CIL/", StringComparison.Ordinal) ||
            p.Key is "CIL.lean" or "lakefile.toml" or "lake-manifest.json" or "lean-toolchain").ToDictionary(), StringComparer.Ordinal);

    static SortedDictionary<string, string> CacheFiles(string directory) =>
        new(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path) != "cache-manifest.json")
            .ToDictionary(path => Path.GetRelativePath(directory, path).Replace('\\', '/'), Sha), StringComparer.Ordinal);

    // Track every olean part, including server/private declaration data.
    static SortedDictionary<string, string> CilArtifacts(string session)
    {
        var compiled = Path.Combine(session, ".lake/build/lib/lean");
        return new(Directory.EnumerateFiles(compiled, "*", SearchOption.AllDirectories)
            .Select(path => (Path: path, Relative: Path.GetRelativePath(compiled, path).Replace('\\', '/')))
            .Where(file => (file.Relative.StartsWith("CIL/", StringComparison.Ordinal) ||
                file.Relative.StartsWith("CIL.olean", StringComparison.Ordinal)) &&
                Path.GetFileName(file.Relative).Contains(".olean", StringComparison.Ordinal))
            .ToDictionary(file => file.Relative, file => Sha(file.Path)), StringComparer.Ordinal);
    }

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
        var toolchain = Run(["lean", "--print-prefix"]).Trim();
        var compiler = Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean");
        libraryKey = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(
            "leancil-library-v2-kernel-replayed\n" + System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier + "\n" +
            toolchain + "\n" + Sha(compiler) + "\n" + JsonSerializer.Serialize(sources))));
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
            if (!fresh && ValidCache(cached) && Same(sources, LibrarySources(CacheFiles(cached))))
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
                Run(["lake", "build", "CIL"], library, progress: "Building fresh Lean verification library");
                var checker = Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
                Run([checker, "CIL"], library, Path.Combine(library, ".lake/build/lib/lean"),
                    progress: "Kernel replay of fresh Lean verification library");
                libraryBuild = "fresh";
                if (!fresh)
                {
                    File.WriteAllText(Path.Combine(library, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(library), Json));
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
        certifiedCil = CilArtifacts(library);
        libraryInputs = common;
        return library;
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

    sealed record Report(int schema, string assemblySha256, string identitySha256, string theorem, string[] axioms,
        string theoremAudit, SortedDictionary<string, string> inputs, string? libraryKey = null, string? libraryBuild = null, string[]? initializedTypes = null);

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

            if (old.schema != 2 || !Same(old.inputs, Inputs(proof, settings)) || old.identitySha256 != Sha(Path.Combine(output, "identity.json")) ||
                old.theorem != theorem || old.assemblySha256 != Sha(assembly))
                throw new InvalidOperationException("Stale verification report or changed proof inputs");

            return old;
        }

        // A failed attempt must not leave an earlier successful report behind.
        File.Delete(reportPath);
        stage?.Invoke("extraction integrity");
        if (existingArtifacts)
            Run(["dotnet", ExtractorPath, "check", output]);
        else
            Run(["dotnet", "build", "Extractor", "-c", "Release", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);

        // Use a source-bound build; CI and --fresh bypass the local library cache.
        stage?.Invoke("Lean library build");
        var before = Inputs(proof, settings);
        var session = Library(before);
        var support = Regex.Matches(File.ReadAllText(proof), @"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", RegexOptions.Multiline)
            .Select(m => m.Groups[1].Value).Where(n => n != "Extracted" && n.Split('.')[0] is not ("Init" or "Lean" or "Std")).ToArray();

        if (support.Length > 0)
            Run(["lake", "build", .. support], session, progress: "Building proof dependencies: " + entry);

        if (!existingArtifacts)
            Run(Extract("extract", assembly, identity, entry, output, profile));
        var identityHash = Sha(Path.Combine(output, "identity.json"));

        // Isolate generated code and the selected proof, then audit the named theorem.
        var fresh = Path.Combine(output, "proof-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(fresh);
        string audit;
        string[] axioms;

        try
        {
            File.Copy(Path.Combine(output, "Extracted.lean"), Path.Combine(fresh, "Extracted.lean"));
            File.Copy(proof, Path.Combine(fresh, "Proof.lean"));
            File.WriteAllText(Path.Combine(fresh, "Audit.lean"), $"import Proof\nrun_cmd do\n  match (← Lean.getEnv).find? `{theorem} with\n  | some (.thmInfo _) => pure ()\n  | _ => throwError \"Expected a theorem\"\n#check {theorem}\n#print axioms {theorem}\n");
            var leanPath = fresh + Path.PathSeparator + Path.Combine(session, ".lake/build/lib/lean");

            stage?.Invoke("proof checking");
            foreach (var name in new[] { "Extracted", "Proof" })
                Run(["lean", "--root=" + fresh, "-o", Path.Combine(fresh, name + ".olean"), Path.Combine(fresh, name + ".lean")],
                    leanPath: leanPath, progress: $"Checking {name}: {entry}");

            // The base audit covers modules built by CIL.lean, not the entire CIL
            // namespace. Replay newly built or changed CIL modules too, alongside every source
            // support root as well as the generated module and proof: checking only
            // Proof would trust unchecked declarations smuggled through an import.
            // Installed Lean toolchain modules remain part of the trusted toolchain.
            stage?.Invoke("kernel replay");
            var toolchain = Run(["lean", "--print-prefix"]).Trim();
            var checker = Path.Combine(toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
            var libraryPath = Path.Combine(session, ".lake/build/lib/lean");
            var replay = Directory.EnumerateFiles(libraryPath, "*.olean", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(libraryPath, path).Split(Path.DirectorySeparatorChar)[0])
                .Select(name => Path.GetFileNameWithoutExtension(name)).Where(n => n != "CIL").Distinct();
            var currentCil = CilArtifacts(session);
            var changedCil = certifiedCil!.Keys.Union(currentCil.Keys)
                .Where(name => !certifiedCil.TryGetValue(name, out var certified) ||
                    !currentCil.TryGetValue(name, out var current) || certified != current)
                .Select(name => name.Split(".olean", 2)[0].Replace('/', '.')).Distinct();
            Run([checker, .. replay, .. changedCil, "Extracted", "Proof"], leanPath: leanPath,
                progress: "Kernel replay: " + entry);

            stage?.Invoke("theorem audit");
            audit = Run(["lean", "--root=" + fresh, Path.Combine(fresh, "Audit.lean")], leanPath: leanPath);
            var matches = Regex.Matches(audit, "'" + Regex.Escape(theorem) + @"' depends on axioms:\s*\[([^\]]*)\]");

            if (matches.Count > 1)
                throw new InvalidOperationException("Ambiguous theorem axiom audit");

            if (matches.Count == 0 && !audit.Contains($"'{theorem}' does not depend on any axioms"))
                throw new InvalidOperationException("Missing transitive theorem axiom audit");

            axioms = matches.Count == 0 ? [] : matches[0].Groups[1].Value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);

            if (axioms.Any(a => a is not ("propext" or "Quot.sound" or "Classical.choice")))
                throw new InvalidOperationException("Unapproved proof axioms: " + string.Join(", ", axioms));
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
        var report = new Report(2, Sha(assembly), identityHash, theorem, axioms, audit, before, libraryKey, libraryBuild, initializedTypes);
        File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");

        return report;
    }

    void IDisposable.Dispose()
    {
        if (library is not null && Directory.Exists(library))
            Directory.Delete(library, true);
    }
}
