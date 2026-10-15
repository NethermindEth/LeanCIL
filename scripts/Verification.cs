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

    static async Task<string> CaptureOutput(StreamReader reader, TextWriter writer)
    {
        var captured = new StringBuilder();
        var buffer = new char[4096];
        int count;
        while ((count = await reader.ReadAsync(buffer)) != 0)
        {
            captured.Append(buffer, 0, count);
            await writer.WriteAsync(buffer.AsMemory(0, count));
            await writer.FlushAsync();
        }
        return captured.ToString();
    }

    static (int Code, string Output, string Stdout, string Stderr) Execute(IEnumerable<string> command, string? cwd = null, string? leanPath = null,
        bool streamOutput = false, string? progress = null)
    {
#if LEANCIL_TOOL
        // CLI output is a stable interface; progress belongs to the repository runner.
        progress = null;
#endif
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
        var stdout = streamOutput ? CaptureOutput(process.StandardOutput, Console.Out) : process.StandardOutput.ReadToEndAsync();
        var stderr = streamOutput ? CaptureOutput(process.StandardError, Console.Error) : process.StandardError.ReadToEndAsync();
        process.WaitForExit();

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

    string Library(SortedDictionary<string, string> snapshot)
    {
        var common = new SortedDictionary<string, string>(snapshot.Where(p => !p.Key.StartsWith("proof:")).ToDictionary(), StringComparer.Ordinal);

        if (library is not null)
        {
            if (!Same(common, libraryInputs!))
                throw new InvalidOperationException("Proof session source inputs changed");

            return library;
        }

        library = Path.Combine(Path.GetTempPath(), "leancil-library-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(library);

        foreach (var name in common.Keys)
            if (name.EndsWith(".lean") || name is "lakefile.toml" or "lake-manifest.json" or "lean-toolchain")
            {
                var destination = Path.Combine(library, name);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.Copy(At(name), destination);
            }

        Run(["lake", "build", "CIL"], library, progress: "Building fresh Lean verification library");
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
        string theoremAudit, SortedDictionary<string, string> inputs);

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

            if (old.schema != 1 || !Same(old.inputs, Inputs(proof, settings)) || old.identitySha256 != Sha(Path.Combine(output, "identity.json")) ||
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

        // Rebuild handwritten Lean sources without trusting existing compiled artifacts.
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

        var report = new Report(1, Sha(assembly), identityHash, theorem, axioms, audit, before);
        File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");

        return report;
    }

    void IDisposable.Dispose()
    {
        if (library is not null && Directory.Exists(library))
            Directory.Delete(library, true);
    }
}
