using System.Diagnostics;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;
using Nethermind.LeanCIL;

// `leancil watch`: keeps every method extraction that `leancil workspace` recorded in a package current with the C#
// and its proofs verified. Each cycle rebuilds the projects, refreshes only the extractions whose generated modules
// changed and runs ordinary `leancil verify` for the proofs those or their own sources affect.
partial class Program
{
    const string WatchUsage = "Usage: leancil watch [package-directory] [--project project.csproj]... " +
        "[--configuration name] [--once] [--format text|json]";

    /// <summary>The cycle's report shape; a change that removes or renames a field increments it.</summary>
    const int WatchSchema = 1;
    const string WatchStateFile = "watch.json";
    static readonly JsonSerializerOptions WatchJson = new(JsonSerializerDefaults.Web);
    static readonly TimeSpan WatchPollInterval = TimeSpan.FromMilliseconds(300);
    // Editors save a burst of files; a cycle starts once the inputs stop changing for this long.
    static readonly TimeSpan WatchSettleInterval = TimeSpan.FromMilliseconds(400);

    sealed record WatchSettings(string Root, string[] Projects, string Configuration, bool Once, bool Json);

    /// <summary>An MSBuild error: its C# location, compiler code and message.</summary>
    sealed record BuildDiagnostic(string File, int Line, int Column, string Code, string Message);

    /// <summary>
    /// What the last verification of a proof checked: the extraction's modules and the proof's sources, by hash,
    /// and its result. Equal inputs make a rerun redundant; a failed build deletes it.
    /// </summary>
    sealed record WatchState(string Extracted, string? Symbols, SortedDictionary<string, string> Sources,
        string Status);

    /// <summary>
    /// One proof's outcome in a cycle: `verified` or `failed` by ordinary verification, `stale` when the build
    /// failed, `missing` when the method no longer extracts, `unverified` when it names no theorem. `Rechecked` is
    /// false when nothing it depends on changed, so the earlier result stands.
    /// </summary>
    sealed record WatchResult(string Status, bool Rechecked, string Method, string Profile, string Module,
        string Proof, string? Theorem, string? Message, JsonNode? Report);

    internal static int Watch(string[] args)
    {
        var settings = ParseWatchSettings(args);
        var editor = Path.Combine(EditorFramework(settings.Root), EditorSourceDirectory);
        if (EditorSelections(editor).Count == 0)
            throw new InvalidDataException("No method extraction is recorded in " + CliPaths.Display(settings.Root) +
                "; run leancil workspace for each proof first.");
        // The modules watch refreshes are what the editor's `lake serve` loads; an oversized environment fails here.
        RequireLeanEnvironmentFits(["lake", "serve"], settings.Root,
            new System.Diagnostics.ProcessStartInfo().Environment);
        var inputs = WatchedInputs(settings, editor);
        var passed = WatchCycle(settings, editor, 1, build: true);
        if (settings.Once) return passed ? 0 : 1;
        inputs = AfterCycle(inputs, settings, editor);
        for (var cycle = 2; ; cycle++)
        {
            var current = WatchedInputs(settings, editor);
            while (Same(current, inputs))
            {
                Thread.Sleep(WatchPollInterval);
                current = WatchedInputs(settings, editor);
            }
            SortedDictionary<string, string> settled;
            do
            {
                settled = current;
                Thread.Sleep(WatchSettleInterval);
                current = WatchedInputs(settings, editor);
            }
            while (!Same(current, settled));
            var changed = current.Keys.Union(inputs.Keys).Where(path =>
                !current.TryGetValue(path, out var stamp) || !inputs.TryGetValue(path, out var previous) ||
                stamp != previous).ToArray();
            var csharp = changed.Any(path => settings.Projects.Any(project =>
                path.StartsWith(Path.GetDirectoryName(project)! + Path.DirectorySeparatorChar,
                    StringComparison.Ordinal)));
            try { WatchCycle(settings, editor, cycle, csharp); }
            catch (Exception error) when (error is not OutOfMemoryException)
            {
                Console.Error.WriteLine("Watch cycle " + cycle + " failed: " + error.Message);
            }
            inputs = AfterCycle(current, settings, editor);
        }
    }

    /// <summary>
    /// The inputs a finished cycle answered: sources as read before it, so an edit made during it starts another
    /// cycle, and assemblies as now, so its own build does not.
    /// </summary>
    static SortedDictionary<string, string> AfterCycle(SortedDictionary<string, string> before,
        WatchSettings settings, string editor)
    {
        var assemblies = EditorSelections(editor).Values.Select(selection => Path.GetFullPath(selection.Assembly))
            .ToHashSet(StringComparer.Ordinal);
        var after = WatchedInputs(settings, editor);
        var inputs = new SortedDictionary<string, string>(before.Where(pair => !assemblies.Contains(pair.Key))
            .ToDictionary(), StringComparer.Ordinal);
        foreach (var (path, stamp) in after.Where(pair => assemblies.Contains(pair.Key))) inputs[path] = stamp;
        return inputs;
    }

    static WatchSettings ParseWatchSettings(string[] args)
    {
        string? root = null;
        string? configuration = null;
        string? format = null;
        var once = false;
        var projects = new List<string>();
        for (var index = 0; index < args.Length; index++)
        {
            var option = args[index];
            if (option == "--once" && !once)
            {
                once = true;
                continue;
            }
            if (!option.StartsWith("--", StringComparison.Ordinal) && root is null)
            {
                root = Path.GetFullPath(option);
                continue;
            }
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException("Missing value for " + option + ".\n" + WatchUsage);
            switch (option)
            {
                case "--project":
                    projects.Add(File.Exists(args[index]) ? Path.GetFullPath(args[index])
                        : throw new FileNotFoundException("Project not found: " + args[index]));
                    break;
                case "--configuration" when configuration is null:
                    configuration = args[index];
                    break;
                case "--format" when format is null:
                    format = args[index] is "text" or "json" ? args[index]
                        : throw new ArgumentException("--format takes text or json.");
                    break;
                default:
                    throw new ArgumentException("Unknown or duplicate option: " + option + "\n" + WatchUsage);
            }
        }
        root ??= Directory.GetCurrentDirectory();
        if (!File.Exists(Path.Combine(root, "lake-manifest.json")))
            throw new InvalidDataException(CliPaths.Display(root) + " is no resolved Lake package; run lake update " +
                "there, or pass the package directory that leancil workspace used.");
        return new(root, [.. projects], configuration ?? "Release", once, format == "json");
    }

    /// <summary>
    /// Length and write time of every input a cycle reads: the projects' C# and MSBuild files, the selected
    /// assemblies and the package's Lean sources and configuration.
    /// </summary>
    static SortedDictionary<string, string> WatchedInputs(WatchSettings settings, string editor)
    {
        var stamps = new SortedDictionary<string, string>(StringComparer.Ordinal);
        void Add(string path)
        {
            var file = new FileInfo(path);
            if (file.Exists) stamps[file.FullName] = file.Length + ":" + file.LastWriteTimeUtc.Ticks;
        }
        foreach (var project in settings.Projects)
            foreach (var path in ProjectSources(Path.GetDirectoryName(project)!)) Add(path);
        foreach (var selection in EditorSelections(editor).Values) Add(selection.Assembly);
        foreach (var path in ConsumerSources(settings.Root)) Add(path);
        return stamps;
    }

    static IEnumerable<string> ProjectSources(string directory)
    {
        foreach (var path in Directory.EnumerateFiles(directory))
            if (Path.GetExtension(path) is ".cs" or ".csproj" or ".props" or ".targets") yield return path;
        foreach (var child in Directory.EnumerateDirectories(directory))
            if (Path.GetFileName(child) is not ("bin" or "obj" or ".git" or ".lake" or ".vs"))
                foreach (var path in ProjectSources(child)) yield return path;
    }

    // `path(line,column): error CODE: message [project]`, as MSBuild prints compiler errors.
    [GeneratedRegex(@"^\s*(?<file>[^\s(][^(]*)\((?<line>\d+),(?<column>\d+)\): error (?<code>[A-Za-z]+\d+): " +
        @"(?<message>.*?)(?: \[[^\]]+\])?\s*$", RegexOptions.Multiline)]
    private static partial Regex BuildError();

    /// <summary>Builds each project; the errors of the builds that failed, none when every build succeeded.</summary>
    static BuildDiagnostic[] BuildProjects(WatchSettings settings)
    {
        var diagnostics = new List<BuildDiagnostic>();
        foreach (var project in settings.Projects)
        {
            var build = Execute(["dotnet", "build", project, "-c", settings.Configuration],
                Path.GetDirectoryName(project));
            if (build.Code == 0) continue;
            var errors = BuildError().Matches(build.Stdout).Select(match => new BuildDiagnostic(
                    Path.GetFullPath(match.Groups["file"].Value.Trim(), Path.GetDirectoryName(project)!),
                    int.Parse(match.Groups["line"].Value), int.Parse(match.Groups["column"].Value),
                    match.Groups["code"].Value, match.Groups["message"].Value)).Distinct().ToArray();
            diagnostics.AddRange(errors.Length > 0 ? errors
                : [new(project, 0, 0, "MSB", "dotnet build failed (" + build.Code + ")")]);
        }
        return [.. diagnostics];
    }

    /// <summary>
    /// The proof's sources in the package: the proof, the package sources its imports reach and the Lake
    /// configuration, by path relative to `root` and hash.
    /// </summary>
    static SortedDictionary<string, string> ProofSources(string root, string proof)
    {
        var sources = ConsumerSources(root).Where(path => Path.GetExtension(path) == ".lean")
            .Select(path => (Path: path, Relative: "/" + Path.GetRelativePath(root, path).Replace('\\', '/')))
            .ToArray();
        var hashes = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var name in new[] { "lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain" })
            if (File.Exists(Path.Combine(root, name))) hashes[name] = Sha(Path.Combine(root, name));
        var pending = new Queue<string>([proof]);
        while (pending.TryDequeue(out var path))
        {
            var relative = Path.GetRelativePath(root, path).Replace('\\', '/');
            if (hashes.ContainsKey(relative) || !File.Exists(path)) continue;
            hashes[relative] = Sha(path);
            // Every source a module name could resolve to counts, so an ambiguous import only widens the set.
            foreach (Match import in SourceImport().Matches(File.ReadAllText(path)))
            {
                var module = "/" + import.Groups[1].Value.Replace('.', '/') + ".lean";
                foreach (var source in sources.Where(source =>
                    source.Relative.EndsWith(module, StringComparison.Ordinal)))
                    pending.Enqueue(source.Path);
            }
        }
        return hashes;
    }

    /// <summary>Where `watch` verifies one proof of a selection: its copy of the extraction and its reports.</summary>
    static string WatchDirectory(string editor, string key, EditorProof proof) =>
        Path.Combine(editor, EditorSelectionsDirectory, key, "proofs",
            ContentKey(proof.Proof + "\n" + proof.Theorem)[..12]);

    // A certificate or state of an extraction that may no longer describe the assembly must not outlive a cycle.
    static void ForgetVerification(string directory)
    {
        File.Delete(Path.Combine(directory, "verified.json"));
        File.Delete(Path.Combine(directory, WatchStateFile));
    }

    /// <summary>
    /// Runs one cycle and prints its report; true when every proof verified or names no theorem. A failed build
    /// makes every proof stale and deletes its certificate, so no result of an earlier build stays green.
    /// </summary>
    static bool WatchCycle(WatchSettings settings, string editor, int cycle, bool build)
    {
        var clock = Stopwatch.StartNew();
        var root = settings.Root;
        var selections = EditorSelections(editor);
        var results = new List<WatchResult>();
        var buildErrors = build ? BuildProjects(settings) : [];
        var refreshed = new List<string>();
        var scratch = new List<string>();
        try
        {
            if (buildErrors.Length > 0)
            {
                foreach (var (key, selection) in selections)
                    foreach (var proof in selection.Proofs)
                    {
                        ForgetVerification(WatchDirectory(editor, key, proof));
                        results.Add(WatchOutcome(key, selection, proof, "stale", true,
                            "the C# build failed; the proof was not checked against the last good build", null));
                    }
                return PrintWatchCycle(settings, cycle, clock.Elapsed, buildErrors, refreshed, results);
            }
            var checks = new List<(string Key, EditorSelection Selection, EditorProof Proof, string Extraction,
                WatchState State)>();
            foreach (var (key, selection) in selections)
            {
                string extraction;
                try
                {
                    extraction = ExtractEditorSelection(selection);
                    scratch.Add(extraction);
                    if (SelectionModules.Key(ExtractionIdentity.Read(extraction).Root) != key)
                        throw new InvalidDataException("The selection now extracts as another method.");
                }
                catch (Exception error) when (error is InvalidDataException or InvalidOperationException
                    or ArgumentException or IOException)
                {
                    // A proof of a method that no longer extracts must fail at its import, not check the old one.
                    RemoveEditorModules(editor, key);
                    var missing = Rejections.Of(error) == Rejection.Selector;
                    foreach (var proof in selection.Proofs)
                    {
                        ForgetVerification(WatchDirectory(editor, key, proof));
                        results.Add(WatchOutcome(key, selection, proof, missing ? "missing" : "failed", true,
                            (missing ? "the method is no longer in the assembly: " : "extraction failed: ") +
                            error.Message, null));
                    }
                    continue;
                }
                var changed = EditorModulesDiffer(editor, key, extraction);
                if (changed) refreshed.AddRange(ApplyEditorExtraction(editor, key, extraction, selection));
                var symbols = Path.Combine(extraction, "Symbols.lean");
                foreach (var proof in selection.Proofs)
                {
                    var state = new WatchState(Sha(Path.Combine(extraction, "Extracted.lean")),
                        File.Exists(symbols) ? ContentKey(EditorSymbols(File.ReadAllText(symbols))) : null,
                        ProofSources(root, Path.GetFullPath(proof.Proof, root)), "");
                    var statePath = Path.Combine(WatchDirectory(editor, key, proof), WatchStateFile);
                    var previous = File.Exists(statePath)
                        ? JsonSerializer.Deserialize<WatchState>(File.ReadAllText(statePath)) : null;
                    if (previous is not null && previous.Extracted == state.Extracted &&
                        previous.Symbols == state.Symbols && Same(previous.Sources, state.Sources))
                        results.Add(WatchOutcome(key, selection, proof, previous.Status, false, null, null));
                    else checks.Add((key, selection, proof, extraction, state));
                }
            }
            BuildEditorModules(root, refreshed);
            foreach (var (key, selection, proof, extraction, state) in checks)
            {
                var result = VerifyWatched(settings, editor, key, selection, proof, extraction);
                File.WriteAllText(Path.Combine(WatchDirectory(editor, key, proof), WatchStateFile),
                    JsonSerializer.Serialize(state with { Status = result.Status }, Json) + "\n");
                results.Add(result);
            }
            return PrintWatchCycle(settings, cycle, clock.Elapsed, [], refreshed, results);
        }
        finally
        {
            foreach (var directory in scratch) Directory.Delete(directory, true);
        }
    }

    static WatchResult WatchOutcome(string key, EditorSelection selection, EditorProof proof, string status,
        bool rechecked, string? message, JsonNode? report) =>
        new(status, rechecked, selection.Method, selection.Profile, "Extracted." + key, proof.Proof, proof.Theorem,
            message, report);

    /// <summary>Verifies one proof with ordinary `leancil verify` against a copy of the cycle's extraction.</summary>
    static WatchResult VerifyWatched(WatchSettings settings, string editor, string key, EditorSelection selection,
        EditorProof proof, string extraction)
    {
        var directory = WatchDirectory(editor, key, proof);
        Directory.CreateDirectory(directory);
        ForgetVerification(directory);
        if (proof.Theorem is null)
            return WatchOutcome(key, selection, proof, "unverified", true,
                "no --theorem was given to leancil workspace; only the editor modules were refreshed", null);
        foreach (var name in new[] { "identity.json", "Extracted.lean", "Symbols.lean" })
            if (File.Exists(Path.Combine(extraction, name)))
                CopyIfChanged(Path.Combine(extraction, name), Path.Combine(directory, name));
            else File.Delete(Path.Combine(directory, name));
        var proofPath = Path.GetFullPath(proof.Proof, settings.Root);
        // A generated scratch package requires the framework by path, which only single-file verification accepts.
        string[] root = IsScratchPackage(settings.Root) ? [] : ["--proof-root", settings.Root];
        var verified = Execute(["dotnet", ExtractorPath, "verify", directory, "--proof", proofPath,
            "--theorem", proof.Theorem, .. root, "--format", "json"], settings.Root);
        JsonNode? report;
        try { report = JsonNode.Parse(verified.Stdout); }
        catch (JsonException) { report = null; }
        var status = verified.Code == 0 && report?["result"]?.GetValue<string>() == "verified" ? "verified" : "failed";
        return WatchOutcome(key, selection, proof, status, true,
            report is null && status == "failed" ? verified.Output.Trim() : null, report);
    }

    /// <summary>Prints the cycle's report and returns whether every proof verified or names no theorem.</summary>
    static bool PrintWatchCycle(WatchSettings settings, int cycle, TimeSpan elapsed, BuildDiagnostic[] build,
        List<string> refreshed, List<WatchResult> results)
    {
        var passed = results.All(result => result.Status is "verified" or "unverified");
        if (settings.Json)
        {
            Console.WriteLine(new JsonObject
            {
                ["schema"] = WatchSchema,
                ["cycle"] = cycle,
                ["seconds"] = Math.Round(elapsed.TotalSeconds, 3),
                ["passed"] = passed,
                ["build"] = JsonSerializer.SerializeToNode(build, WatchJson),
                ["refreshed"] = JsonSerializer.SerializeToNode(refreshed, WatchJson),
                ["results"] = JsonSerializer.SerializeToNode(results, WatchJson),
            }.ToJsonString());
            Console.Out.Flush();
            return passed;
        }
        Console.WriteLine($"Cycle {cycle} ({elapsed.TotalSeconds:F1}s): " + (build.Length > 0 ? "C# build failed"
            : refreshed.Count == 0 ? "no extraction changed" : "refreshed " + string.Join(", ", refreshed)));
        foreach (var error in build)
            Console.WriteLine($"  {CliPaths.Display(error.File)}({error.Line},{error.Column}): error {error.Code}: " +
                error.Message);
        foreach (var result in results)
        {
            Console.WriteLine($"  {result.Status.ToUpperInvariant()}{(result.Rechecked ? "" : " (unchanged)")} " +
                $"{result.Proof}{(result.Theorem is null ? "" : " " + result.Theorem)} [{result.Module}]");
            if (result.Message is not null) Console.WriteLine("    " + result.Message.Split('\n')[0]);
            foreach (var failure in result.Report?["failures"]?.AsArray() ?? [])
            {
                var source = failure?["source"];
                var csharp = failure?["cil"]?["source"];
                var at = source is null ? "" : $"{source["file"]}:{source["line"]}:{source["column"]}: ";
                Console.WriteLine("    " + at +
                    (failure?["message"]?.GetValue<string>() ?? "").Split('\n')[0] +
                    (csharp is null ? "" : $" (C# {csharp["file"]}:{csharp["line"]}:{csharp["column"]})"));
            }
        }
        Console.Out.Flush();
        return passed;
    }
}
