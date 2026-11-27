using System.Collections.Concurrent;
using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
    const string PreparedLeanFixturesPath = "LEANCIL_PREPARED_LEAN_FIXTURES";
    const string PreparedLeanFixturesDigest = "LEANCIL_PREPARED_LEAN_FIXTURES_SHA256";

    sealed record PreparedLeanModule(string Source, string Compiled, string SourceHash, string CompiledHash);
    sealed record PreparedLeanManifest(SortedDictionary<string, string> LibrarySources,
        Dictionary<string, PreparedLeanModule> Modules);

    // The parent freshly compiles test modules against its authenticated library. Children
    // reuse those exact source/output pairs, never a previous run's test artifacts.
    void PrepareLeanFixtures(params string[] modules)
    {
        var inputs = CommonInputs();
        var session = Library(inputs);
        var compiled = Path.Combine(session, ".lake/build/lib/lean");
        var records = new ConcurrentDictionary<string, PreparedLeanModule>(StringComparer.Ordinal);
        foreach (var module in modules)
            if (!FixtureModule.IsMatch(module))
                throw new ArgumentException("Expected a test fixture module: " + module);
        // A fixture's imports of other test modules are compiled and recorded with it, so no list has to name them.
        var importsRemaining = new Dictionary<string, int>(StringComparer.Ordinal);
        var importers = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        var sourceLengths = new Dictionary<string, int>(StringComparer.Ordinal);
        var unread = new Stack<string>(modules);
        while (unread.TryPop(out var module))
        {
            if (importsRemaining.ContainsKey(module)) continue;
            var text = File.ReadAllText(At(module.Replace('.', '/') + ".lean"));
            var imports = TestImport.Matches(text).Select(match => match.Groups[1].Value).Distinct().ToArray();
            sourceLengths.Add(module, text.Length);
            importsRemaining.Add(module, imports.Length);
            foreach (var dependency in imports)
            {
                if (!importers.TryGetValue(dependency, out var children))
                    importers.Add(dependency, children = []);
                children.Add(module);
                unread.Push(dependency);
            }
        }
        var ready = new PriorityQueue<string, (int Leaf, int NegativeLength)>();
        void Enqueue(string module) =>
            ready.Enqueue(module, (importers.ContainsKey(module) ? 0 : 1, -sourceLengths[module]));
        foreach (var (module, count) in importsRemaining)
            if (count == 0) Enqueue(module);
        // Compile prerequisites first, then larger leaves, with at most two Lean processes.
        var running = new Dictionary<Task, string>();
        try
        {
            while (ready.Count != 0 || running.Count != 0)
            {
                while (running.Count < 2 && ready.Count != 0)
                {
                    var module = ready.Dequeue();
                    running.Add(Task.Run(() => Compile(module)), module);
                }
                var finished = Task.WhenAny(running.Keys).GetAwaiter().GetResult();
                var compiledModule = running[finished];
                running.Remove(finished);
                finished.GetAwaiter().GetResult();
                if (importers.TryGetValue(compiledModule, out var children))
                    foreach (var child in children)
                        if (--importsRemaining[child] == 0) Enqueue(child);
            }
        }
        finally
        {
            // A sibling may still be writing into this session when another compilation fails.
            Task.WhenAll(running.Keys).GetAwaiter().GetResult();
        }
        if (records.Count != importsRemaining.Count)
            throw new InvalidOperationException("Test fixture imports contain a cycle");
        var sources = LibrarySources(inputs);
        if (!Same(sources, CommonInputs(libraryOnly: true)))
            throw new InvalidOperationException("Library sources changed while checking fixtures");
        var manifest = Path.Combine(session, "prepared-test-fixtures.json");
        File.WriteAllText(manifest,
            JsonSerializer.Serialize(new PreparedLeanManifest(sources, records.ToDictionary())));
        Environment.SetEnvironmentVariable(PreparedLeanFixturesPath, manifest);
        Environment.SetEnvironmentVariable(PreparedLeanFixturesDigest, Sha(manifest));

        void Compile(string module)
        {
            var relative = module.Replace('.', '/');
            var source = At(relative + ".lean");
            var output = Path.Combine(compiled, relative + ".olean");
            var before = Sha(source);
            Directory.CreateDirectory(Path.GetDirectoryName(output)!);
            File.Delete(output);
            var log = Run(["lean", "--root=" + Root, "-o", output, source], leanPath: SessionLeanPath(session),
                progress: "Checking " + module);
            if (log.Contains("sorryAx", StringComparison.Ordinal) || Sha(source) != before)
                throw new InvalidOperationException("Untrusted or changed fixture: " + module);
            records[module] = new(source, output, before, Sha(output));
        }
    }

    static bool PreparedLeanFixturesMatch(IReadOnlyList<string> modules)
    {
        var path = Environment.GetEnvironmentVariable(PreparedLeanFixturesPath);
        if (string.IsNullOrEmpty(path)) return false;
        if (Sha(path) != Environment.GetEnvironmentVariable(PreparedLeanFixturesDigest))
            throw new InvalidOperationException("Prepared Lean fixture manifest changed");
        var manifest = JsonSerializer.Deserialize<PreparedLeanManifest>(File.ReadAllText(path))!;
        // Compare snapshot keys, not raw files: the lakefile's key covers only its library view.
        var current = CommonInputs(libraryOnly: true);
        if (manifest.LibrarySources.Count != current.Count)
            throw new InvalidOperationException("Prepared Lean library sources changed");
        foreach (var (source, hash) in manifest.LibrarySources)
            if (current.GetValueOrDefault(source) != hash)
                throw new InvalidOperationException("Prepared Lean library source changed: " + source);
        foreach (var module in modules)
        {
            if (module.StartsWith("CIL.", StringComparison.Ordinal))
            {
                if (!manifest.LibrarySources.ContainsKey(module.Replace('.', '/') + ".lean"))
                    throw new InvalidOperationException("Prepared Lean library module is missing: " + module);
                continue;
            }
            if (!manifest.Modules.TryGetValue(module, out var record) ||
                Sha(record.Source) != record.SourceHash || Sha(record.Compiled) != record.CompiledHash)
                throw new InvalidOperationException("Prepared Lean fixture is missing or changed: " + module);
        }
        return true;
    }

    static void RequireLeanFixtures(params string[] modules)
    {
        if (!PreparedLeanFixturesMatch(modules))
            Run(["lake", "build", .. modules], FixturePackage());
    }

    static void CheckLeanFixture(string module)
    {
        if (!PreparedLeanFixturesMatch([module]))
            Run(["lake", "env", "lean", At(module.Replace('.', '/') + ".lean")], FixturePackage());
    }

    [GeneratedRegex(@"(?m)^import[ \t]+(Tests\.[A-Za-z0-9_.]+)")]
    private static partial Regex TestImport { get; }

    [GeneratedRegex(@"\ATests\.[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\z")]
    private static partial Regex FixtureModule { get; }
}
