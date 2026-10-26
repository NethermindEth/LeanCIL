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
        CopyTree(Path.Combine(session, ".lake/build"), At(".lake/build"));
        var records = new ConcurrentDictionary<string, PreparedLeanModule>(StringComparer.Ordinal);
        foreach (var module in modules)
            if (!Regex.IsMatch(module, @"\ATests\.[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\z"))
                throw new ArgumentException("Expected a test fixture module: " + module);
        var dependencies = modules.ToDictionary(module => module, module => Regex.Matches(
                File.ReadAllText(At(module.Replace('.', '/') + ".lean")), @"(?m)^import[ \t]+(Tests\.[A-Za-z0-9_.]+)")
            .Select(match => match.Groups[1].Value).ToArray(), StringComparer.Ordinal);
        var pending = modules.ToHashSet(StringComparer.Ordinal);
        while (pending.Count != 0)
        {
            var ready = pending.Where(module => dependencies[module].All(dependency => !pending.Contains(dependency)))
                .ToArray();
            if (ready.Length == 0) throw new InvalidOperationException("Test fixture imports contain a cycle");
            Parallel.ForEach(ready, new ParallelOptions { MaxDegreeOfParallelism = 2 }, Compile);
            pending.ExceptWith(ready);
        }
        var sources = LibrarySources(inputs);
        if (!Same(sources, LibrarySources(CommonInputs())))
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
            var log = Run(["lean", "--root=" + Root, "-o", output, source], leanPath: compiled,
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
        foreach (var (source, hash) in manifest.LibrarySources)
            if (Sha(At(source)) != hash)
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
        if (!PreparedLeanFixturesMatch(modules)) Run(["lake", "build", .. modules]);
    }

    static void CheckLeanFixture(string module)
    {
        if (!PreparedLeanFixturesMatch([module]))
            Run(["lake", "env", "lean", At(module.Replace('.', '/') + ".lean")]);
    }
}
