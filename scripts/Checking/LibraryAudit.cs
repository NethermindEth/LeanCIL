using System.Text.Json;

// Audits every theorem under namespace prefixes in a Lake package's replayed oleans, without elaborating its source.
partial class Program
{
    internal const string LibraryAuditUsage =
        "Usage: leancil audit-library --project package-directory --module M [--module M]... --prefix P [--prefix P]... [--axioms a,b,c] [--results results.json]";

    sealed record LibraryAudit(string[] Modules, string[] Replayed, AuditedNamespaces Result);

    internal static int AuditLibrary(string[] args)
    {
        string? project = null;
        string? results = null;
        List<string> modules = [], prefixes = [];
        List<string>? axioms = null;
        for (var index = 0; index < args.Length; index++)
        {
            var option = args[index];
            if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException($"Missing value for {option}.\n{LibraryAuditUsage}");
            var value = args[index];
            switch (option)
            {
                case "--project" when project is null: project = Path.GetFullPath(value); break;
                case "--results" when results is null: results = Path.GetFullPath(value); break;
                case "--module": modules.Add(value); break;
                case "--prefix": prefixes.Add(value); break;
                case "--axioms":
                    (axioms ??= []).AddRange(value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries));
                    break;
                default: throw new ArgumentException($"Unknown or duplicate option: {option}\n{LibraryAuditUsage}");
            }
        }
        if (project is null || modules.Count == 0 || prefixes.Count == 0)
            throw new ArgumentException(LibraryAuditUsage);
        using Program verification = new();
        var audit = verification.AuditLibrary(project, [.. modules], [.. prefixes], axioms is null ? ApprovedAxioms : [.. axioms]);
        var result = audit.Result;
        if (results is not null)
            File.WriteAllText(results, JsonSerializer.Serialize(new { modules = audit.Modules, result.count, result.prefixes,
                result.axioms, result.rejected, result.error }, AuditJson) + "\n");
        if (result.error is not null)
            throw new InvalidOperationException("Library audit failed: " + result.error +
                string.Concat(result.rejected.Select(rejected => $"\n  {rejected.name}: {rejected.error}")));
        Console.WriteLine($"Audited {result.count} theorems in {audit.Modules.Length} modules " +
            $"({audit.Replayed.Length} replayed, {audit.Modules.Length - audit.Replayed.Length} certified CIL) under " +
            string.Join(", ", result.prefixes.Select(pair => $"{pair.Key} ({pair.Value})")));
        Console.WriteLine("  Axioms: " + (result.axioms.Length == 0 ? "none" : string.Join(", ", result.axioms)));
        return 0;
    }

    // Build, replay every non-toolchain module in the closure, then audit those exact bytes with the certified checker.
    LibraryAudit AuditLibrary(string project, string[] modules, string[] prefixes, string[] axioms)
    {
        if (modules.FirstOrDefault(module => !ContractModules.Name(module)) is { } invalid)
            throw new ArgumentException("Invalid module name: " + invalid);
        if (axioms.Length == 0) throw new ArgumentException("--axioms requires at least one axiom name.");
        // Binds the audit executable before the package build runs any of its code.
        var session = Library(Inputs(At("CIL.lean")));
        var expected = File.ReadAllText(Path.Combine(session, "lean-toolchain")).Trim();
        var toolchainFile = Path.Combine(project, "lean-toolchain");
        if (!File.Exists(toolchainFile) || File.ReadAllText(toolchainFile).Trim() != expected)
            throw new InvalidDataException($"The package must pin the verification toolchain {expected} in lean-toolchain.");
        Run(["lake", "build", .. modules.Select(module => "+" + module + ":olean")], project, progress: "Building library modules");
        var (directories, leanPath) = ConsumerImportDirectories(project);
        var artifacts = LibraryArtifacts(directories);
        if (modules.FirstOrDefault(module => !artifacts.ContainsKey(module)) is { } missing)
            throw new InvalidDataException("Library module is missing from the resolved import paths: " + missing);
        // Hash the artifacts before reading their import headers, so a swap after the hash fails the closing check.
        var parts = Parts(artifacts);
        var graph = ConsumerModuleImports(Path.GetTempPath(), artifacts);
        var closure = ImportClosure(graph, modules).Where(artifacts.ContainsKey).Order(StringComparer.Ordinal).ToArray();
        var reusable = ReusableCertified(graph, parts, certifiedModules!);
        var replayed = closure.Where(module => !reusable.Contains(module)).ToArray();
        var failures = ReplayConsumerModules(project, replayed, leanPath);
        if (failures.Count > 0)
            throw new InvalidOperationException("Kernel replay rejected " + string.Join(", ", failures.Keys.Order(StringComparer.Ordinal)) + ":\n" +
                string.Join("\n", failures.Values));
        var audited = AuditOleans(leanPath, closure, [], namespaces: new(prefixes, axioms));
        foreach (var module in closure) RequireAuditedModule(audited, module, artifacts[module]);
        if (JsonSerializer.Serialize(Parts(LibraryArtifacts(directories))) != JsonSerializer.Serialize(parts))
            throw new InvalidOperationException("Compiled artifacts changed during the library audit");
        return new(closure, replayed, audited.namespaces!);

        static SortedDictionary<string, SortedDictionary<string, string>> Parts(Dictionary<string, string> found) =>
            new(found.ToDictionary(pair => pair.Key, pair => ConsumerModuleParts(pair.Value)), StringComparer.Ordinal);
    }

    // A certified proof holds only against the definitions it was checked with, so a CIL module skips replay
    // only when it and every module it transitively imports are byte-identical to the certified library.
    static HashSet<string> ReusableCertified(Dictionary<string, string[]> graph,
        SortedDictionary<string, SortedDictionary<string, string>> parts, IReadOnlyDictionary<string, string> certified)
    {
        // Compares exactly the parts ConsumerModuleParts reads; Lake's .olean.hash trace file is not module content.
        bool Identical(string module) => (module == "CIL" || module.StartsWith("CIL.", StringComparison.Ordinal)) &&
            new[] { ".olean", ".olean.server", ".olean.private" }.All(suffix =>
                certified.TryGetValue(module.Replace('.', '/') + suffix, out var hash) == parts[module].TryGetValue(suffix, out var part) && hash == part);
        var identical = parts.Keys.Where(Identical).ToHashSet(StringComparer.Ordinal);
        return identical.Where(module => ImportClosure(graph, [module]).All(import => !parts.ContainsKey(import) || identical.Contains(import)))
            .ToHashSet(StringComparer.Ordinal);
    }

    // Module name to olean path; a module found twice or shadowing the toolchain is rejected.
    Dictionary<string, string> LibraryArtifacts(string[] directories)
    {
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var directory in directories.Where(Directory.Exists))
            foreach (var path in Directory.EnumerateFiles(directory, "*.olean", SearchOption.AllDirectories))
            {
                var module = ModuleName(Path.GetRelativePath(directory, path).Replace('\\', '/'));
                if (File.Exists(Path.Combine(Toolchain, "lib/lean", module.Replace('.', '/') + ".olean")))
                    throw new InvalidDataException("Library module shadows the trusted Lean toolchain: " + module);
                if (!result.TryAdd(module, path)) throw new InvalidDataException("Ambiguous library module: " + module);
            }
        return result;
    }
}
