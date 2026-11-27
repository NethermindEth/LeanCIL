using System.Text.Json;
using System.Text.RegularExpressions;

// Consumer workspace snapshots, dependency cloning and extraction component splitting.
partial class Program
{
    /// <summary>A Lake dependency of a consumer package: a git checkout pinned by a full revision.</summary>
    sealed record ConsumerDependency(string Name, string Directory, string Source, string Revision, string Url);
    ConsumerDependency[]? fullBundleDependencies { get; init; }

    /// <summary>
    /// `relative`, read against `root`, spelled under `root` as given. Containment is decided after links are
    /// followed on both sides, so Lake's resolved spelling of a package directory matches the root as given.
    /// </summary>
    static string Within(string root, string relative)
    {
        var spelledRoot = Path.TrimEndingDirectorySeparator(Path.GetFullPath(root));
        // Not made full first: Path.GetFullPath would drop a `..` before the link it follows is read.
        var inside = ResolvedRelativePath(spelledRoot, Path.Combine(spelledRoot, relative))
            ?? throw new InvalidDataException("Consumer path escapes its package: " + relative);
        return inside == "." ? spelledRoot : Path.Join(spelledRoot, inside);
    }

    /// <summary>A directory name whose contents are never consumer sources, such as build outputs.</summary>
    static bool ExcludedConsumerDirectory(string name) =>
        name is ".git" or ".lake" or "artifacts" or "generated" or "bin" or "obj" or ".work";

    static IEnumerable<string> ConsumerSources(string root, string? excludedDirectory = null)
    {
        if (excludedDirectory is not null &&
            LocationComparer.Equals(Path.GetFullPath(root), Path.GetFullPath(excludedDirectory))) yield break;
        foreach (var path in Directory.EnumerateFileSystemEntries(root).Order(StringComparer.Ordinal))
        {
            var attributes = File.GetAttributes(path);
            if ((attributes & FileAttributes.ReparsePoint) != 0)
                throw new InvalidDataException("Consumer sources must not contain symbolic links: " + path);
            if ((attributes & FileAttributes.Directory) != 0)
            {
                if (ExcludedConsumerDirectory(Path.GetFileName(path))) continue;
                foreach (var source in ConsumerSources(path, excludedDirectory)) yield return source;
            }
            else if (Path.GetExtension(path) is ".lean" or ".toml" or ".json" || Path.GetFileName(path) == "lean-toolchain")
                yield return path;
        }
    }

    /// <summary>The package's dependencies from lake-manifest.json: git packages pinned by a full revision.</summary>
    static ConsumerDependency[] ConsumerDependencies(string root)
    {
        var manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(root, "lake-manifest.json")));
        if (manifest.GetProperty("packagesDir").GetString() != ".lake/packages" ||
            manifest.GetProperty("lakeDir").GetString() != ".lake")
            throw new InvalidDataException("Consumer verification requires the standard .lake and .lake/packages directories.");
        return manifest.GetProperty("packages").EnumerateArray().Select(package =>
        {
            var name = package.GetProperty("name").GetString()!;
            var revision = package.TryGetProperty("rev", out var rev) ? rev.GetString() ?? "" : "";
            if (package.GetProperty("type").GetString() != "git" ||
                !Regex.IsMatch(name, @"\A[A-Za-z_][A-Za-z0-9_-]*\z") || !Regex.IsMatch(revision, @"\A[0-9a-fA-F]{40}\z"))
                throw new InvalidDataException("Consumer dependencies must be git packages pinned by a full revision in lake-manifest.json.");
            var directory = Within(root, ".lake/packages/" + name);
            var source = Within(directory, package.TryGetProperty("subDir", out var sub) ? sub.GetString() ?? "." : ".");
            var actual = Run(["git", "rev-parse", "HEAD"], directory).Trim();
            if (actual != revision)
                throw new InvalidDataException("Consumer dependency revision differs from lake-manifest.json: " + name);
            return new ConsumerDependency(name, directory, source, revision, package.GetProperty("url").GetString()!);
        }).ToArray();
    }

    /// <summary>Resolved locations where a batch output would overlap a consumer source.</summary>
    static HashSet<string> ConsumerSourceLocations(SortedDictionary<string, string> snapshot)
    {
        var locations = new HashSet<string>(CollidingLocationComparer);
        var parents = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var key in snapshot.Keys)
        {
            if (!key.StartsWith("consumer:", StringComparison.Ordinal)) continue;
            var source = key["consumer:".Length..];
            var parent = Path.GetDirectoryName(source)!;
            if (!parents.TryGetValue(parent, out var resolved))
                parents.Add(parent, resolved = ResolvedPath(parent));
            string? location = Path.Join(resolved, Path.GetFileName(source));
            // A source may have become a link since the snapshot read it.
            if (new FileInfo(location).LinkTarget is not null) location = ResolvedPath(source);
            while (location is not null && locations.Add(location))
                location = Path.GetDirectoryName(location);
        }
        foreach (var (parent, resolved) in parents)
            if (!string.Equals(ResolvedPath(parent), resolved, StringComparison.Ordinal))
                throw new InvalidDataException("Consumer source directory changed during verification: " + parent);
        return locations;
    }

    static SortedDictionary<string, string> ConsumerSnapshot(string root, string? output,
        ConsumerDependency[]? bundled = null, SortedDictionary<string, string>? frameworkInputs = null)
    {
        var inputs = new SortedDictionary<string, string>(StringComparer.Ordinal);
        ConsumerDependency[] dependencies = bundled ?? ConsumerDependencies(root);
        foreach (var directory in new[] { root }.Concat(dependencies.Select(d => d.Directory)))
            foreach (var path in ConsumerSources(directory, output)) inputs["consumer:" + path] = Sha(path);
        foreach (var dependency in dependencies) inputs["revision:" + dependency.Name] = dependency.Revision;
        if (inputs.Keys.Any(k => k.StartsWith("consumer:", StringComparison.Ordinal) && Path.GetFileName(k) == "Extracted.lean"))
            throw new InvalidDataException("Extracted.lean is reserved for the selected extraction artifact; remove stale generated sources from the consumer package.");
        var framework = dependencies.SingleOrDefault(d => d.Name == "leancil")
            ?? throw new InvalidDataException("Consumer package must depend on leancil. Run lake update first.");
        RequireBundledFramework(framework.Source, root, inputs, frameworkInputs);
        return inputs;
    }

    /// <summary>Rejects a framework at `source` or a toolchain pin at `root` that differs from the tool's.</summary>
    static void RequireBundledFramework(string source, string root,
        SortedDictionary<string, string>? consumerInputs = null, SortedDictionary<string, string>? frameworkInputs = null)
    {
        foreach (var path in Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories)
            .Append(At("CIL.lean")).Append(At("lean-toolchain")))
        {
            var relative = Path.GetRelativePath(Root, path);
            var consumer = Path.Combine(source, relative);
            var bundledHash = frameworkInputs?.GetValueOrDefault(relative.Replace('\\', '/'));
            var consumerHash = bundledHash is null ? null : consumerInputs?.GetValueOrDefault("consumer:" + consumer);
            if (!File.Exists(consumer) || !SameFrameworkSource(consumer, consumerHash, path, bundledHash))
                throw new InvalidDataException("Consumer leancil sources differ from the verifier's bundled framework: " +
                    consumer + (SourceRevision is { } revision
                        ? $"\n  Pin leancil to rev \"{revision}\" (see leancil --version)." : ""));
        }
        if (File.ReadAllText(Path.Combine(root, "lean-toolchain")).Trim() != File.ReadAllText(At("lean-toolchain")).Trim())
            throw new InvalidDataException("Consumer and verifier Lean toolchains differ.");
    }

    // Git checkouts may encode identical Lean text with different line endings.
    static bool SameFrameworkSource(string consumer, string? consumerHash, string bundled, string? bundledHash) =>
        consumerHash is not null && consumerHash == bundledHash ||
        SnapshotText(consumer, consumerHash).ReplaceLineEndings("\n") ==
            SnapshotText(bundled, bundledHash).ReplaceLineEndings("\n");

    static SortedDictionary<string, string> RequestInputs(SortedDictionary<string, string> common, string proof, string? settings)
    {
        var inputs = new SortedDictionary<string, string>(common, StringComparer.Ordinal);
        inputs["proof:" + proof] = Sha(proof);
        if (settings is not null) inputs["settings:" + settings] = Sha(settings);
        return inputs;
    }

    /// <summary>Read a source as text, checking the same bytes against its snapshot when supplied.</summary>
    static string SnapshotText(string path, string? expected)
    {
        if (expected is null) return File.ReadAllText(path);
        var bytes = File.ReadAllBytes(path);
        if (Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes)) != expected)
            throw new InvalidOperationException("Inputs changed during consumer verification");
        using StreamReader reader = new(new MemoryStream(bytes));
        return reader.ReadToEnd();
    }

    /// <summary>Consumer import paths and source imports for one input snapshot.</summary>
    sealed class ConsumerImports(SortedDictionary<string, string> snapshot, string root)
    {
        // Multiple package or library roots can provide the same module. Keep snapshot order for diagnostics.
        readonly ILookup<string, string> sources = snapshot.Keys
            .Where(key => key.StartsWith("consumer:", StringComparison.Ordinal) &&
                key.EndsWith(".lean", StringComparison.Ordinal))
            .SelectMany(key => ModulePaths(root, key["consumer:".Length..]))
            .ToLookup(entry => entry.Module, entry => entry.Path, StringComparer.Ordinal);
        readonly Dictionary<string, string[]> imports = new(StringComparer.Ordinal);

        static IEnumerable<(string Module, string Path)> ModulePaths(string root, string path)
        {
            var relative = Path.GetRelativePath(root, path).Replace('\\', '/');
            for (var start = 0; start < relative.Length;)
            {
                yield return (relative[start..], path);
                var separator = relative.IndexOf('/', start);
                if (separator < 0) yield break;
                start = separator + 1;
            }
        }

        string[] ReadImports(string path)
        {
            if (imports.TryGetValue(path, out var names)) return names;
            var source = SnapshotText(path, snapshot["consumer:" + path]);
            names = SourceImport.Matches(source).Select(match => match.Groups[1].Value).ToArray();
            imports.Add(path, names);
            return names;
        }

        // Lean's compiled import headers confirm the source-level selection after the build.
        internal IEnumerable<(string Module, string Source)> Generated(string proof)
        {
            var pending = new Queue<string>([proof]);
            var seen = new HashSet<string>(StringComparer.Ordinal) { proof };
            while (pending.TryDequeue(out var path))
                foreach (var name in ReadImports(path))
                {
                    if (name == "ExtractedSymbols" || SelectionModules.Is(name)) yield return (name, path);
                    foreach (var source in sources[name.Replace('.', '/') + ".lean"])
                        if (seen.Add(source)) pending.Enqueue(source);
                }
        }
    }

    /// <summary>Package name of the session package that holds the generated certificate modules.</summary>
    const string GeneratedPackageName = "leancil_generated";

    /// <summary>
    /// Resolves the session's leancil dependency to the certified library directory, which Lake then
    /// reads in place, and adds a generated-module package that the session root requires. Returns
    /// that package: it has its own layout, so the consumer's srcDir and buildDir cannot move it.
    /// </summary>
    static string UseCertifiedFramework(string session, string certified)
    {
        var generated = Within(session, ".lake/packages/" + GeneratedPackageName);
        Directory.CreateDirectory(generated);
        File.WriteAllText(Path.Combine(generated, "lakefile.toml"),
            $"name = \"{GeneratedPackageName}\"\n\n[[require]]\nname = \"leancil\"\npath = " +
            JsonSerializer.Serialize(Path.GetFullPath(certified).Replace('\\', '/')) + "\n");
        File.Copy(Path.Combine(certified, "lean-toolchain"), Path.Combine(generated, "lean-toolchain"));
        var relative = Path.GetRelativePath(session, generated).Replace('\\', '/');
        var toml = Path.Combine(session, "lakefile.toml");
        if (File.Exists(toml))
            File.AppendAllText(toml, $"\n[[require]]\nname = \"{GeneratedPackageName}\"\npath = \"{relative}\"\n");
        else
            File.AppendAllText(Path.Combine(session, "lakefile.lean"), $"\nrequire {GeneratedPackageName} from \"{relative}\"\n");

        var path = Path.Combine(session, "lake-manifest.json");
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(path))!.AsObject();
        var packages = manifest["packages"]!.AsArray();
        var index = packages.Select((package, position) => (package, position))
            .Single(entry => entry.package!["name"]!.GetValue<string>() == "leancil").position;
        System.Text.Json.Nodes.JsonObject PathPackage(string name, string directory, bool inherited) => new()
        {
            ["type"] = "path", ["scope"] = "", ["name"] = name, ["manifestFile"] = "lake-manifest.json",
            ["inherited"] = inherited, ["dir"] = directory, ["configFile"] = "lakefile.toml"
        };
        packages[index] = PathPackage("leancil", Path.GetFullPath(certified),
            packages[index]!["inherited"]?.GetValue<bool>() ?? false);
        packages.Add(PathPackage(GeneratedPackageName, relative, false));
        File.WriteAllText(path, manifest.ToJsonString());
        return generated;
    }

    internal static void AddConsumerLibrary(string directory, string name, string[]? leanArguments = null)
    {
        var toml = Path.Combine(directory, "lakefile.toml");
        bool useToml = File.Exists(toml);
        Func<string, string> quote = useToml ? value => JsonSerializer.Serialize(value) : LeanString;
        var quoted = string.Join(", ", (leanArguments ?? []).Select(quote));
        if (useToml)
            File.AppendAllText(toml, $"\n[[lean_lib]]\nname = \"{name}\"\n" +
                (quoted.Length == 0 ? "" : $"moreLeanArgs = [{quoted}]\n"));
        else
            File.AppendAllText(Path.Combine(directory, "lakefile.lean"), $"\nlean_lib {name}\n" +
                (quoted.Length == 0 ? "" : $"  where moreLeanArgs := #[{quoted}]\n"));
    }

    /// <summary>The compiled module directory of a certified library.</summary>
    static string CertifiedModuleDirectory(string certified) =>
        Path.TrimEndingDirectorySeparator(Path.GetFullPath(Path.Combine(certified, ".lake/build/lib/lean")));

    /// <summary>
    /// The import directories in `leanPath`, read against `session`, without the trusted toolchain's: the certified
    /// base spelled as `certified` and every other directory spelled under `session`. A directory that lies
    /// outside the session once links are followed is refused, so no import is read from a directory the session
    /// does not hold.
    /// </summary>
    static string[] ValidatedConsumerImportDirectories(
        string session, string trusted, string? certified, string leanPath) =>
        [.. leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(path => Path.Combine(session, path))
            // Lake reports directories with links followed, so each is compared after following links too.
            .Where(path => !SameLocation(trusted, path))
            .Select(path => certified is not null && SameLocation(certified, path) ? certified : Within(session, path))
            .Distinct(LocationComparer)];

    (string[] Directories, string LeanPath) ConsumerImportDirectories(string session)
    {
        // Ask the same Lake environment used by the checker. Package buildDir and
        // leanLibDir need not be the default .lake/build/lib/lean directories.
        var lines = Run(["lake", "env"], session).Split('\n', StringSplitOptions.TrimEntries)
            .Where(line => line.StartsWith("LEAN_PATH=", StringComparison.Ordinal)).ToArray();
        if (lines.Length != 1) throw new InvalidDataException("Could not resolve consumer Lean import paths.");
        var leanPath = lines[0]["LEAN_PATH=".Length..];
        var trusted = Path.GetFullPath(Path.Combine(Toolchain, "lib/lean"));
        var certified = library is null ? null : CertifiedModuleDirectory(library);
        return (ValidatedConsumerImportDirectories(session, trusted, certified, leanPath), leanPath);
    }

    // Variables read by Lean, Lake and elan, plus any a consumer's elaborators read
    // (LEANCIL_CACHE_ENVIRONMENT). Lake's traces already bind sources, options and tools.
    static SortedDictionary<string, string> ConsumerCacheEnvironment()
    {
        static string Normalize(string name) => OperatingSystem.IsWindows() ? name.ToUpperInvariant() : name;
        var named = (Environment.GetEnvironmentVariable("LEANCIL_CACHE_ENVIRONMENT") ?? "")
            .Split([',', ';', ' '], StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Select(Normalize).Append("LEANCIL_CACHE_ENVIRONMENT").ToHashSet(StringComparer.Ordinal);
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (System.Collections.DictionaryEntry entry in Environment.GetEnvironmentVariables())
        {
            var name = Normalize((string)entry.Key);
            // The thread count bounds parallelism only; elaboration results do not depend on it.
            if (named.Contains(name) || (name != "LEAN_NUM_THREADS" &&
                new[] { "LEAN_", "LAKE_", "ELAN_", "RESERVOIR_" }.Any(prefix => name.StartsWith(prefix, StringComparison.Ordinal))))
                result[name] = (string?)entry.Value ?? "";
        }
        return result;
    }

    // Changes whenever the verifier, framework, Lean/Lake binaries, the variables they
    // read, or the bound inputs change. Never log the environment values.
    string ConsumerCacheKey(string kind, SortedDictionary<string, string> inputs, string extra) =>
        ContentKey("consumer-" + kind + "-v2\n" + VerificationPolicy + "\n" + libraryKey + "\n" +
            Sha(LeanExecutable) + "\n" +
            Sha(Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker")) + "\n" +
            Sha(Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "lake.exe" : "lake")) + "\n" +
            JsonSerializer.Serialize(ConsumerCacheEnvironment()) + "\n" +
            JsonSerializer.Serialize(inputs) + "\n" + extra);

    // Lake traces depend on compiled imports even when framework sources are unchanged.
    string ConsumerSupportCacheKey(SortedDictionary<string, string> snapshot,
        IEnumerable<string> importDirectories, IEnumerable<string> configuration) =>
        ConsumerCacheKey("support", new(snapshot.Where(pair =>
                pair.Key.StartsWith("revision:", StringComparison.Ordinal))
                .ToDictionary(), StringComparer.Ordinal),
            string.Join("\n", importDirectories) + "\n" + string.Join("\n", configuration) + "\n" +
            JsonSerializer.Serialize(baseModules));

    static HashSet<string> ImportClosure(Dictionary<string, string[]> graph, IEnumerable<string> roots)
    {
        var closure = new HashSet<string>(roots, StringComparer.Ordinal);
        var pending = new Queue<string>(closure);
        while (pending.TryDequeue(out var name))
            if (graph.TryGetValue(name, out var imports))
                foreach (var import in imports)
                    if (closure.Add(import)) pending.Enqueue(import);
        return closure;
    }

    static HashSet<string> DependentModules(IReadOnlyDictionary<string, string[]> graph, IEnumerable<string> roots)
    {
        var importers = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        foreach (var (name, imports) in graph)
            foreach (var import in imports)
            {
                if (!importers.TryGetValue(import, out var users)) importers.Add(import, users = []);
                users.Add(name);
            }
        var dependent = new HashSet<string>(roots, StringComparer.Ordinal);
        var pending = new Queue<string>(dependent);
        while (pending.TryDequeue(out var name))
            if (importers.TryGetValue(name, out var users))
                foreach (var user in users)
                    if (dependent.Add(user)) pending.Enqueue(user);
        return dependent;
    }

    const string ConsumerSupportRecordName = "leancil-support.json";

    // Sources are package-relative paths of every candidate source file for the module.
    sealed record ConsumerSupportModule(SortedDictionary<string, string> Sources, string[] Imports, string[] Files);

    // Generated certificates depend on their own package and certified framework, not the
    // consumer's package configuration. Keep their authenticated record free of consumer modules.
    void PublishConsumerCertificateSupport(string family, string collected, HashSet<string> modules)
    {
        var record = ReadConsumerSupportRecord(Path.Combine(collected, ConsumerSupportRecordName));
        if (record is null) return;
        var selected = new SortedDictionary<string, ConsumerSupportModule>(record
            .Where(pair => modules.Contains(pair.Key)).ToDictionary(), StringComparer.Ordinal);
        if (selected.Count != modules.Count || selected.Values.Any(module => module.Imports.Any(import =>
                !modules.Contains(import) && !ExternalConsumerModule(import)))) return;
        var publication = Path.Combine(Path.GetTempPath(),
            "leancil-certificate-support-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(publication);
        try
        {
            foreach (var file in selected.Values.SelectMany(module => module.Files).Distinct(StringComparer.Ordinal))
            {
                var target = Within(publication, file);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Within(collected, file), target);
            }
            var manifest = Path.Combine(publication, ConsumerSupportRecordName);
            File.WriteAllText(manifest, JsonSerializer.Serialize(selected));
            PublishSuccess(family + "-" + Sha(manifest), publication, family);
        }
        finally { Directory.Delete(publication, true); }
    }

    bool ExternalConsumerModule(string name) => IsCertifiedLibraryModule(name) ||
        File.Exists(Path.Combine(Toolchain, "lib/lean", name.Replace('.', '/') + ".olean"));

    // Binds extraction-dependent support to the generated program text, not to the assembly bytes.
    // Restored dependents only skip rebuilding: they are always replayed against the fresh Extracted.
    const string ExtractedSourceKey = "<generated>/Extracted.lean";

    static IReadOnlyDictionary<string, string> WithExtraction(IReadOnlyDictionary<string, string> sources, string extracted) =>
        sources.Append(new(ExtractedSourceKey, extracted)).ToDictionary(StringComparer.Ordinal);

    // Keep only modules whose candidate sources are unchanged and whose imports are
    // kept, certified framework modules or toolchain modules.
    HashSet<string> RestorableConsumerSupport(SortedDictionary<string, ConsumerSupportModule> record, IReadOnlyDictionary<string, string> sources)
    {
        var result = record.Where(pair => pair.Value.Sources.Count > 0 &&
                pair.Value.Sources.All(source => sources.TryGetValue(source.Key, out var hash) && hash == source.Value))
            .Select(pair => pair.Key).ToHashSet(StringComparer.Ordinal);
        var graph = record.ToDictionary(pair => pair.Key,
            pair => pair.Value.Imports.Where(import => !ExternalConsumerModule(import) &&
                !(import == "Extracted" && pair.Value.Sources.ContainsKey(ExtractedSourceKey))).ToArray(),
            StringComparer.Ordinal);
        var invalid = record.Keys.Where(name => !result.Contains(name))
            .Concat(graph.Values.SelectMany(imports => imports).Where(import => !record.ContainsKey(import)));
        result.ExceptWith(DependentModules(graph, invalid));
        return result;
    }

    static SortedDictionary<string, ConsumerSupportModule>? ReadConsumerSupportRecord(string path)
    {
        try
        {
            var record = JsonSerializer.Deserialize<SortedDictionary<string, ConsumerSupportModule>>(File.ReadAllText(path));
            return record is null || record.Values.Any(module => module?.Sources is null || module.Imports is null || module.Files is null)
                ? null : new(record, StringComparer.Ordinal);
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException) { return null; }
    }

    static SortedDictionary<string, string> ConsumerSourceHashes(SortedDictionary<string, string> snapshot, string root) =>
        new(snapshot.Where(pair => pair.Key.StartsWith("consumer:", StringComparison.Ordinal) && pair.Key.EndsWith(".lean", StringComparison.Ordinal))
            .ToDictionary(pair => Path.GetRelativePath(root, pair.Key["consumer:".Length..]).Replace('\\', '/'), pair => pair.Value), StringComparer.Ordinal);

    // Restores the largest unchanged, import-closed module set of one authenticated
    // generation. Lake still decides reuse; a rebuilt restored module forces full replay.
    // dependent selects extraction-dependent modules (true), the others (false) or both (null).
    SortedDictionary<string, string> RestoreConsumerSupport(string key, IReadOnlyDictionary<string, string> sources, string destination,
        bool? dependent = null, IReadOnlyCollection<string>? requiredModules = null)
    {
        bool Selected(SortedDictionary<string, ConsumerSupportModule> record, string module) =>
            dependent is not bool wanted || record[module].Sources.ContainsKey(ExtractedSourceKey) == wanted;
        if (!UseSuccessCache || !Directory.Exists(SuccessCacheRoot)) return new(StringComparer.Ordinal);
        var candidates = new List<(string Name, int Count, DateTime Time)>();
        foreach (var generation in Directory.EnumerateDirectories(SuccessCacheRoot, key + "-*"))
        {
            var name = Path.GetFileName(generation);
            // Staging and replaced entries carry a '.' suffix and are never restored.
            if (name.Contains('.')) continue;
            // Unauthenticated preselection only; the chosen generation is authenticated below.
            var record = ReadConsumerSupportRecord(Path.Combine(generation, "files", ConsumerSupportRecordName));
            var restorable = record is null ? [] : RestorableConsumerSupport(record, sources);
            var count = record is null || requiredModules?.Any(module => !restorable.Contains(module)) == true
                ? 0 : restorable.Count(module => Selected(record, module));
            if (count > 0) candidates.Add((name, count, Directory.GetLastWriteTimeUtc(generation)));
        }
        foreach (var (name, _, _) in candidates.OrderByDescending(item => item.Count).ThenByDescending(item => item.Time))
        {
            var staging = Path.Combine(Path.GetTempPath(), "leancil-consumer-restored-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(staging);
            try
            {
                // RestoreSuccess verifies the local producer signature and all artifact hashes.
                if (!RestoreSuccess(name, staging)) continue;
                var record = ReadConsumerSupportRecord(Path.Combine(staging, ConsumerSupportRecordName));
                if (record is null) continue;
                var restorable = RestorableConsumerSupport(record, sources);
                if (requiredModules?.Any(module => !restorable.Contains(module)) == true) continue;
                var files = restorable.Where(module => Selected(record, module))
                    .SelectMany(module => record[module].Files)
                    .Select(file => (Source: Within(staging, file), Target: Within(destination, file))).ToArray();
                if (files.Any(file => !File.Exists(file.Source))) continue;
                foreach (var (source, target) in files)
                {
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(source, target, true);
                }
                TouchEntry(Path.Combine(SuccessCacheRoot, name));
                return CacheFiles(destination);
            }
            catch (Exception error) when (error is InvalidDataException or IOException or UnauthorizedAccessException) { }
            finally { Directory.Delete(staging, true); }
        }
        return new(StringComparer.Ordinal);
    }

    // Collects certified modules and their source/import closures. Generated certificates bind
    // their exact source too; restoring them saves compilation but never their replay or audit.
    // Returns null when no module can be bound to its sources.
    string? CollectConsumerSupport(string session, Dictionary<string, string> modules, Dictionary<string, string[]> graph,
        HashSet<string> excluded, HashSet<string> extractionDependent, IReadOnlyDictionary<string, string> sources)
    {
        var generatedArtifacts = Directory.EnumerateFiles(session, "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(session, path).Replace('\\', '/'))
            .Where(relative => !relative.Split('/').Contains(".git") &&
                new[] { ".c", ".c.hash", ".ir", ".ir.hash", ".setup.json" }.Any(suffix => relative.EndsWith(suffix, StringComparison.Ordinal)))
            .ToArray();
        var record = new SortedDictionary<string, ConsumerSupportModule>(StringComparer.Ordinal);
        foreach (var (name, path) in modules.Where(pair => !excluded.Contains(pair.Key) &&
            !IsCertifiedLibraryModule(pair.Key)))
        {
            var files = new SortedSet<string>(StringComparer.Ordinal);
            var stem = Path.GetFileNameWithoutExtension(path);
            foreach (var artifact in Directory.EnumerateFiles(Path.GetDirectoryName(path)!, stem + ".*"))
            {
                // A sibling module Foo.Bar must not be mistaken for Foo's artifact.
                var suffix = Path.GetFileName(artifact)[stem.Length..];
                if (suffix is ".olean" or ".olean.hash" or ".olean.private" or ".olean.private.hash" or
                    ".olean.server" or ".olean.server.hash" or ".ilean" or ".ilean.hash" or ".trace" or ".ir" or ".ir.hash" or
                    ".ir.sig" or ".ir.sig.hash")
                    files.Add(Path.GetRelativePath(session, artifact).Replace('\\', '/'));
            }
            // Lake's olean trace also records generated C/IR outputs. Without
            // those outputs it recompiles an otherwise valid cached module.
            // Search by full module suffix to respect custom build/IR dirs.
            var modulePath = name.Replace('.', '/');
            foreach (var artifact in generatedArtifacts)
                if (new[] { ".c", ".c.hash", ".ir", ".ir.hash", ".setup.json" }
                    .Any(suffix => artifact.EndsWith("/" + modulePath + suffix, StringComparison.Ordinal)))
                    files.Add(artifact);
            var candidates = sources.Where(pair =>
                (pair.Key != ExtractedSourceKey || name == "Extracted") &&
                (pair.Key[..^".lean".Length] == modulePath ||
                    pair.Key[..^".lean".Length].EndsWith("/" + modulePath, StringComparison.Ordinal))).ToDictionary();
            if (extractionDependent.Contains(name) && candidates.Count > 0) candidates[ExtractedSourceKey] = sources[ExtractedSourceKey];
            record[name] = new(new(candidates, StringComparer.Ordinal),
                graph[name].Order(StringComparer.Ordinal).ToArray(), files.ToArray());
        }
        // A module without known sources cannot be matched later, nor can its importers.
        var bound = RestorableConsumerSupport(record, record.Values.SelectMany(module => module.Sources)
            .DistinctBy(pair => pair.Key).ToDictionary(StringComparer.Ordinal));
        foreach (var name in record.Keys.Where(name => !bound.Contains(name)).ToArray()) record.Remove(name);
        if (record.Count == 0) return null;
        var publication = Path.Combine(Path.GetTempPath(), "leancil-consumer-support-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(publication);
        foreach (var file in record.Values.SelectMany(module => module.Files))
        {
            var target = Within(publication, file);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Within(session, file), target, true);
        }
        File.WriteAllText(Path.Combine(publication, ConsumerSupportRecordName), JsonSerializer.Serialize(record));
        return publication;
    }

    /// <summary>
    /// A prepared consumer workspace. <paramref name="Generated"/> is the package holding the generated
    /// modules: the session root for verification, whose leancil resolves to the certified library in
    /// place, or the framework source copy for an editor workspace.
    /// </summary>
    /// <summary>
    /// A prepared consumer workspace: its generated package, the hash of each file placed in it, and the
    /// developer's files among them, so diagnostics cite those originals.
    /// </summary>
    sealed record ConsumerSession(string Generated, Dictionary<string, string> Copied, SourceCopies Sources);

    sealed record ExtractionComponents(string InputHash, string Aggregate, Dictionary<string, string> Sources);

    [GeneratedRegex(@"(?m)^set_option maxRecDepth [0-9]+\r?$")]
    private static partial Regex ExtractionRecursionDepth { get; }

    /// <summary>The first whole-program declaration of an extraction: its local or specialized method table.</summary>
    [GeneratedRegex(@"(?m)^def (?:localMethods|specializedMethods) :")]
    private static partial Regex AggregateStart();

    // Components keep the extraction's own recursion depth, which follows its longest method;
    // a fixed depth would reject bodies the complete extraction compiles.
    static string ExtractionComponentContext(string source) =>
        "namespace Extracted\nopen CIL\n" + ExtractionRecursionDepth.Match(source).Value.TrimEnd('\r') + "\n\n";

    // Split only the extractor's declaration boundaries. Lean still checks every imported
    // declaration and the aggregate certificate against the complete program.
    static ExtractionComponents SplitExtractionComponents(string source)
    {
        var methods = Regex.Matches(source, @"(?m)^def method[0-9]+Signature : String := ");
        // A bound package's whole-program data starts at its local methods, which precede its specialized methods.
        var aggregate = AggregateStart().Match(source) is { Success: true } start ? start.Index : -1;
        var context = ExtractionComponentContext(source);
        if (methods.Count < 2 || aggregate <= methods[^1].Index)
            return new(ContentKey(source), source, new(StringComparer.Ordinal));
        var localValidation = new Regex(@"(?m)^theorem method([0-9]+)_" +
            @"(?:coverage|shape|declared|division|opaque|object_operands)_validated[^\r\n]*\r?\n");
        var tail = source[aggregate..];
        var validations = localValidation.Matches(tail).GroupBy(match => int.Parse(match.Groups[1].Value))
            .ToDictionary(group => group.Key, group => string.Concat(group.Select(match => match.Value)));
        tail = localValidation.Replace(tail, "");
        var sources = new Dictionary<string, string>(StringComparer.Ordinal);
        string Component(string text)
        {
            var name = "LeanCILComponent_" + ContentKey(text);
            sources.Add(name, text);
            return name;
        }
        var header = Component(source[..methods[0].Index] + "\nend Extracted\n");
        var declarations = new Dictionary<string, int>(StringComparer.Ordinal);
        var modules = new List<string> { header };
        for (var index = 0; index < methods.Count; index++)
        {
            var end = index + 1 < methods.Count ? methods[index + 1].Index : aggregate;
            var body = source[methods[index].Index..end] + validations.GetValueOrDefault(index, "");
            // Extra dependencies from literal text are conservative. Missing dependencies
            // cannot authorize a certificate: compilation and kernel replay remain mandatory.
            var tokens = Regex.Matches(body, @"[A-Za-z_][A-Za-z0-9_]*")
                .Select(match => match.Value).ToHashSet(StringComparer.Ordinal);
            var imports = tokens.Select(token => declarations.GetValueOrDefault(token, -1))
                .Where(declaration => declaration >= 0).Distinct().Order()
                .Select(declaration => modules[declaration]).Prepend(header);
            var name = Component(string.Join("\n", imports.Select(module => "import " + module)) +
                "\n\n" + context + body + "\nend Extracted\n");
            modules.Add(name);
            // Decoded and evaluated definitions are declared by their commands, so components naming them import them.
            foreach (Match declaration in Regex.Matches(body,
                @"(?m)^(?:@\[[^\r\n]*\]\s+)?(?:def|theorem|cil_decoded_method|cil_evaluated) ([A-Za-z_][A-Za-z0-9_]*)"))
                declarations.Add(declaration.Groups[1].Value, modules.Count - 1);
        }
        return new(ContentKey(source), string.Join("\n", modules.Select(module => "import " + module)) +
            "\n\n" + context + tail, sources);
    }

    // A unique wrapper stays in Extracted so its compilation shares the aggregate process.
    static ExtractionComponents SharedExtractionComponents(ExtractionComponents plan, HashSet<string> repeated)
    {
        if (plan.Sources.Keys.Count(repeated.Contains) < 2)
            return new(plan.InputHash, "", new(StringComparer.Ordinal));
        var context = ExtractionComponentContext(plan.Aggregate);
        var shared = plan.Sources.Where(pair => repeated.Contains(pair.Key)).ToDictionary(StringComparer.Ordinal);
        var bodies = plan.Sources.Where(pair => !repeated.Contains(pair.Key)).Select(pair =>
            pair.Value[(pair.Value.IndexOf(context, StringComparison.Ordinal) +
                context.Length)..^"\nend Extracted\n".Length]);
        var tail = plan.Aggregate[(plan.Aggregate.IndexOf(context, StringComparison.Ordinal) +
            context.Length)..];
        return new(plan.InputHash, string.Join("\n", shared.Keys.Select(module => "import " + module)) + "\n\n" +
            context + string.Concat(bodies) + tail, shared);
    }

    static void RejectContractSourceShadow(string module, IEnumerable<string> sourceDirectories)
    {
        var relative = module.Replace('.', Path.DirectorySeparatorChar) + ".lean";
        // File lookup respects the actual filesystem's case rules, including per-directory settings.
        if (sourceDirectories.Any(directory => File.Exists(Path.Combine(directory, relative))))
            throw new InvalidDataException("Contract interface module shadows a consumer source: " + module);
    }

    // Source imports schedule work only; compiled import headers decide what can be shared.
    [GeneratedRegex(@"(?<!\S)(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_'.]*)")]
    private static partial Regex ConsumerImportCommand { get; }

    static IEnumerable<string> ConsumerSourceImports(string source)
    {
        var text = source.ToCharArray();
        var blockDepth = 0;
        var lineComment = false;
        for (var index = 0; index < text.Length; index++)
        {
            if (text[index] == '\n') { lineComment = false; continue; }
            var current = source[index];
            var next = index + 1 < text.Length ? source[index + 1] : '\0';
            if (!lineComment && current == '/' && next == '-')
            {
                blockDepth++;
                text[index] = text[index + 1] = ' ';
                index++;
            }
            else if (!lineComment && blockDepth > 0 && current == '-' && next == '/')
            {
                blockDepth--;
                text[index] = text[index + 1] = ' ';
                index++;
            }
            else
            {
                if (blockDepth == 0 && current == '-' && next == '-') lineComment = true;
                if (blockDepth > 0 || lineComment) text[index] = ' ';
            }
        }
        return ConsumerImportCommand.Matches(new string(text)).Select(import => import.Groups[1].Value);
    }

    static string[] ConsumerSupportCandidates(IEnumerable<string> proofs, string[] sourceDirectories,
        IEnumerable<string> generatedModules, string toolchainModules)
    {
        var excluded = generatedModules.Concat(["Extracted", "ExtractedSymbols", "ExtractionAudit"])
            .ToHashSet(StringComparer.Ordinal);
        // Lake lists source directories with links followed, as macOS reaches /var through /private/var, while
        // package roots are spelled as given: one location counts once, or every module there looks ambiguous.
        sourceDirectories = [.. sourceDirectories.DistinctBy(ResolvedPath, LocationComparer)];
        var imports = new Dictionary<string, string[]>(StringComparer.Ordinal);
        var pending = new Queue<string>();
        foreach (var proof in proofs)
            foreach (var import in ConsumerSourceImports(File.ReadAllText(proof)))
                pending.Enqueue(import);
        while (pending.TryDequeue(out var module))
        {
            if (excluded.Contains(module) || SelectionModules.Is(module) || imports.ContainsKey(module) ||
                IsCertifiedLibraryModule(module)) continue;
            var relative = module.Replace('.', Path.DirectorySeparatorChar) + ".lean";
            if (File.Exists(Path.Combine(toolchainModules, Path.ChangeExtension(relative, ".olean")))) continue;
            var sources = sourceDirectories.Select(directory => Path.Combine(directory, relative))
                .Where(File.Exists).Distinct().ToArray();
            // Ambiguous and unresolved sources are left to each group's ordinary Lake build.
            if (sources.Length != 1) { excluded.Add(module); continue; }
            imports[module] = ConsumerSourceImports(File.ReadAllText(sources[0])).Distinct().ToArray();
            foreach (var imported in imports[module]) pending.Enqueue(imported);
        }
        var dependent = DependentModules(imports, excluded);
        return imports.Keys.Where(module => !dependent.Contains(module)).Order(StringComparer.Ordinal).ToArray();
    }

    // Git marks objects read-only on Windows. The session owns each copy and removes it after replay.
    static void CloneConsumerDependency(string source, string destination)
    {
        try { Run(["git", "clone", "--no-hardlinks", "--no-checkout", source, destination]); }
        finally
        {
            string objects = Path.Combine(destination, ".git", "objects");
            if (OperatingSystem.IsWindows() && Directory.Exists(objects))
            {
                var options = new EnumerationOptions
                {
                    RecurseSubdirectories = true,
                    AttributesToSkip = FileAttributes.ReparsePoint
                };
                foreach (FileInfo file in new DirectoryInfo(objects).EnumerateFiles("*", options))
                    if (file.IsReadOnly) file.IsReadOnly = false;
            }
        }
    }

    ConsumerSession PrepareConsumerSession(string session, string root, ConsumerDependency[] dependencies,
        SortedDictionary<string, string> snapshot, string certifiedLibrary, ExtractionIdentity extraction,
        IReadOnlyList<(string Module, string Proof)> proofs, string? symbols,
        IReadOnlyDictionary<string, string>? exportAudits = null,
        IReadOnlyDictionary<string, string>? generatedSources = null,
        ExtractionComponents? components = null, bool checkRejectedProofs = false)
    {
        foreach (var dependency in dependencies)
        {
            var destination = Within(session, Path.GetRelativePath(root, dependency.Directory));
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            if (fullBundleDependencies is null)
            {
                CloneConsumerDependency(dependency.Directory, destination);
                Run(["git", "remote", "set-url", "origin", dependency.Url], destination);
            }
            else Directory.CreateDirectory(destination);
        }
        var sources = new SourceCopies(session);
        foreach (var (key, hash) in snapshot.Where(p => p.Key.StartsWith("consumer:", StringComparison.Ordinal)))
        {
            var source = key["consumer:".Length..];
            var destination = Within(session, Path.GetRelativePath(root, source));
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(source, destination);
            if (Sha(destination) != hash) throw new InvalidDataException("Consumer source changed during copying: " + source);
            sources.Add(destination, source);
        }
        var framework = dependencies.Single(d => d.Name == "leancil");
        var frameworkCopy = Within(session, Path.GetRelativePath(root, framework.Source));
        // Lake reads the certified library in place and writes only below this session.
        string generatedPackage = UseCertifiedFramework(session, certifiedLibrary);
        // Give Lake a real generated-module target before building consumer imports.
        if (File.Exists(Path.Combine(frameworkCopy, "Extracted.lean")) || File.Exists(Path.Combine(session, "Extracted.lean")))
            throw new InvalidDataException("Extracted is reserved for the selected extraction artifact.");
        File.Copy(Path.Combine(extraction.Output, "Extracted.lean"), Path.Combine(generatedPackage, "Extracted.lean"));
        var generated = Sha(Path.Combine(generatedPackage, "Extracted.lean"));
        // Components replace this copy with generated text, which then fails the byte comparison and stays unmapped.
        var extractedCopy = (Path.Combine(generatedPackage, "Extracted.lean"),
            Path.Combine(extraction.Output, "Extracted.lean"));
        if (generated != extraction.GeneratedSha256)
            throw new InvalidDataException("Generated CIL changed during consumer snapshot.");
        AddConsumerLibrary(generatedPackage, "Extracted");
        var componentPaths = new List<string>();
        if (components is { Sources.Count: > 0 })
        {
            if (generated != components.InputHash)
                throw new InvalidDataException("Generated CIL changed before component preparation.");
            var packageRoots = dependencies.Select(dependency =>
                Within(session, Path.GetRelativePath(root, dependency.Source))).Prepend(session);
            var directories = ConsumerSourceDirectories(session, packageRoots);
            foreach (var (module, source) in components.Sources)
            {
                RejectContractSourceShadow(module, directories);
                var path = Path.Combine(generatedPackage, module + ".lean");
                File.WriteAllText(path, source);
                AddConsumerLibrary(generatedPackage, module);
                componentPaths.Add(path);
            }
            File.WriteAllText(Path.Combine(generatedPackage, "Extracted.lean"), components.Aggregate);
        }
        if (extraction.Sources.Count > 0)
        {
            var packageRoots = dependencies.Select(dependency =>
                Within(session, Path.GetRelativePath(root, dependency.Source))).Prepend(session);
            var sourceDirectories = ConsumerSourceDirectories(session, packageRoots);
            foreach (var module in extraction.Sources.Keys)
                RejectContractSourceShadow(module, sourceDirectories);
        }
        string[] importModules = StageImportSources(extraction, generatedPackage);
        foreach (string module in importModules) AddConsumerLibrary(generatedPackage, module);
        var symbolsPath = Path.Combine(generatedPackage, "ExtractedSymbols.lean");
        // Declared only when a proof imports it: symbol-free workspaces, and so their support keys, stay unchanged.
        if (symbols is not null)
        {
            if (File.Exists(symbolsPath) || File.Exists(Path.Combine(session, "ExtractedSymbols.lean")) ||
                snapshot.Keys.Any(k => k.StartsWith("consumer:", StringComparison.Ordinal) && Path.GetFileName(k) == "ExtractedSymbols.lean"))
                throw new InvalidDataException("ExtractedSymbols is reserved for the PDB names of the selected extraction.");
            File.Copy(Path.Combine(extraction.Output, "Symbols.lean"), symbolsPath);
            if (Sha(symbolsPath) != symbols) throw new InvalidDataException("PDB names changed during consumer snapshot.");
            sources.Add(symbolsPath, Path.Combine(extraction.Output, "Symbols.lean"));
            AddConsumerLibrary(generatedPackage, "ExtractedSymbols");
        }
        var copied = snapshot.Keys.Where(k => k.StartsWith("consumer:", StringComparison.Ordinal))
            .Select(k => Within(session, Path.GetRelativePath(root, k["consumer:".Length..])))
            .Append(Path.Combine(generatedPackage, "Extracted.lean")).ToList();
        if (checkRejectedProofs)
        {
            // Rejected proofs stop before the final native audit, so check the certificate first.
            var extractionAuditPath = Path.Combine(generatedPackage, "ExtractionAudit.lean");
            if (File.Exists(extractionAuditPath))
                throw new InvalidDataException("ExtractionAudit is reserved for the certificate audit.");
            File.WriteAllText(extractionAuditPath, ExtractionAuditSource);
            AddConsumerLibrary(generatedPackage, "ExtractionAudit");
            copied.Add(extractionAuditPath);
        }
        copied.AddRange(componentPaths);
        copied.AddRange(importModules.Select(module => Path.Combine(generatedPackage, module.Replace('.', Path.DirectorySeparatorChar) + ".lean")));
        if (symbols is not null) copied.Add(symbolsPath);
        if (generatedSources is not null)
        {
            var packageRoots = dependencies.Select(dependency =>
                Within(session, Path.GetRelativePath(root, dependency.Source))).Prepend(session);
            var directories = ConsumerSourceDirectories(session, packageRoots);
            foreach (var (module, source) in generatedSources)
            {
                RejectContractSourceShadow(module, directories);
                var path = Within(generatedPackage, module.Replace('.', '/') + ".lean");
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.WriteAllText(path, source);
                AddConsumerLibrary(generatedPackage, module);
                copied.Add(path);
            }
        }
        foreach ((string module, string proof) in proofs)
        {
            string target = Path.Combine(session, module + ".lean");
            if (File.Exists(target)) throw new InvalidDataException(module + " is reserved for the selected proof.");
            if (exportAudits is not null && exportAudits.TryGetValue(module, out string? audit))
            {
                string author = module + "Author";
                string authorPath = Path.Combine(session, author + ".lean");
                if (File.Exists(authorPath)) throw new InvalidDataException(author + " is reserved for the export author proof.");
                File.WriteAllBytes(authorPath,
                    CheckedProofBytes(File.ReadAllBytes(Path.Combine(session, Path.GetRelativePath(root, proof)))));
                AddConsumerLibrary(session, author, ProofOptions);
                copied.Add(authorPath);
                File.WriteAllText(target, "import " + author + "\n" + audit);
            }
            else
            {
                File.WriteAllBytes(target,
                    CheckedProofBytes(File.ReadAllBytes(Path.Combine(session, Path.GetRelativePath(root, proof)))));
                var original = Path.ChangeExtension(Path.GetRelativePath(root, proof), null).Replace('\\', '/')
                    .Replace('/', '.');
                if (ObservesProof) sources.AddObserved(target, proof, module, original);
                else sources.Add(target, proof, module, original);
            }
            AddConsumerLibrary(session, module, ProofOptions);
            copied.Add(target);
        }
        sources.Add(extractedCopy.Item1, extractedCopy.Item2);
        return new(generatedPackage, copied.ToDictionary(path => path, Sha), sources);
    }
}
