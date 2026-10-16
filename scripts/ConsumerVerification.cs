using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
    sealed record ConsumerSupportManifest(int Schema, string Policy, string Library, string Toolchain,
        SortedDictionary<string, string> Sources, SortedDictionary<string, SortedDictionary<string, string>> Modules,
        SortedDictionary<string, string[]> Imports);

    static SortedDictionary<string, string> PortableConsumerSources(string root, SortedDictionary<string, string> inputs) =>
        new(inputs.Where(pair => !pair.Key.StartsWith("proof:", StringComparison.Ordinal) &&
                !pair.Key.StartsWith("settings:", StringComparison.Ordinal))
            .ToDictionary(pair => pair.Key.StartsWith("consumer:", StringComparison.Ordinal)
                ? "consumer:" + Path.GetRelativePath(root, pair.Key[9..]).Replace('\\', '/') : pair.Key, pair => pair.Value), StringComparer.Ordinal);

    string ConsumerToolchainIdentity()
    {
        var directory = Path.Combine(Toolchain, "lib", "lean");
        var files = new SortedDictionary<string, string>(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
            .ToDictionary(path => Path.GetRelativePath(directory, path).Replace('\\', '/'), Sha), StringComparer.Ordinal);
        return ContentKey(JsonSerializer.Serialize(files));
    }

    static SortedDictionary<string, string> ConsumerModuleParts(string path)
    {
        var parts = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var suffix in new[] { "", ".server", ".private" })
            if (File.Exists(path + suffix)) parts[".olean" + suffix] = Sha(path + suffix);
        return parts;
    }

    void ExportConsumerSupport(string root, SortedDictionary<string, string> inputs,
        Dictionary<string, string> independent, Dictionary<string, string[]> graph)
    {
        var destination = Environment.GetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT");
        if (string.IsNullOrWhiteSpace(destination)) return;
        var modules = new SortedDictionary<string, SortedDictionary<string, string>>(
            independent.ToDictionary(pair => pair.Key, pair => ConsumerModuleParts(pair.Value)), StringComparer.Ordinal);
        var manifest = new ConsumerSupportManifest(1, VerificationPolicy, libraryKey!, ConsumerToolchainIdentity(),
            PortableConsumerSources(root, inputs), modules,
            new(independent.Keys.ToDictionary(name => name, name => graph[name]), StringComparer.Ordinal));
        var json = JsonSerializer.Serialize(manifest, Json) + "\n";
        var digest = ContentKey(json);
        Directory.CreateDirectory(destination);
        var path = Path.GetFullPath(Path.Combine(destination, digest + ".json"));
        // The trusted digest must travel separately from the downloadable manifest.
        var temporary = path + "." + Guid.NewGuid().ToString("N");
        try
        {
            File.WriteAllText(temporary, json);
            try { File.Move(temporary, path); }
            catch (IOException) when (File.Exists(path) && Sha(path) == digest) { }
        }
        finally { File.Delete(temporary); }
        Console.WriteLine("Certified consumer support manifest: " + path);
        Console.WriteLine("Certified consumer support SHA256: " + digest);
        var githubOutput = Environment.GetEnvironmentVariable("GITHUB_OUTPUT");
        if (!string.IsNullOrWhiteSpace(githubOutput))
            File.AppendAllText(githubOutput, "consumer-support-sha256=" + digest + "\n");
    }

    HashSet<string> ImportedConsumerSupport(string root, SortedDictionary<string, string> inputs,
        Dictionary<string, string> modules)
    {
        if (freshLibrary) return [];
        var path = Environment.GetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT");
        var digest = Environment.GetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256");
        if (string.IsNullOrWhiteSpace(path) && string.IsNullOrWhiteSpace(digest)) return [];
        if (string.IsNullOrWhiteSpace(path) || string.IsNullOrWhiteSpace(digest))
            throw new InvalidDataException("Consumer support manifest digest mismatch or missing trusted digest.");
        var bytes = File.ReadAllBytes(path);
        if (Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes)) != digest)
            throw new InvalidDataException("Consumer support manifest digest mismatch or missing trusted digest.");
        var manifest = JsonSerializer.Deserialize<ConsumerSupportManifest>(bytes)
            ?? throw new InvalidDataException("Invalid consumer support manifest.");
        if (manifest.Sources is null || manifest.Modules is null || manifest.Imports is null ||
            manifest.Modules.Any(pair => pair.Value is null || !manifest.Imports.TryGetValue(pair.Key, out var imports) || imports is null))
            throw new InvalidDataException("Invalid consumer support manifest.");
        if (manifest.Schema != 1 || manifest.Policy != VerificationPolicy || manifest.Library != libraryKey ||
            !Same(manifest.Sources, PortableConsumerSources(root, inputs)) || manifest.Toolchain != ConsumerToolchainIdentity()) return [];
        // Invalidate the entire dependent closure of changed or missing modules.
        // Unused producer modules need not be built by a different method gate.
        var invalid = manifest.Modules.Where(pair => !modules.TryGetValue(pair.Key, out var artifact) ||
            !Same(pair.Value, ConsumerModuleParts(artifact))).Select(pair => pair.Key).ToHashSet(StringComparer.Ordinal);
        bool changed;
        do
        {
            changed = false;
            foreach (var name in manifest.Modules.Keys)
                if (manifest.Imports[name].Any(import => invalid.Contains(import) ||
                    (!manifest.Modules.ContainsKey(import) &&
                     !File.Exists(Path.Combine(Toolchain, "lib/lean", import.Replace('.', '/') + ".olean")))))
                    changed |= invalid.Add(name);
        } while (changed);
        return manifest.Modules.Keys.Where(name => !invalid.Contains(name) && name != "CIL" && !name.StartsWith("CIL.", StringComparison.Ordinal) &&
            name is not ("Extracted" or "ExtractionAudit" or "LeanCILProof")).ToHashSet(StringComparer.Ordinal);
    }

    static void ReplayConsumerModules(string session, IEnumerable<string> modules)
    {
        var targets = modules.ToArray();
        var profile = Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") == "true";
        var configuredThreads = Environment.GetEnvironmentVariable("LEAN_NUM_THREADS");
        var threads = string.IsNullOrWhiteSpace(configuredThreads) ? "2" : configuredThreads;
        if (!uint.TryParse(threads, out var count) || count == 0)
            throw new InvalidDataException("LEAN_NUM_THREADS must be a positive integer.");
        var runner = Path.Combine(Path.GetTempPath(), "leancil-replay-" + Guid.NewGuid().ToString("N") + ".lean");
        try
        {
            // Use the pinned toolchain's checker, not a consumer implementation
            // of kernel replay. Explicit targets avoid repeated search-path scans.
            File.WriteAllText(runner, """
import LeanChecker
unsafe def replayConsumerModule (name : String) : IO Nat := do
  let started ← IO.monoMsNow
  replayFromImports name.toName
  return (← IO.monoMsNow) - started
def reportConsumerModule (name : String) (elapsed : Nat) : IO Unit :=
  IO.println (Lean.Json.mkObj [("module", Lean.toJson name), ("milliseconds", Lean.toJson elapsed)]).compress
unsafe def replayConsumerModules (args : List String) (profile : Bool) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  if profile then
    for name in args do
      reportConsumerModule name (← replayConsumerModule name)
  else
    let tasks ← args.toArray.mapM fun name => do
      return (name, ← IO.asTask (replayConsumerModule name))
    for (name, task) in tasks do
      match task.get with
      | .ok elapsed => reportConsumerModule name elapsed
      | .error error => throw error
""" + "\n#eval do\n  let json := String.fromUTF8! (ByteArray.mk #[" +
                string.Join(",", System.Text.Encoding.UTF8.GetBytes(JsonSerializer.Serialize(targets))) +
                "])\n  let args ← IO.ofExcept <| (Lean.Json.parse json).bind Lean.fromJson?\n  replayConsumerModules args " +
                profile.ToString().ToLowerInvariant() + "\n");
            // Unlike leanchecker, the lean frontend defaults to hardware
            // concurrency rather than honoring LEAN_NUM_THREADS itself.
            Run(["lake", "env", "lean", "-j" + threads, runner], session, progress: profile
                ? "Profiled kernel replay of consumer modules" : "Kernel replay of consumer proof and dependencies");
        }
        finally { File.Delete(runner); }
    }

    sealed record ConsumerDependency(string Name, string Directory, string Source, string Revision, string Url);

    static string Within(string root, string relative)
    {
        var path = Path.GetFullPath(relative, root);
        var back = Path.GetRelativePath(root, path);
        if (Path.IsPathRooted(back) || back == ".." || back.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            throw new InvalidDataException("Consumer path escapes its package: " + relative);
        return path;
    }

    static IEnumerable<string> ConsumerSources(string root, string? excludedDirectory = null)
    {
        if (excludedDirectory is not null && Path.GetFullPath(root) == Path.GetFullPath(excludedDirectory)) yield break;
        foreach (var path in Directory.EnumerateFileSystemEntries(root).Order(StringComparer.Ordinal))
        {
            if ((File.GetAttributes(path) & FileAttributes.ReparsePoint) != 0)
                throw new InvalidDataException("Consumer sources must not contain symbolic links: " + path);
            if (Directory.Exists(path))
            {
                if (Path.GetFileName(path) is ".git" or ".lake" or "artifacts" or "generated" or "bin" or "obj" or ".work") continue;
                foreach (var source in ConsumerSources(path, excludedDirectory)) yield return source;
            }
            else if (Path.GetExtension(path) is ".lean" or ".toml" or ".json" || Path.GetFileName(path) == "lean-toolchain")
                yield return path;
        }
    }

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

    static SortedDictionary<string, string> ConsumerInputs(string root, string proof, string? settings, string output)
    {
        var inputs = Inputs(proof, settings);
        var dependencies = ConsumerDependencies(root);
        foreach (var directory in new[] { root }.Concat(dependencies.Select(d => d.Directory)))
            foreach (var path in ConsumerSources(directory, output)) inputs["consumer:" + path] = Sha(path);
        foreach (var dependency in dependencies) inputs["revision:" + dependency.Name] = dependency.Revision;
        if (inputs.Keys.Any(k => k.StartsWith("consumer:", StringComparison.Ordinal) && Path.GetFileName(k) == "Extracted.lean"))
            throw new InvalidDataException("Extracted.lean is reserved for the selected extraction artifact; remove stale generated sources from the consumer package.");
        var framework = dependencies.SingleOrDefault(d => d.Name == "leancil")
            ?? throw new InvalidDataException("Consumer package must depend on leancil. Run lake update first.");
        foreach (var path in Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories)
            .Append(At("CIL.lean")).Append(At("lean-toolchain")))
        {
            var consumer = Path.Combine(framework.Source, Path.GetRelativePath(Root, path));
            if (!File.Exists(consumer) || File.ReadAllText(consumer).ReplaceLineEndings("\n") != File.ReadAllText(path).ReplaceLineEndings("\n"))
                throw new InvalidDataException("Consumer leancil sources differ from the verifier's bundled framework: " + consumer);
        }
        if (File.ReadAllText(Path.Combine(root, "lean-toolchain")).Trim() != File.ReadAllText(At("lean-toolchain")).Trim())
            throw new InvalidDataException("Consumer and verifier Lean toolchains differ.");
        return inputs;
    }

    static void AddConsumerLibrary(string directory, string name)
    {
        var toml = Path.Combine(directory, "lakefile.toml");
        if (File.Exists(toml))
            File.AppendAllText(toml, $"\n[[lean_lib]]\nname = \"{name}\"\n");
        else
            File.AppendAllText(Path.Combine(directory, "lakefile.lean"), $"\nlean_lib {name}\n");
    }

    string[] ConsumerImportDirectories(string session)
    {
        // Ask the same Lake environment used by the checker. Package buildDir and
        // leanLibDir need not be the default .lake/build/lib/lean directories.
        var probe = Path.Combine(session, "LeanCILPaths" + Guid.NewGuid().ToString("N") + ".lean");
        string output;
        try
        {
            File.WriteAllText(probe, "def main : IO Unit := do\n  IO.println (\"LEANCIL_LEAN_PATH=\" ++ (← IO.getEnv \"LEAN_PATH\").getD \"\")\n");
            output = Run(["lake", "env", "lean", "--run", probe], session);
        }
        finally { File.Delete(probe); }
        var lines = output.Split('\n', StringSplitOptions.TrimEntries)
            .Where(line => line.StartsWith("LEANCIL_LEAN_PATH=", StringComparison.Ordinal)).ToArray();
        if (lines.Length != 1) throw new InvalidDataException("Could not resolve consumer Lean import paths.");
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        var trusted = Path.GetFullPath(Path.Combine(Toolchain, "lib/lean"));
        return lines[0]["LEANCIL_LEAN_PATH=".Length..].Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(path => Path.TrimEndingDirectorySeparator(Path.GetFullPath(path, session)))
            .Where(path => !path.Equals(trusted, comparison))
            .Select(path => Within(session, Path.GetRelativePath(session, path)))
            .Distinct(OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal).ToArray();
    }

    // A deliberately conservative key: include all package sources (not only the
    // selected proof's syntactic imports), pinned revisions, and effective config.
    // Only artifacts whose compiled import closure excludes Extracted are shared.
    string ConsumerCacheKey(string kind, SortedDictionary<string, string> inputs, string extra) =>
        ContentKey("consumer-" + kind + "-v1\n" + VerificationPolicy + "\n" + libraryKey + "\n" +
            Sha(Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean")) + "\n" +
            Sha(Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker")) + "\n" +
            // lakefile.lean may consult environment variables when choosing
            // options/plugins. Bind them conservatively; never log their values.
            JsonSerializer.Serialize(new SortedDictionary<string, string>(Environment.GetEnvironmentVariables()
                .Cast<System.Collections.DictionaryEntry>().ToDictionary(entry => (string)entry.Key, entry => (string)entry.Value!), StringComparer.Ordinal)) + "\n" +
            JsonSerializer.Serialize(inputs) + "\n" + extra);

    Dictionary<string, string[]> ConsumerModuleImports(string session, Dictionary<string, string> modules)
    {
        // Read Lean's compiled import headers, not a regex over source text. This
        // also handles public/private imports and transitive package dependencies.
        var probe = Path.Combine(session, "LeanCILImports" + Guid.NewGuid().ToString("N") + ".lean");
        var input = probe + ".json";
        try
        {
            File.WriteAllText(probe, """
import Lean
unsafe def main (args : List String) : IO Unit := do
  let [input] := args | throw (IO.userError "Expected module manifest")
  let paths : Array String ← IO.ofExcept <| (Lean.Json.parse (← IO.FS.readFile input)).bind Lean.fromJson?
  for path in paths do
    let (data, region) ← Lean.readModuleData path
    IO.println (Lean.Json.arr (data.imports.map fun i => Lean.Json.str i.module.toString)).compress
    region.free
""");
            var paths = modules.Values.ToArray();
            File.WriteAllText(input, JsonSerializer.Serialize(paths));
            var result = Run(["lean", "--run", probe, input], session);
            var lines = result.Split('\n', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
            if (lines.Length != paths.Length) throw new InvalidDataException("Incomplete consumer compiled import graph.");
            return modules.Keys.Zip(lines).ToDictionary(pair => pair.First,
                pair => JsonSerializer.Deserialize<string[]>(pair.Second) ?? throw new InvalidDataException("Invalid import graph."));
        }
        finally { File.Delete(probe); File.Delete(input); }
    }

    void PublishConsumerSupport(string session, string key, string[] directories, string proofModule,
        string root, SortedDictionary<string, string> inputs)
    {
        if (!UseSuccessCache && string.IsNullOrWhiteSpace(Environment.GetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT"))) return;
        var modules = directories.Where(Directory.Exists)
            .SelectMany(directory => Directory.EnumerateFiles(directory, "*.olean", SearchOption.AllDirectories)
                .Select(path => (Name: ModuleName(Path.GetRelativePath(directory, path).Replace('\\', '/')), Path: path)))
            .ToDictionary(pair => pair.Name, pair => pair.Path, StringComparer.Ordinal);
        var graph = ConsumerModuleImports(session, modules);
        var dependent = new HashSet<string>(["Extracted", "ExtractionAudit", proofModule], StringComparer.Ordinal);
        bool changed;
        do
        {
            changed = false;
            foreach (var (name, imports) in graph)
                if (imports.Any(dependent.Contains)) changed |= dependent.Add(name);
        } while (changed);
        ExportConsumerSupport(root, inputs, modules.Where(pair => !dependent.Contains(pair.Key)).ToDictionary(), graph);
        if (!UseSuccessCache) return;
        var publication = Path.Combine(Path.GetTempPath(), "leancil-consumer-support-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(publication);
        try
        {
            var generatedArtifacts = Directory.EnumerateFiles(session, "*", SearchOption.AllDirectories)
                .Select(path => (Path: path, Relative: Path.GetRelativePath(session, path).Replace('\\', '/')))
                .Where(file => !file.Relative.Split('/').Contains(".git") &&
                    new[] { ".c", ".c.hash", ".ir", ".ir.hash", ".setup.json" }.Any(suffix => file.Relative.EndsWith(suffix, StringComparison.Ordinal)))
                .ToArray();
            foreach (var (name, path) in modules.Where(pair => !dependent.Contains(pair.Key) &&
                pair.Key != "CIL" && !pair.Key.StartsWith("CIL.", StringComparison.Ordinal)))
            {
                var stem = Path.GetFileNameWithoutExtension(path);
                foreach (var artifact in Directory.EnumerateFiles(Path.GetDirectoryName(path)!, stem + ".*"))
                {
                    // A sibling module Foo.Bar must not be mistaken for Foo's artifact.
                    var suffix = Path.GetFileName(artifact)[stem.Length..];
                    if (suffix is not (".olean" or ".olean.hash" or ".olean.private" or ".olean.private.hash" or
                        ".olean.server" or ".olean.server.hash" or ".ilean" or ".ilean.hash" or ".trace" or ".ir" or ".ir.hash")) continue;
                    var target = Within(publication, Path.GetRelativePath(session, artifact));
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(artifact, target);
                }
                // Lake's olean trace also records generated C/IR outputs. Without
                // those outputs it recompiles an otherwise valid cached module.
                // Search by full module suffix to respect custom build/IR dirs.
                var modulePath = name.Replace('.', '/');
                foreach (var artifact in generatedArtifacts)
                {
                    if (!new[] { ".c", ".c.hash", ".ir", ".ir.hash", ".setup.json" }
                        .Any(suffix => artifact.Relative.EndsWith("/" + modulePath + suffix, StringComparison.Ordinal))) continue;
                    var target = Within(publication, artifact.Relative);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(artifact.Path, target, true);
                }
            }
            // Append immutable certified generations: later gates may discover
            // additional independent helpers that were absent from the first gate.
            PublishSuccess(key + "-" + ContentKey(JsonSerializer.Serialize(CacheFiles(publication))), publication);
        }
        finally { Directory.Delete(publication, true); }
    }

    Report VerifyConsumer(string assembly, string proof, string output, string theorem, string root,
        string? settings, Action<string>? stage)
    {
        root = Path.GetFullPath(root);
        proof = Within(root, Path.GetRelativePath(root, proof));
        var reportPath = Path.Combine(output, "verified.json");
        File.Delete(reportPath);
        stage?.Invoke("extraction integrity");
        Run(["dotnet", ExtractorPath, "check", output]);
        stage?.Invoke("consumer source snapshot");
        var before = ConsumerInputs(root, proof, settings, output);
        if (!before.ContainsKey("consumer:" + proof))
            throw new InvalidDataException("Proof must be a Lean source under the consumer root, outside excluded build/artifact directories.");
        stage?.Invoke("Lean library build");
        var certifiedLibrary = Library(Inputs(proof, settings));
        var certifiedBase = ModuleArtifacts(certifiedLibrary).Where(pair =>
            ModuleName(pair.Key) == "CIL" || ModuleName(pair.Key).StartsWith("CIL.", StringComparison.Ordinal)).ToDictionary();
        var identityHash = Sha(Path.Combine(output, "identity.json"));
        var proofKey = ConsumerCacheKey("proof", before, identityHash + "\n" + theorem + "\n" + Sha(assembly));
        var session = Path.Combine(Path.GetTempPath(), "leancil-consumer-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(session);
        try
        {
            var receipt = Path.Combine(session, "certified-result");
            if (RestoreSuccess(proofKey, receipt))
            {
                var cached = JsonSerializer.Deserialize<Report>(File.ReadAllText(Path.Combine(receipt, "report.json")))!;
                Run(["dotnet", ExtractorPath, "check", output]);
                if (!Same(before, ConsumerInputs(root, proof, settings, output)) || identityHash != Sha(Path.Combine(output, "identity.json")))
                    throw new InvalidOperationException("Inputs changed during consumer verification");
                var reused = cached with { libraryBuild = "consumer-proof-cache" };
                File.WriteAllText(reportPath, JsonSerializer.Serialize(reused, Json) + "\n");
                CacheProgress("certified consumer proof: " + theorem);
                return reused;
            }
            var dependencies = ConsumerDependencies(root);
            foreach (var dependency in dependencies)
            {
                var destination = Within(session, Path.GetRelativePath(root, dependency.Directory));
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                Run(["git", "clone", "--no-hardlinks", "--no-checkout", dependency.Directory, destination]);
                Run(["git", "remote", "set-url", "origin", dependency.Url], destination);
            }
            foreach (var (key, hash) in before.Where(p => p.Key.StartsWith("consumer:", StringComparison.Ordinal)))
            {
                var source = key["consumer:".Length..];
                var destination = Within(session, Path.GetRelativePath(root, source));
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.Copy(source, destination);
                if (Sha(destination) != hash) throw new InvalidDataException("Consumer source changed during copying: " + source);
            }
            var framework = dependencies.Single(d => d.Name == "leancil");
            var frameworkCopy = Within(session, Path.GetRelativePath(root, framework.Source));
            // ConsumerInputs already checked normalized source equality. Use the
            // certified bytes (including line endings) so Lake can reuse its traces.
            foreach (var path in Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories).Append(At("CIL.lean")))
                File.Copy(path, Path.Combine(frameworkCopy, Path.GetRelativePath(Root, path)), true);
            var baseBuild = Path.Combine(certifiedLibrary, ".lake/build");
            var frameworkBuild = Path.Combine(frameworkCopy, ".lake/build");
            foreach (var path in Directory.EnumerateFiles(baseBuild, "*", SearchOption.AllDirectories))
            {
                var relative = Path.GetRelativePath(baseBuild, path).Replace('\\', '/');
                if (!new[] { "lib/lean/CIL/", "lib/lean/CIL.", "ir/CIL/", "ir/CIL." }
                    .Any(prefix => relative.StartsWith(prefix, StringComparison.Ordinal))) continue;
                var destination = Path.Combine(frameworkBuild, relative);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.Copy(path, destination, true);
            }
            // Give Lake a real generated-module target before building consumer imports.
            if (File.Exists(Path.Combine(frameworkCopy, "Extracted.lean")) || File.Exists(Path.Combine(session, "Extracted.lean")))
                throw new InvalidDataException("Extracted is reserved for the selected extraction artifact.");
            File.Copy(Path.Combine(output, "Extracted.lean"), Path.Combine(frameworkCopy, "Extracted.lean"));
            var extraction = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
            if (Sha(Path.Combine(frameworkCopy, "Extracted.lean")) != extraction.GetProperty("generatedSha256").GetString())
                throw new InvalidDataException("Generated CIL changed during consumer snapshot.");
            AddConsumerLibrary(frameworkCopy, "Extracted");
            var extractionAuditPath = Path.Combine(frameworkCopy, "ExtractionAudit.lean");
            if (File.Exists(extractionAuditPath)) throw new InvalidDataException("ExtractionAudit is reserved for the certificate audit.");
            File.WriteAllText(extractionAuditPath, ExtractionAuditSource);
            AddConsumerLibrary(frameworkCopy, "ExtractionAudit");
            const string proofModule = "LeanCILProof";
            if (File.Exists(Path.Combine(session, proofModule + ".lean")))
                throw new InvalidDataException("LeanCILProof is reserved for the selected proof.");
            File.Copy(Path.Combine(session, Path.GetRelativePath(root, proof)), Path.Combine(session, proofModule + ".lean"));
            AddConsumerLibrary(session, proofModule);
            var copied = before.Keys.Where(k => k.StartsWith("consumer:", StringComparison.Ordinal))
                .Select(k => Within(session, Path.GetRelativePath(root, k["consumer:".Length..])))
                .Append(Path.Combine(frameworkCopy, "Extracted.lean"))
                .Append(extractionAuditPath)
                .Append(Path.Combine(session, proofModule + ".lean"))
                .ToDictionary(path => path, Sha);
            var initialImportDirectories = ConsumerImportDirectories(session);
            var supportInputs = new SortedDictionary<string, string>(before.Where(pair =>
                !pair.Key.StartsWith("proof:", StringComparison.Ordinal) && !pair.Key.StartsWith("settings:", StringComparison.Ordinal))
                .ToDictionary(), StringComparer.Ordinal);
            var configuration = copied.Where(pair => Path.GetFileName(pair.Key) is "lakefile.toml" or "lakefile.lean" or "lake-manifest.json")
                .OrderBy(pair => pair.Key, StringComparer.Ordinal)
                .Select(pair => Path.GetRelativePath(session, pair.Key) + ":" + pair.Value);
            var supportKey = ConsumerCacheKey("support", supportInputs,
                string.Join("\n", initialImportDirectories.Select(path => Path.GetRelativePath(session, path))) + "\n" + string.Join("\n", configuration));
            var restoredArtifacts = new SortedDictionary<string, string>(StringComparer.Ordinal);
            var restoredDirectory = Path.Combine(Path.GetTempPath(), "leancil-consumer-restored-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(restoredDirectory);
            try
            {
                var restored = false;
                foreach (var generation in UseSuccessCache && Directory.Exists(SuccessCacheRoot)
                    ? Directory.EnumerateDirectories(SuccessCacheRoot, supportKey + "-*").OrderByDescending(Directory.GetLastWriteTimeUtc)
                    : Enumerable.Empty<string>())
                {
                    // RestoreSuccess verifies the local producer signature and all
                    // artifact hashes. Staging directories never have a valid receipt.
                    if (RestoreSuccess(Path.GetFileName(generation), restoredDirectory))
                    {
                        restored = true;
                        break;
                    }
                    // An interrupted copy may leave partial files; they have no
                    // reusable certificate and must never enter the package.
                    Directory.Delete(restoredDirectory, true);
                    Directory.CreateDirectory(restoredDirectory);
                }
                if (restored) restoredArtifacts = CacheFiles(restoredDirectory);
                if (restoredArtifacts.Count > 0)
                {
                    CopyTree(restoredDirectory, session);
                    CacheProgress("certified consumer support library");
                }
            }
            finally { Directory.Delete(restoredDirectory, true); }
            // Snapshot before invoking Lake: configuration elaboration and imported
            // metaprograms must not redefine the source bytes accepted by this run.
            stage?.Invoke("extraction certificate audit");
            var extractionAudit = Run(["lake", "build", "+ExtractionAudit:olean"], frameworkCopy,
                progress: "Checking consumer extraction certificate");
            AuditedAxioms(extractionAudit, "ExtractionAudit.valid");
            stage?.Invoke("proof checking");
            Run(["lake", "build", "+" + proofModule + ":olean"], session, progress: "Building fresh consumer proof and dependencies");
            // Replay every consumer/external module, including unused declarations.
            // Only identical artifacts in the validated framework package can reuse
            // the base certificate; a same-named consumer module cannot inherit it.
            stage?.Invoke("kernel replay");
            var importDirectories = ConsumerImportDirectories(session);
            if (!initialImportDirectories.SequenceEqual(importDirectories))
                throw new InvalidDataException("Consumer import paths changed during verification.");
            var supportUnchanged = restoredArtifacts.Count > 0 && restoredArtifacts.Where(pair =>
                Path.GetFileName(pair.Key).Contains(".olean", StringComparison.Ordinal)).All(pair =>
                File.Exists(Within(session, pair.Key)) && Sha(Within(session, pair.Key)) == pair.Value);
            var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
            var frameworkModules = Path.GetFullPath(Path.Combine(frameworkCopy, ".lake/build/lib/lean"));
            var currentBase = ModuleArtifacts(frameworkCopy).Where(pair =>
                ModuleName(pair.Key) == "CIL" || ModuleName(pair.Key).StartsWith("CIL.", StringComparison.Ordinal)).ToDictionary();
            var baseUnchanged = importDirectories.Any(path => path.Equals(frameworkModules, comparison)) &&
                certifiedBase.Count == currentBase.Count &&
                certifiedBase.All(pair => currentBase.TryGetValue(pair.Key, out var hash) && hash == pair.Value);
            var names = new HashSet<string>(StringComparer.Ordinal);
            var discovered = new List<(string Name, bool Certified)>();
            foreach (var directory in importDirectories)
            {
                if (!Directory.Exists(directory)) continue;
                var artifacts = Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
                    .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
                    .Select(path => new KeyValuePair<string, string>(Path.GetRelativePath(directory, path).Replace('\\', '/'), Sha(path)));
                foreach (var module in artifacts.GroupBy(pair => ModuleName(pair.Key)))
                {
                    if (!names.Add(module.Key)) throw new InvalidDataException("Ambiguous consumer module: " + module.Key);
                    if (File.Exists(Path.Combine(Toolchain, "lib/lean", module.Key.Replace('.', '/') + ".olean")))
                        throw new InvalidDataException("Consumer module shadows the trusted Lean toolchain: " + module.Key);
                    var unchanged = directory.Equals(frameworkModules, comparison) &&
                        module.Count() == certifiedBase.Count(pair => ModuleName(pair.Key) == module.Key) &&
                        module.All(pair => certifiedBase.TryGetValue(pair.Key, out var hash) && hash == pair.Value);
                    if (!unchanged && (module.Key == "CIL" || module.Key.StartsWith("CIL.", StringComparison.Ordinal)))
                        baseUnchanged = false;
                    var certifiedSupport = supportUnchanged && module.All(pair =>
                    {
                        var relative = Path.GetRelativePath(session, Path.Combine(directory, pair.Key));
                        return restoredArtifacts.TryGetValue(relative.Replace('\\', '/'), out var hash) && hash == pair.Value;
                    });
                    discovered.Add((module.Key, unchanged || certifiedSupport));
                }
            }
            if (!names.Contains(proofModule) || !names.Contains("Extracted") || !names.Contains("ExtractionAudit"))
                throw new InvalidDataException("Consumer proof or certificate is missing from the resolved import paths.");
            var currentArtifacts = importDirectories.Where(Directory.Exists).SelectMany(directory =>
                Directory.EnumerateFiles(directory, "*.olean", SearchOption.AllDirectories).Select(path =>
                    (Name: ModuleName(Path.GetRelativePath(directory, path).Replace('\\', '/')), Path: path)))
                .ToDictionary(pair => pair.Name, pair => pair.Path, StringComparer.Ordinal);
            var portableSupport = ImportedConsumerSupport(root, before, currentArtifacts);
            var checkedArtifacts = JsonSerializer.Serialize(currentArtifacts.OrderBy(pair => pair.Key, StringComparer.Ordinal)
                .ToDictionary(pair => pair.Key, pair => ConsumerModuleParts(pair.Value)));
            var modules = discovered.Where(module => !baseUnchanged || (!module.Certified && !portableSupport.Contains(module.Name)))
                .Select(module => module.Name);
            ReplayConsumerModules(session, modules);
            var auditPath = Path.Combine(session, "LeanCILAudit.lean");
            File.WriteAllText(auditPath, $"import {proofModule}\nrun_cmd do\n  match (← Lean.getEnv).find? `{theorem} with\n  | some (.thmInfo _) => pure ()\n  | _ => throwError \"Expected a theorem\"\n#check {theorem}\n#print axioms {theorem}\n");
            stage?.Invoke("theorem audit");
            var audit = Run(["lake", "env", "lean", auditPath], session);
            var matches = Regex.Matches(audit, "'" + Regex.Escape(theorem) + @"' depends on axioms:\s*\[([^\]]*)\]");
            if (matches.Count > 1 || (matches.Count == 0 && !audit.Contains($"'{theorem}' does not depend on any axioms")))
                throw new InvalidOperationException("Missing or ambiguous transitive theorem axiom audit");
            var axioms = matches.Count == 0 ? [] : matches[0].Groups[1].Value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
            if (axioms.Any(a => a is not ("propext" or "Quot.sound" or "Classical.choice")))
                throw new InvalidOperationException("Unapproved proof axioms: " + string.Join(", ", axioms));
            stage?.Invoke("extraction integrity");
            Run(["dotnet", ExtractorPath, "check", output]);
            if (!Same(before, ConsumerInputs(root, proof, settings, output)) || identityHash != Sha(Path.Combine(output, "identity.json")))
                throw new InvalidOperationException("Inputs changed during consumer verification");
            if (copied.Any(pair => !File.Exists(pair.Key) || Sha(pair.Key) != pair.Value))
                throw new InvalidOperationException("Sources changed in the fresh consumer build");
            var finalArtifacts = importDirectories.Where(Directory.Exists).SelectMany(directory =>
                Directory.EnumerateFiles(directory, "*.olean", SearchOption.AllDirectories).Select(path =>
                    (Name: ModuleName(Path.GetRelativePath(directory, path).Replace('\\', '/')), Path: path)))
                .OrderBy(pair => pair.Name, StringComparer.Ordinal)
                .ToDictionary(pair => pair.Name, pair => ConsumerModuleParts(pair.Path));
            if (checkedArtifacts != JsonSerializer.Serialize(finalArtifacts))
                throw new InvalidOperationException("Compiled artifacts changed during consumer verification");
            var initializedTypes = extraction.TryGetProperty("initializedTypes", out var assumptions)
                ? assumptions.Deserialize<string[]>() : [];
            var report = new Report(3, Sha(assembly), identityHash, theorem, axioms, audit, before,
                libraryKey, "consumer-" + libraryBuild, extractionAudit, initializedTypes,
                consumerSupportSha256: baseUnchanged && portableSupport.Count > 0
                    ? Environment.GetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256") : null);
            // Publish only after the complete declaration replay, exact theorem
            // audit, extraction recheck and source-stability checks succeeded.
            PublishConsumerSupport(session, supportKey, importDirectories, proofModule, root, before);
            Directory.CreateDirectory(receipt);
            File.WriteAllText(Path.Combine(receipt, "report.json"), JsonSerializer.Serialize(report, Json));
            PublishSuccess(proofKey, receipt);
            File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");
            return report;
        }
        finally { Directory.Delete(session, true); }
    }
}
