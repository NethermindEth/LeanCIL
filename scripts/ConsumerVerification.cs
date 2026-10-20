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

    // Exclude only Lean's persisted linter diagnostics, never strings in
    // declarations or other environment extensions. Keep every module part.
    Dictionary<string, SortedDictionary<string, string>> PortableConsumerModuleParts(
        string session, Dictionary<string, string> modules)
    {
        var temporary = Path.Combine(Path.GetTempPath(), "leancil-fingerprints-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(temporary);
        try
        {
            var probe = Path.Combine(temporary, "Fingerprint.lean");
            File.WriteAllText(probe, """
import Lean
@[noinline] def fingerprintModule (name : String) (sources destinations : Array String) :
    IO (Array Lean.CompactedRegion) := do
  let parts ← Lean.readModuleDataParts (sources.map System.FilePath.mk)
  let filtered := parts.map fun (data, _) =>
    { data with entries := data.entries.filter (fun entry => entry.1 != `Lean.Linter.lintLogExt) }
  Lean.saveModuleDataParts name.toName (destinations.map System.FilePath.mk |>.zip filtered)
  return parts.map Prod.snd
unsafe def main (args : List String) : IO Unit := do
  let [input] := args | throw (IO.userError "Expected fingerprint manifest")
  let modules : Array (String × Array String × Array String) ←
    IO.ofExcept <| (Lean.Json.parse (← IO.FS.readFile input)).bind Lean.fromJson?
  for (name, sources, destinations) in modules do
    -- Drop the reconstructed data before unmapping its referenced objects.
    let regions ← fingerprintModule name sources destinations
    for region in regions.reverse do
      region.free
""");
            var paths = modules.Select((pair, index) => (pair.Key, Source: pair.Value,
                Destination: Path.Combine(temporary, index + ".olean"))).ToArray();
            var input = Path.Combine(temporary, "modules.json");
            File.WriteAllText(input, JsonSerializer.Serialize(paths.Select(item => new object[]
            {
                item.Key,
                new object[]
                {
                    new[] { "", ".server", ".private" }.Where(suffix => File.Exists(item.Source + suffix)).Select(suffix => item.Source + suffix).ToArray(),
                    new[] { "", ".server", ".private" }.Where(suffix => File.Exists(item.Source + suffix)).Select(suffix => item.Destination + suffix).ToArray()
                }
            })));
            Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean"),
                "-j2", "--run", probe, input], session, progress: "Fingerprinting portable consumer modules");
            return paths.ToDictionary(item => item.Key, item => ConsumerModuleParts(item.Destination));
        }
        finally { Directory.Delete(temporary, true); }
    }

    void ExportConsumerSupport(string session, string root, SortedDictionary<string, string> inputs,
        Dictionary<string, string> independent, Dictionary<string, string[]> graph)
    {
        var destination = Environment.GetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT");
        if (string.IsNullOrWhiteSpace(destination)) return;
        var modules = new SortedDictionary<string, SortedDictionary<string, string>>(
            PortableConsumerModuleParts(session, independent), StringComparer.Ordinal);
        var manifest = new ConsumerSupportManifest(2, VerificationPolicy, libraryKey!, ConsumerToolchainIdentity(),
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

    HashSet<string> ImportedConsumerSupport(string session, string root, SortedDictionary<string, string> inputs,
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
        if (manifest.Schema != 2 || manifest.Policy != VerificationPolicy || manifest.Library != libraryKey ||
            !Same(manifest.Sources, PortableConsumerSources(root, inputs)) || manifest.Toolchain != ConsumerToolchainIdentity()) return [];
        var fingerprints = PortableConsumerModuleParts(session,
            modules.Where(pair => manifest.Modules.ContainsKey(pair.Key)).ToDictionary());
        // Invalidate the entire dependent closure of changed or missing modules.
        // Unused producer modules need not be built by a different method gate.
        var invalid = manifest.Modules.Where(pair => !fingerprints.TryGetValue(pair.Key, out var parts) ||
            !Same(pair.Value, parts)).Select(pair => pair.Key).ToHashSet(StringComparer.Ordinal);
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
            name is not ("Extracted" or "ExtractionAudit") && !name.StartsWith("LeanCILProof", StringComparison.Ordinal)).ToHashSet(StringComparer.Ordinal);
    }


    string LeanExecutable => Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean");

    // Pin the sysroot that `lake env` would supply, so direct Lean runs use the trusted toolchain.
    IReadOnlyDictionary<string, string> LeanEnvironment => new Dictionary<string, string> { ["LEAN_SYSROOT"] = Toolchain };

    // Per-module replay re-imports each module's dependencies; one shared import of
    // everything outside the targets makes large sets several times cheaper.
    // No target constant may preexist, since Replay skips matching theorems unchecked.
    const string JointReplaySource = """
import LeanChecker
unsafe def readConsumerParts (module : Lean.Name) : IO (Lean.ModuleData × Lean.ModuleData) := do
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
unsafe def replayConsumerModulesJointly (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let started ← IO.monoMsNow
  let names := args.map String.toName
  let targets : Lean.NameSet := names.foldl (·.insert ·) {}
  let mut imports : Std.HashMap Lean.Name Lean.Import := {}
  let mut constants : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for module in names do
    let (exported, complete) ← readConsumerParts module
    for i in exported.imports do
      unless targets.contains i.module do
        imports := imports.insert i.module <| match imports[i.module]? with
          | some j => { j with importAll := j.importAll || i.importAll, isExported := j.isExported || i.isExported, isMeta := j.isMeta || i.isMeta }
          | none => i
    -- The most private part subsumes the others.
    for name in complete.constNames, ci in complete.constants do
      if constants.contains name then
        throw <| IO.userError s!"Constant {name} is declared by more than one replay target"
      constants := constants.insert name ci
  let external := imports.toArray.map (·.2) |>.qsort (·.module.toString < ·.module.toString)
  let (_, s) ← Lean.importModulesCore external |>.run
  let env ← Lean.finalizeImport s external {} 0 false false (isModule := true)
  for (name, _) in constants do
    if env.contains name then
      throw <| IO.userError s!"Replay target constant {name} is already imported"
  discard <| env.toKernelEnv.replay constants
  env.freeRegions
  let elapsed := (← IO.monoMsNow) - started
  for name in args do
    IO.println (Lean.Json.mkObj [("module", Lean.toJson name), ("joint", Lean.toJson true), ("milliseconds", Lean.toJson elapsed)]).compress
""";

    // Every requested module is reported as replayed or rejected; a checker process failure throws.
    Dictionary<string, string> ReplayConsumerModules(string session, IEnumerable<string> modules, string leanPath)
    {
        var targets = modules.ToArray();
        var profile = Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") == "true";
        // A rejected or ineligible joint replay falls through to per-module replay, which attributes failures.
        if (!profile && targets.Length > 1 && ReplayConsumerModulesJointly(session, targets, leanPath)) return [];
        return ReplayConsumerModulesSeparately(session, targets, leanPath, profile);
    }

    bool ReplayConsumerModulesJointly(string session, string[] targets, string leanPath)
    {
        var runner = Path.Combine(Path.GetTempPath(), "leancil-joint-replay-" + Guid.NewGuid().ToString("N") + ".lean");
        var targetsPath = Path.ChangeExtension(runner, ".json");
        try
        {
            File.WriteAllText(targetsPath, JsonSerializer.Serialize(targets));
            File.WriteAllText(runner, JointReplaySource + "\n#eval do\n  let json ← IO.FS.readFile (String.fromUTF8! (ByteArray.mk #[" +
                string.Join(",", System.Text.Encoding.UTF8.GetBytes(targetsPath)) +
                "]))\n  let args ← IO.ofExcept <| (Lean.Json.parse json).bind Lean.fromJson?\n  replayConsumerModulesJointly args\n");
            var result = Execute([LeanExecutable, runner], session, leanPath,
                progress: "Joint kernel replay of consumer proof and dependencies", environment: LeanEnvironment);
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

    Dictionary<string, string> ReplayConsumerModulesSeparately(string session, string[] targets, string leanPath, bool profile)
    {
        var configuredThreads = Environment.GetEnvironmentVariable("LEAN_NUM_THREADS");
        var threads = string.IsNullOrWhiteSpace(configuredThreads) ? "2" : configuredThreads;
        if (!uint.TryParse(threads, out var count) || count == 0)
            throw new InvalidDataException("LEAN_NUM_THREADS must be a positive integer.");
        var runner = Path.Combine(Path.GetTempPath(), "leancil-replay-" + Guid.NewGuid().ToString("N") + ".lean");
        var targetsPath = Path.ChangeExtension(runner, ".json");
        try
        {
            // A literal target list exceeds Lean's recursion limit for large module sets.
            File.WriteAllText(targetsPath, JsonSerializer.Serialize(targets));
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
def reportConsumerFailure (name : String) (error : IO.Error) : IO Unit :=
  IO.println (Lean.Json.mkObj [("module", Lean.toJson name), ("error", Lean.toJson (toString error))]).compress
unsafe def replayConsumerModules (args : List String) (profile : Bool) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let mut failed := false
  if profile then
    for name in args do
      try
        reportConsumerModule name (← replayConsumerModule name)
      catch error =>
        reportConsumerFailure name error
        failed := true
  else
    let tasks ← args.toArray.mapM fun name => do
      return (name, ← IO.asTask (replayConsumerModule name))
    for (name, task) in tasks do
      match task.get with
      | .ok elapsed => reportConsumerModule name elapsed
      | .error error =>
        reportConsumerFailure name error
        failed := true
  if failed then
    throw (IO.userError "Kernel replay rejected at least one consumer module")
""" + "\n#eval do\n  let json ← IO.FS.readFile (String.fromUTF8! (ByteArray.mk #[" +
                string.Join(",", System.Text.Encoding.UTF8.GetBytes(targetsPath)) +
                "]))\n  let args ← IO.ofExcept <| (Lean.Json.parse json).bind Lean.fromJson?\n  replayConsumerModules args " +
                profile.ToString().ToLowerInvariant() + "\n");
            // Unlike leanchecker, the lean frontend defaults to hardware
            // concurrency rather than honoring LEAN_NUM_THREADS itself.
            string[] command = [LeanExecutable, "-j" + threads, runner];
            var result = Execute(command, session, leanPath, progress: profile
                ? "Profiled kernel replay of consumer modules" : "Kernel replay of consumer proof and dependencies",
                environment: LeanEnvironment);
            var replayed = new HashSet<string>(StringComparer.Ordinal);
            var failures = new Dictionary<string, string>(StringComparer.Ordinal);
            foreach (var line in result.Stdout.Split('\n', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
            {
                if (!line.StartsWith('{')) continue;
                JsonElement record;
                try { record = JsonSerializer.Deserialize<JsonElement>(line); }
                catch (JsonException) { continue; }
                if (record.ValueKind != JsonValueKind.Object || !record.TryGetProperty("module", out var module) ||
                    module.ValueKind != JsonValueKind.String) continue;
                if (record.TryGetProperty("error", out var error)) failures[module.GetString()!] = error.ToString();
                else replayed.Add(module.GetString()!);
            }
            if ((result.Code == 0) != (failures.Count == 0) || replayed.Overlaps(failures.Keys) ||
                !targets.All(name => replayed.Contains(name) || failures.ContainsKey(name)))
                throw new InvalidOperationException($"Command failed ({result.Code}): {string.Join(' ', command)}\n{result.Output}");
            return failures;
        }
        finally { File.Delete(runner); File.Delete(targetsPath); }
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

    static SortedDictionary<string, string> ConsumerSnapshot(string root, string? output)
    {
        var inputs = new SortedDictionary<string, string>(StringComparer.Ordinal);
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

    static SortedDictionary<string, string> ConsumerInputs(string root, string proof, string? settings, string output)
    {
        var inputs = Inputs(proof, settings);
        foreach (var (key, value) in ConsumerSnapshot(root, output)) inputs[key] = value;
        return inputs;
    }

    static SortedDictionary<string, string> RequestInputs(SortedDictionary<string, string> common, string proof, string? settings)
    {
        var inputs = new SortedDictionary<string, string>(common, StringComparer.Ordinal);
        inputs["proof:" + proof] = Sha(proof);
        if (settings is not null) inputs["settings:" + settings] = Sha(settings);
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

    (string[] Directories, string LeanPath) ConsumerImportDirectories(string session)
    {
        // Ask the same Lake environment used by the checker. Package buildDir and
        // leanLibDir need not be the default .lake/build/lib/lean directories.
        var lines = Run(["lake", "env"], session).Split('\n', StringSplitOptions.TrimEntries)
            .Where(line => line.StartsWith("LEAN_PATH=", StringComparison.Ordinal)).ToArray();
        if (lines.Length != 1) throw new InvalidDataException("Could not resolve consumer Lean import paths.");
        var leanPath = lines[0]["LEAN_PATH=".Length..];
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        var trusted = Path.GetFullPath(Path.Combine(Toolchain, "lib/lean"));
        return (leanPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(path => Path.TrimEndingDirectorySeparator(Path.GetFullPath(path, session)))
            .Where(path => !path.Equals(trusted, comparison))
            .Select(path => Within(session, Path.GetRelativePath(session, path)))
            .Distinct(OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal).ToArray(), leanPath);
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
            var result = Run([LeanExecutable, "--run", probe, input], session, environment: LeanEnvironment);
            var lines = result.Split('\n', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
            if (lines.Length != paths.Length) throw new InvalidDataException("Incomplete consumer compiled import graph.");
            return modules.Keys.Zip(lines).ToDictionary(pair => pair.First,
                pair => JsonSerializer.Deserialize<string[]>(pair.Second) ?? throw new InvalidDataException("Invalid import graph."));
        }
        finally { File.Delete(probe); File.Delete(input); }
    }

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

    static HashSet<string> DependentModules(Dictionary<string, string[]> graph, IEnumerable<string> roots)
    {
        var dependent = new HashSet<string>(roots, StringComparer.Ordinal);
        bool changed;
        do
        {
            changed = false;
            foreach (var (name, imports) in graph)
                if (imports.Any(dependent.Contains)) changed |= dependent.Add(name);
        } while (changed);
        return dependent;
    }

    const string ConsumerSupportRecordName = "leancil-support.json";

    // Sources are package-relative paths of every candidate source file for the module.
    sealed record ConsumerSupportModule(SortedDictionary<string, string> Sources, string[] Imports, string[] Files);

    bool ExternalConsumerModule(string name) => name == "CIL" || name.StartsWith("CIL.", StringComparison.Ordinal) ||
        File.Exists(Path.Combine(Toolchain, "lib/lean", name.Replace('.', '/') + ".olean"));

    // Keep only modules whose candidate sources are unchanged and whose imports are
    // kept, certified framework modules or toolchain modules.
    HashSet<string> RestorableConsumerSupport(SortedDictionary<string, ConsumerSupportModule> record, IReadOnlyDictionary<string, string> sources)
    {
        var result = record.Where(pair => pair.Value.Sources.Count > 0 &&
                pair.Value.Sources.All(source => sources.TryGetValue(source.Key, out var hash) && hash == source.Value))
            .Select(pair => pair.Key).ToHashSet(StringComparer.Ordinal);
        bool changed;
        do
        {
            changed = false;
            foreach (var name in result.ToArray())
                if (record[name].Imports.Any(import => !result.Contains(import) && !ExternalConsumerModule(import)))
                    changed |= result.Remove(name);
        } while (changed);
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
    SortedDictionary<string, string> RestoreConsumerSupport(string key, IReadOnlyDictionary<string, string> sources, string destination)
    {
        if (!UseSuccessCache || !Directory.Exists(SuccessCacheRoot)) return new(StringComparer.Ordinal);
        var candidates = new List<(string Name, int Count, DateTime Time)>();
        foreach (var generation in Directory.EnumerateDirectories(SuccessCacheRoot, key + "-*"))
        {
            var name = Path.GetFileName(generation);
            // Staging and replaced entries carry a '.' suffix and are never restored.
            if (name.Contains('.')) continue;
            // Unauthenticated preselection only; the chosen generation is authenticated below.
            var record = ReadConsumerSupportRecord(Path.Combine(generation, "files", ConsumerSupportRecordName));
            var count = record is null ? 0 : RestorableConsumerSupport(record, sources).Count;
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
                var files = RestorableConsumerSupport(record, sources).SelectMany(module => record[module].Files)
                    .Select(file => (Source: Within(staging, file), Target: Within(destination, file))).ToArray();
                if (files.Any(file => !File.Exists(file.Source))) continue;
                foreach (var (source, target) in files)
                {
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(source, target, true);
                }
                return CacheFiles(destination);
            }
            catch (Exception error) when (error is InvalidDataException or IOException or UnauthorizedAccessException) { }
            finally { Directory.Delete(staging, true); }
        }
        return new(StringComparer.Ordinal);
    }

    // Collects certified, extraction-independent modules with their sources and
    // imports. Returns null when no module can be bound to its sources.
    string? CollectConsumerSupport(string session, Dictionary<string, string> modules, Dictionary<string, string[]> graph,
        HashSet<string> dependent, IReadOnlyDictionary<string, string> sources)
    {
        var generatedArtifacts = Directory.EnumerateFiles(session, "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(session, path).Replace('\\', '/'))
            .Where(relative => !relative.Split('/').Contains(".git") &&
                new[] { ".c", ".c.hash", ".ir", ".ir.hash", ".setup.json" }.Any(suffix => relative.EndsWith(suffix, StringComparison.Ordinal)))
            .ToArray();
        var record = new SortedDictionary<string, ConsumerSupportModule>(StringComparer.Ordinal);
        foreach (var (name, path) in modules.Where(pair => !dependent.Contains(pair.Key) &&
            pair.Key != "CIL" && !pair.Key.StartsWith("CIL.", StringComparison.Ordinal)))
        {
            var files = new SortedSet<string>(StringComparer.Ordinal);
            var stem = Path.GetFileNameWithoutExtension(path);
            foreach (var artifact in Directory.EnumerateFiles(Path.GetDirectoryName(path)!, stem + ".*"))
            {
                // A sibling module Foo.Bar must not be mistaken for Foo's artifact.
                var suffix = Path.GetFileName(artifact)[stem.Length..];
                if (suffix is ".olean" or ".olean.hash" or ".olean.private" or ".olean.private.hash" or
                    ".olean.server" or ".olean.server.hash" or ".ilean" or ".ilean.hash" or ".trace" or ".ir" or ".ir.hash")
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
            var candidates = sources.Where(pair => pair.Key[..^".lean".Length] == modulePath ||
                pair.Key[..^".lean".Length].EndsWith("/" + modulePath, StringComparison.Ordinal));
            record[name] = new(new(candidates.ToDictionary(), StringComparer.Ordinal),
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

    sealed record ConsumerSession(string FrameworkCopy, Dictionary<string, string> Copied);

    ConsumerSession PrepareConsumerSession(string session, string root, ConsumerDependency[] dependencies,
        SortedDictionary<string, string> snapshot, string certifiedLibrary, string extraction,
        IReadOnlyList<(string Module, string Proof, string Output)> proofs)
    {
        foreach (var dependency in dependencies)
        {
            var destination = Within(session, Path.GetRelativePath(root, dependency.Directory));
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            Run(["git", "clone", "--no-hardlinks", "--no-checkout", dependency.Directory, destination]);
            Run(["git", "remote", "set-url", "origin", dependency.Url], destination);
        }
        foreach (var (key, hash) in snapshot.Where(p => p.Key.StartsWith("consumer:", StringComparison.Ordinal)))
        {
            var source = key["consumer:".Length..];
            var destination = Within(session, Path.GetRelativePath(root, source));
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(source, destination);
            if (Sha(destination) != hash) throw new InvalidDataException("Consumer source changed during copying: " + source);
        }
        var framework = dependencies.Single(d => d.Name == "leancil");
        var frameworkCopy = Within(session, Path.GetRelativePath(root, framework.Source));
        // The snapshot already checked normalized source equality. Use the
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
        File.Copy(Path.Combine(extraction, "Extracted.lean"), Path.Combine(frameworkCopy, "Extracted.lean"));
        var generated = Sha(Path.Combine(frameworkCopy, "Extracted.lean"));
        foreach (var output in proofs.Select(proof => proof.Output).Distinct())
            if (generated != JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")))
                .GetProperty("generatedSha256").GetString())
                throw new InvalidDataException("Generated CIL changed during consumer snapshot.");
        AddConsumerLibrary(frameworkCopy, "Extracted");
        var extractionAuditPath = Path.Combine(frameworkCopy, "ExtractionAudit.lean");
        if (File.Exists(extractionAuditPath)) throw new InvalidDataException("ExtractionAudit is reserved for the certificate audit.");
        File.WriteAllText(extractionAuditPath, ExtractionAuditSource);
        AddConsumerLibrary(frameworkCopy, "ExtractionAudit");
        var copied = snapshot.Keys.Where(k => k.StartsWith("consumer:", StringComparison.Ordinal))
            .Select(k => Within(session, Path.GetRelativePath(root, k["consumer:".Length..])))
            .Append(Path.Combine(frameworkCopy, "Extracted.lean"))
            .Append(extractionAuditPath).ToList();
        foreach (var (module, proof, _) in proofs)
        {
            if (File.Exists(Path.Combine(session, module + ".lean")))
                throw new InvalidDataException(module + " is reserved for the selected proof.");
            File.Copy(Path.Combine(session, Path.GetRelativePath(root, proof)), Path.Combine(session, module + ".lean"));
            AddConsumerLibrary(session, module);
            copied.Add(Path.Combine(session, module + ".lean"));
        }
        return new(frameworkCopy, copied.ToDictionary(path => path, Sha));
    }

    sealed record ConsumerRequest(string Assembly, string Output, string Proof, string Theorem, string? Settings,
        bool ExpectRejection = false);

    sealed class ConsumerOutcome
    {
        public string Stage = "extraction integrity";
        public Report? Report;
        public Exception? Error;
        public bool Rejected;
        public string? Detail;
    }

    Report VerifyConsumer(string assembly, string proof, string output, string theorem, string root,
        string? settings, Action<string>? stage)
    {
        var outcome = VerifyConsumerRequests(root, [new(assembly, output, proof, theorem, settings)],
            (_, value) => stage?.Invoke(value), batch: false)[0];
        if (outcome.Error is not null) System.Runtime.ExceptionServices.ExceptionDispatchInfo.Throw(outcome.Error);
        return outcome.Report!;
    }

    // Verifies requests against one consumer snapshot. Each request gets its own
    // certificate, proof module, theorem audit and failure; requests that share an
    // extraction share one Lake workspace, build and kernel replay.
    ConsumerOutcome[] VerifyConsumerRequests(string root, IReadOnlyList<ConsumerRequest> requests,
        Action<int, string>? stage, bool batch, int parallelism = 1)
    {
        root = Path.GetFullPath(root);
        var outcomes = requests.Select(_ => new ConsumerOutcome()).ToArray();
        bool Live(int i) => outcomes[i].Error is null && !outcomes[i].Rejected && outcomes[i].Report is null;
        int[] Pending(IEnumerable<int> members) => members.Where(Live).ToArray();
        void Stage(IEnumerable<int> members, string value)
        {
            foreach (var i in Pending(members))
            {
                outcomes[i].Stage = value;
                stage?.Invoke(i, value);
            }
        }
        void Fail(IEnumerable<int> members, Exception error)
        {
            foreach (var i in Pending(members)) outcomes[i].Error = error;
        }
        var comparer = OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;
        var all = Enumerable.Range(0, requests.Count).ToArray();
        var identities = new string[requests.Count];
        var proofKeys = new string[requests.Count];
        var outputs = requests.Select(request => Path.GetFullPath(request.Output)).ToArray();
        var proofs = new string[requests.Count];
        foreach (var i in all)
            try { proofs[i] = Within(root, Path.GetRelativePath(root, Path.GetFullPath(requests[i].Proof))); }
            catch (Exception error) { Fail([i], error); }
        // Only the last request for an output may leave a certificate, as in sequential runs.
        var last = all.GroupBy(i => outputs[i], comparer).ToDictionary(group => group.Key, group => group.Max(), comparer);
        foreach (var output in last.Keys) File.Delete(Path.Combine(output, "verified.json"));
        var parallel = new ParallelOptions { MaxDegreeOfParallelism = Math.Max(1, parallelism) };
        void CheckExtractions(int[] members)
        {
            Stage(members, "extraction integrity");
            Parallel.ForEach(Pending(members).GroupBy(i => outputs[i], comparer), parallel, group =>
            {
                try { Run(["dotnet", ExtractorPath, "check", group.Key]); }
                catch (Exception error) { Fail(group, error); }
            });
        }
        CheckExtractions(all);
        if (batch && !string.IsNullOrWhiteSpace(Environment.GetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT")))
            Fail(all, new InvalidOperationException("LEANCIL_EXPORT_CONSUMER_SUPPORT requires a single-request verify."));
        var live = Pending(all);
        if (live.Length == 0) return outcomes;

        // A batch shares one snapshot, so no output may be part of the consumer sources.
        string? excluded = batch ? null : outputs[live[0]];
        SortedDictionary<string, string> Common(SortedDictionary<string, string> snapshot)
        {
            var common = new SortedDictionary<string, string>(Inputs(At("CIL.lean")).Where(pair =>
                !pair.Key.StartsWith("proof:", StringComparison.Ordinal) && !pair.Key.StartsWith("settings:", StringComparison.Ordinal))
                .ToDictionary(), StringComparer.Ordinal);
            foreach (var (key, value) in snapshot) common[key] = value;
            return common;
        }
        var before = new SortedDictionary<string, string>[requests.Count];
        SortedDictionary<string, string> snapshot;
        Stage(live, "consumer source snapshot");
        try
        {
            snapshot = ConsumerSnapshot(root, excluded);
            var common = Common(snapshot);
            foreach (var i in live)
                try
                {
                    var output = outputs[i] + Path.DirectorySeparatorChar;
                    if (batch && snapshot.Keys.Any(key => key.StartsWith("consumer:" + output, OperatingSystem.IsWindows()
                        ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal)))
                        throw new InvalidDataException("Batch outputs must lie outside the consumer sources, for example under artifacts/: " + outputs[i]);
                    before[i] = RequestInputs(common, proofs[i], requests[i].Settings);
                    if (!before[i].ContainsKey("consumer:" + proofs[i]))
                        throw new InvalidDataException("Proof must be a Lean source under the consumer root, outside excluded build/artifact directories.");
                }
                catch (Exception error) { Fail([i], error); }
        }
        catch (Exception error)
        {
            Fail(live, error);
            return outcomes;
        }
        void Recheck(int[] members)
        {
            CheckExtractions(members);
            members = Pending(members);
            if (members.Length == 0) return;
            try
            {
                var common = Common(ConsumerSnapshot(root, excluded));
                foreach (var i in members)
                    if (!Same(before[i], RequestInputs(common, proofs[i], requests[i].Settings)) ||
                        identities[i] != Sha(Path.Combine(outputs[i], "identity.json")))
                        Fail([i], new InvalidOperationException("Inputs changed during consumer verification"));
            }
            catch (Exception error) { Fail(members, error); }
        }

        live = Pending(all);
        if (live.Length == 0) return outcomes;
        Stage(live, "Lean library build");
        string certifiedLibrary;
        Dictionary<string, string> certifiedBase;
        ConsumerDependency[] dependencies;
        try
        {
            certifiedLibrary = Library(Inputs(proofs[live[0]], requests[live[0]].Settings));
            certifiedBase = ModuleArtifacts(certifiedLibrary).Where(pair =>
                ModuleName(pair.Key) == "CIL" || ModuleName(pair.Key).StartsWith("CIL.", StringComparison.Ordinal)).ToDictionary();
            dependencies = ConsumerDependencies(root);
            // Resolve lazily initialized identities before any parallel work.
            _ = VerificationPolicy;
            if (UseSuccessCache) _ = ReceiptKey;
        }
        catch (Exception error)
        {
            Fail(live, error);
            return outcomes;
        }
        var cached = new List<int>();
        foreach (var i in live)
        {
            try
            {
                identities[i] = Sha(Path.Combine(outputs[i], "identity.json"));
                proofKeys[i] = ConsumerCacheKey("proof", before[i], identities[i] + "\n" + requests[i].Theorem + "\n" + Sha(requests[i].Assembly));
                if (requests[i].ExpectRejection) continue;
                var receipt = Path.Combine(Path.GetTempPath(), "leancil-consumer-receipt-" + Guid.NewGuid().ToString("N"));
                Directory.CreateDirectory(receipt);
                try
                {
                    if (!RestoreSuccess(proofKeys[i], receipt)) continue;
                    var report = JsonSerializer.Deserialize<Report>(File.ReadAllText(Path.Combine(receipt, "report.json")))!;
                    outcomes[i].Detail = JsonSerializer.Serialize(report with { libraryBuild = "consumer-proof-cache" }, Json);
                    cached.Add(i);
                }
                finally { Directory.Delete(receipt, true); }
            }
            catch (Exception error) { Fail([i], error); }
        }
        if (cached.Count > 0)
        {
            // An unchanged proof reuses its authenticated result; integrity and inputs are still rechecked.
            Recheck([.. cached]);
            foreach (var i in Pending(cached))
            {
                var report = JsonSerializer.Deserialize<Report>(outcomes[i].Detail!)!;
                outcomes[i].Detail = null;
                if (last[outputs[i]] == i) File.WriteAllText(Path.Combine(outputs[i], "verified.json"), JsonSerializer.Serialize(report, Json) + "\n");
                outcomes[i].Report = report;
                CacheProgress("certified consumer proof: " + requests[i].Theorem);
            }
        }

        var groups = new Dictionary<string, List<int>>(StringComparer.Ordinal);
        foreach (var i in Pending(all))
            try
            {
                var key = Sha(Path.Combine(outputs[i], "Extracted.lean"));
                if (!groups.TryGetValue(key, out var members)) groups[key] = members = [];
                members.Add(i);
            }
            catch (Exception error) { Fail([i], error); }
        if (groups.Count == 0) return outcomes;
        var ordered = groups.Values.Select(group => group.ToArray())
            .OrderByDescending(group => group.Count(i => !requests[i].ExpectRejection)).ToArray();
        var sources = ConsumerSourceHashes(snapshot, root);
        var exporting = !string.IsNullOrWhiteSpace(Environment.GetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT"));
        string supportKey = "";
        string[] relativeImportDirectories = [];
        // Certified extraction-independent support shared by later workspaces.
        var support = Path.Combine(Path.GetTempPath(), "leancil-consumer-restored-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(support);
        var supportArtifacts = new SortedDictionary<string, string>(StringComparer.Ordinal);

        void VerifyGroup(int[] members, string session, bool first, bool share)
        {
            var names = members.Length == 1 ? ["LeanCILProof"] : members.Select((_, k) => "LeanCILProof" + k).ToArray();
            var prepared = PrepareConsumerSession(session, root, dependencies, snapshot, certifiedLibrary, outputs[members[0]],
                members.Select((i, k) => (names[k], proofs[i], outputs[i])).ToArray());
            var frameworkCopy = prepared.FrameworkCopy;
            string[] initialImportDirectories;
            if (!first && relativeImportDirectories.Length > 0)
                initialImportDirectories = relativeImportDirectories.Select(path => Path.GetFullPath(path, session)).ToArray();
            else if (!first)
                initialImportDirectories = ConsumerImportDirectories(session).Directories;
            else
            {
                initialImportDirectories = ConsumerImportDirectories(session).Directories;
                relativeImportDirectories = initialImportDirectories.Select(path => Path.GetRelativePath(session, path)).ToArray();
                // Lean sources are bound per module inside each generation, not by this key.
                var configuration = prepared.Copied.Where(pair => Path.GetFileName(pair.Key) is "lakefile.toml" or "lakefile.lean" or "lake-manifest.json" or "lean-toolchain")
                    .OrderBy(pair => pair.Key, StringComparer.Ordinal)
                    .Select(pair => Path.GetRelativePath(session, pair.Key).Replace('\\', '/') + ":" + pair.Value);
                supportKey = ConsumerCacheKey("support", new(snapshot.Where(pair => pair.Key.StartsWith("revision:", StringComparison.Ordinal))
                        .ToDictionary(), StringComparer.Ordinal),
                    string.Join("\n", relativeImportDirectories) + "\n" + string.Join("\n", configuration));
                supportArtifacts = RestoreConsumerSupport(supportKey, sources, support);
            }
            var restoredArtifacts = new SortedDictionary<string, string>(supportArtifacts.Where(pair => pair.Key != ConsumerSupportRecordName)
                .ToDictionary(), StringComparer.Ordinal);
            foreach (var file in restoredArtifacts.Keys)
            {
                var target = Within(session, file);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Within(support, file), target, true);
            }
            if (restoredArtifacts.Count > 0) CacheProgress("certified consumer support library");
            // Snapshot before invoking Lake: configuration elaboration and imported
            // metaprograms must not redefine the source bytes accepted by this run.
            Stage(members, "extraction certificate audit");
            var extractionAudit = Run(["lake", "build", "+ExtractionAudit:olean"], frameworkCopy,
                progress: "Checking consumer extraction certificate");
            AuditedAxioms(extractionAudit, "ExtractionAudit.valid");
            Stage(members, "proof checking");
            string[] command = ["lake", "build", .. names.Select(name => "+" + name + ":olean")];
            var build = Execute(command, session, progress: "Building fresh consumer proof and dependencies");
            var buildFailure = build.Code == 0 ? null
                : new InvalidOperationException($"Command failed ({build.Code}): {string.Join(' ', command)}\n{build.Output}");
            string[] importDirectories = [];
            var leanPath = "";
            bool[] built = [false];
            if (buildFailure is null || members.Length > 1)
            {
                if (members.Length == 1) Stage(members, "kernel replay");
                (importDirectories, leanPath) = ConsumerImportDirectories(session);
                // Lake writes a module's olean and trace only after it checks successfully.
                built = names.Select(name => importDirectories.Any(directory =>
                    File.Exists(Path.Combine(directory, name + ".olean")) && File.Exists(Path.Combine(directory, name + ".trace")))).ToArray();
                if (buildFailure is null && !built.All(value => value))
                    throw new InvalidDataException("Consumer proof or certificate is missing from the resolved import paths.");
            }
            var rejecting = new List<int>();
            for (var k = 0; k < members.Length; k++)
            {
                var i = members[k];
                if (!built[k])
                {
                    if (requests[i].ExpectRejection) rejecting.Add(i);
                    else Fail([i], buildFailure!);
                }
                else if (requests[i].ExpectRejection)
                    Fail([i], new InvalidOperationException("Expected proof checking to reject " + requests[i].Theorem + ", but the proof checked."));
            }
            if (rejecting.Count > 0)
            {
                // A rejection counts only for unchanged inputs and an intact extraction.
                Recheck([.. rejecting]);
                foreach (var i in Pending(rejecting))
                {
                    outcomes[i].Stage = "proof checking";
                    outcomes[i].Detail = buildFailure!.Message;
                    outcomes[i].Rejected = true;
                }
            }
            var proceeding = Pending(members);
            if (proceeding.Length == 0) return;
            Stage(proceeding, "kernel replay");
            // Replay every consumer/external module, including unused declarations.
            // Only identical artifacts in the validated framework package can reuse
            // the base certificate; a same-named consumer module cannot inherit it.
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
            var moduleNames = new HashSet<string>(StringComparer.Ordinal);
            var discovered = new List<(string Name, bool Certified)>();
            foreach (var directory in importDirectories)
            {
                if (!Directory.Exists(directory)) continue;
                var artifacts = Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
                    .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
                    .Select(path => new KeyValuePair<string, string>(Path.GetRelativePath(directory, path).Replace('\\', '/'), Sha(path)));
                foreach (var module in artifacts.GroupBy(pair => ModuleName(pair.Key)))
                {
                    if (!moduleNames.Add(module.Key)) throw new InvalidDataException("Ambiguous consumer module: " + module.Key);
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
            if (!moduleNames.Contains("Extracted") || !moduleNames.Contains("ExtractionAudit") ||
                proceeding.Any(i => !moduleNames.Contains(names[Array.IndexOf(members, i)])))
                throw new InvalidDataException("Consumer proof or certificate is missing from the resolved import paths.");
            var currentArtifacts = importDirectories.Where(Directory.Exists).SelectMany(directory =>
                Directory.EnumerateFiles(directory, "*.olean", SearchOption.AllDirectories).Select(path =>
                    (Name: ModuleName(Path.GetRelativePath(directory, path).Replace('\\', '/')), Path: path)))
                .ToDictionary(pair => pair.Name, pair => pair.Path, StringComparer.Ordinal);
            var checkedArtifacts = JsonSerializer.Serialize(currentArtifacts.OrderBy(pair => pair.Key, StringComparer.Ordinal)
                .ToDictionary(pair => pair.Key, pair => ConsumerModuleParts(pair.Value)));
            var portableSupport = ImportedConsumerSupport(session, root, before[proceeding[0]], currentArtifacts);
            var graph = members.Length > 1 || share || UseSuccessCache || exporting ? ConsumerModuleImports(session, currentArtifacts) : null;
            var failures = ReplayConsumerModules(session, discovered.Where(module => !baseUnchanged ||
                (!module.Certified && !portableSupport.Contains(module.Name))).Select(module => module.Name), leanPath);
            foreach (var i in proceeding)
            {
                // A request depends only on its own proof's import closure and the extraction certificate.
                var closure = graph is null ? null
                    : ImportClosure(graph, [names[Array.IndexOf(members, i)], "Extracted", "ExtractionAudit"]);
                var rejected = failures.Keys.Where(name => closure is null || closure.Contains(name)).Order(StringComparer.Ordinal).ToArray();
                if (rejected.Length > 0)
                    Fail([i], new InvalidOperationException("Kernel replay rejected " + string.Join(", ", rejected) + ":\n" +
                        string.Join("\n", rejected.Select(name => failures[name]))));
            }
            proceeding = Pending(proceeding);
            if (proceeding.Length == 0) return;
            Stage(proceeding, "theorem audit");
            var audits = new Dictionary<int, (string Audit, string[] Axioms)>();
            foreach (var i in proceeding)
            {
                try
                {
                    var theorem = requests[i].Theorem;
                    var module = names[Array.IndexOf(members, i)];
                    var auditPath = Path.Combine(session, "LeanCILAudit" + module["LeanCILProof".Length..] + ".lean");
                    File.WriteAllText(auditPath, $"import {module}\nrun_cmd do\n  match (← Lean.getEnv).find? `{theorem} with\n  | some (.thmInfo _) => pure ()\n  | _ => throwError \"Expected a theorem\"\n#check {theorem}\n#print axioms {theorem}\n");
                    var audit = Run([LeanExecutable, auditPath], session, leanPath, environment: LeanEnvironment);
                    var matches = Regex.Matches(audit, "'" + Regex.Escape(theorem) + @"' depends on axioms:\s*\[([^\]]*)\]");
                    if (matches.Count > 1 || (matches.Count == 0 && !audit.Contains($"'{theorem}' does not depend on any axioms")))
                        throw new InvalidOperationException("Missing or ambiguous transitive theorem axiom audit");
                    string[] axioms = matches.Count == 0 ? [] : matches[0].Groups[1].Value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
                    if (axioms.Any(a => a is not ("propext" or "Quot.sound" or "Classical.choice")))
                        throw new InvalidOperationException("Unapproved proof axioms: " + string.Join(", ", axioms));
                    audits[i] = (audit, axioms);
                }
                catch (Exception error) { Fail([i], error); }
            }
            proceeding = Pending(proceeding);
            if (proceeding.Length == 0) return;
            Recheck(proceeding);
            proceeding = Pending(proceeding);
            if (proceeding.Length == 0) return;
            if (prepared.Copied.Any(pair => !File.Exists(pair.Key) || Sha(pair.Key) != pair.Value))
                throw new InvalidOperationException("Sources changed in the fresh consumer build");
            var finalArtifacts = importDirectories.Where(Directory.Exists).SelectMany(directory =>
                Directory.EnumerateFiles(directory, "*.olean", SearchOption.AllDirectories).Select(path =>
                    (Name: ModuleName(Path.GetRelativePath(directory, path).Replace('\\', '/')), Path: path)))
                .OrderBy(pair => pair.Name, StringComparer.Ordinal)
                .ToDictionary(pair => pair.Name, pair => ConsumerModuleParts(pair.Path));
            if (checkedArtifacts != JsonSerializer.Serialize(finalArtifacts))
                throw new InvalidOperationException("Compiled artifacts changed during consumer verification");
            // Publish only after the complete declaration replay, exact theorem
            // audit, extraction recheck and source-stability checks succeeded.
            if (failures.Count == 0 && graph is not null)
            {
                var dependent = DependentModules(graph, ["Extracted", "ExtractionAudit", .. names]);
                if (exporting)
                    ExportConsumerSupport(session, root, before[proceeding[0]],
                        currentArtifacts.Where(pair => !dependent.Contains(pair.Key)).ToDictionary(), graph);
                if (UseSuccessCache || share)
                {
                    var collected = CollectConsumerSupport(session, currentArtifacts, graph, dependent, sources);
                    if (collected is not null)
                    {
                        try
                        {
                            if (supportKey.Length > 0)
                                PublishSuccess(supportKey + "-" + Sha(Path.Combine(collected, ConsumerSupportRecordName)), collected);
                            if (share)
                            {
                                Directory.Delete(support, true);
                                Directory.Move(collected, support);
                                supportArtifacts = CacheFiles(support);
                            }
                        }
                        finally { if (Directory.Exists(collected)) Directory.Delete(collected, true); }
                    }
                }
            }
            foreach (var i in proceeding)
            {
                var extraction = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(outputs[i], "identity.json")));
                var initializedTypes = extraction.TryGetProperty("initializedTypes", out var assumptions)
                    ? assumptions.Deserialize<string[]>() : [];
                var report = new Report(3, Sha(requests[i].Assembly), identities[i], requests[i].Theorem, audits[i].Axioms,
                    audits[i].Audit, before[i], libraryKey, "consumer-" + libraryBuild, extractionAudit, initializedTypes,
                    consumerSupportSha256: baseUnchanged && portableSupport.Count > 0
                        ? Environment.GetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256") : null);
                var receipt = Path.Combine(session, "certified-result-" + i);
                Directory.CreateDirectory(receipt);
                File.WriteAllText(Path.Combine(receipt, "report.json"), JsonSerializer.Serialize(report, Json));
                PublishSuccess(proofKeys[i], receipt);
                if (last[outputs[i]] == i) File.WriteAllText(Path.Combine(outputs[i], "verified.json"), JsonSerializer.Serialize(report, Json) + "\n");
                outcomes[i].Report = report;
            }
        }

        void RunGroup(int[] members, bool first, bool share)
        {
            var session = Path.Combine(Path.GetTempPath(), "leancil-consumer-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(session);
            try { VerifyGroup(members, session, first, share); }
            catch (Exception error) { Fail(members, error); }
            finally { Directory.Delete(session, true); }
        }

        try
        {
            // The first workspace certifies shared support before later ones start.
            RunGroup(ordered[0], first: true, share: ordered.Length > 1);
            Parallel.ForEach(ordered.Skip(1), parallel, group => RunGroup(group, first: false, share: false));
        }
        finally { Directory.Delete(support, true); }
        return outcomes;
    }
}
