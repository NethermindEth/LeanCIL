using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
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
        var session = Path.Combine(Path.GetTempPath(), "leancil-consumer-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(session);
        try
        {
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
            var proofModule = "LeanCILProof" + Guid.NewGuid().ToString("N");
            File.Copy(Path.Combine(session, Path.GetRelativePath(root, proof)), Path.Combine(session, proofModule + ".lean"));
            AddConsumerLibrary(session, proofModule);
            var copied = before.Keys.Where(k => k.StartsWith("consumer:", StringComparison.Ordinal))
                .Select(k => Within(session, Path.GetRelativePath(root, k["consumer:".Length..])))
                .Append(Path.Combine(frameworkCopy, "Extracted.lean"))
                .Append(extractionAuditPath)
                .Append(Path.Combine(session, proofModule + ".lean"))
                .ToDictionary(path => path, Sha);
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
            var checker = Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
            var importDirectories = ConsumerImportDirectories(session);
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
                    discovered.Add((module.Key, unchanged));
                }
            }
            if (!names.Contains(proofModule) || !names.Contains("Extracted") || !names.Contains("ExtractionAudit"))
                throw new InvalidDataException("Consumer proof or certificate is missing from the resolved import paths.");
            var modules = discovered.Where(module => !baseUnchanged || !module.Certified).Select(module => module.Name);
            Run(["lake", "env", checker, .. modules], session, progress: "Kernel replay of consumer proof and dependencies");
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
            var initializedTypes = extraction.TryGetProperty("initializedTypes", out var assumptions)
                ? assumptions.Deserialize<string[]>() : [];
            var report = new Report(3, Sha(assembly), identityHash, theorem, axioms, audit, before,
                libraryKey, "consumer-" + libraryBuild, extractionAudit, initializedTypes);
            File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");
            return report;
        }
        finally { Directory.Delete(session, true); }
    }
}
