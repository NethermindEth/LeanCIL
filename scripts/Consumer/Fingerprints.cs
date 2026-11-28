using System.Text.Json;
using System.Text.RegularExpressions;

// Certified consumer module fingerprints and support-cache manifests.
partial class Program
{
    // Files maps each module to its session-relative compiled artifacts and their hashes.
    sealed record ConsumerSupportManifest(int Schema, string Policy, string Library, string Toolchain,
        SortedDictionary<string, string> Sources, SortedDictionary<string, SortedDictionary<string, string>> Modules,
        SortedDictionary<string, string[]> Imports, string Tools,
        SortedDictionary<string, SortedDictionary<string, string>> Files);

    const string RestoreConsumerSupportVariable = "LEANCIL_RESTORE_CONSUMER_SUPPORT";

    static SortedDictionary<string, string> PortableConsumerSources(string root, SortedDictionary<string, string> inputs) =>
        new(inputs.Where(pair => !pair.Key.StartsWith("proof:", StringComparison.Ordinal) &&
                !pair.Key.StartsWith("settings:", StringComparison.Ordinal))
            .ToDictionary(pair => pair.Key.StartsWith("consumer:", StringComparison.Ordinal)
                ? "consumer:" + Path.GetRelativePath(root, pair.Key[9..]).Replace('\\', '/') : pair.Key, pair => pair.Value), StringComparer.Ordinal);

    /// <summary>
    /// The toolchain release, by its elan name: a release fixes its compiled modules, so portable
    /// support records match across machines and platforms of that release.
    /// </summary>
    string ConsumerToolchainIdentity() =>
        ContentKey("toolchain-release-v1\n" + Path.GetFileName(Path.TrimEndingDirectorySeparator(Toolchain)));

    static SortedDictionary<string, string> ConsumerModuleParts(string path)
    {
        var parts = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var suffix in new[] { "", ".server", ".private" })
            if (File.Exists(path + suffix)) parts[".olean" + suffix] = Sha(path + suffix);
        return parts;
    }

    // Normalization reads module parts directly, without importing toolchain oleans. The toolchain
    // release, platform and lean executable fix its native runtime; the auditor hash fixes the normalizer.
    string CanonicalFingerprintTools(string executableHash) =>
        ContentKey("canonical-fingerprints-v3\n" +
            System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier + "\n" +
            Path.GetFileName(Path.TrimEndingDirectorySeparator(Toolchain)) + "\n" +
            Sha(LeanExecutable) + "\n" + executableHash);

    sealed record CertifiedFingerprintModule(SortedDictionary<string, string> Raw,
        SortedDictionary<string, string> Canonical);
    sealed record CertifiedFingerprintManifest(int Schema, string Tools,
        SortedDictionary<string, CertifiedFingerprintModule> Modules);

    // The outer certified-library manifest authenticates this transformation table alongside
    // its sources, toolchain and compiled artifacts. It does not authorize consumer proofs.
    void PrepareCertifiedFingerprints()
    {
        if (session is not null && !ownsLibrary)
            throw new InvalidOperationException("Fingerprint metadata must be written before the library is opened in place.");
        Library(Inputs(At("CIL.lean")), writes: true);
        var certified = library!;
        var executable = CheckedAuditExecutable();
        var tools = CanonicalFingerprintTools(auditExecutableSha!);
        var modules = certifiedModules!.Keys.Where(path => path.EndsWith(".olean", StringComparison.Ordinal))
            .ToDictionary(ModuleName, path => Path.Combine(certified, ".lake/build/lib/lean", path),
                StringComparer.Ordinal);
        var raw = modules.ToDictionary(pair => pair.Key, pair => ConsumerModuleParts(pair.Value),
            StringComparer.Ordinal);
        var reused = CertifiedFingerprintParts(modules, tools);
        var pending = modules.Where(pair => !reused.ContainsKey(pair.Key))
            .ToDictionary(StringComparer.Ordinal);
        var normalized = pending.Count == 0
            ? new Dictionary<string, SortedDictionary<string, string>>(StringComparer.Ordinal)
            : NormalizeConsumerParts(certified, executable, pending);
        foreach (var (name, fingerprint) in reused) normalized.Add(name, fingerprint.Canonical);
        RequireCertifiedFingerprints(reused, modules, tools);
        CheckedAuditExecutable();
        if (tools != CanonicalFingerprintTools(auditExecutableSha!) || modules.Any(pair =>
                !Same(raw[pair.Key], ConsumerModuleParts(pair.Value))))
            throw new InvalidDataException("Certified library fingerprint inputs changed during normalization.");
        var manifest = new CertifiedFingerprintManifest(1, tools,
            new(modules.Keys.ToDictionary(name => name,
                name => new CertifiedFingerprintModule(raw[name], normalized[name])), StringComparer.Ordinal));
        var path = Path.Combine(certified, CertifiedFingerprintsName);
        var json = JsonSerializer.Serialize(manifest);
        File.WriteAllText(path, json);
        certifiedFingerprintsSha = ContentKey(json);
        Console.WriteLine($"Prepared canonical fingerprints for {modules.Count} certified library modules " +
            $"({reused.Count} reused, {pending.Count} serialized).");
    }

    // A matching name is insufficient: every module part and the actual normalizer must
    // match the authenticated producer's input before its canonical bytes can be reused.
    Dictionary<string, CertifiedFingerprintModule> CertifiedFingerprintParts(
        Dictionary<string, string> modules, string tools)
    {
        if (certifiedFingerprintsSha is null || library is null) return new(StringComparer.Ordinal);
        var path = Path.Combine(library, CertifiedFingerprintsName);
        var bytes = File.ReadAllBytes(path);
        if (Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes)) != certifiedFingerprintsSha)
            throw new InvalidDataException("Certified library fingerprint metadata changed.");
        var manifest = JsonSerializer.Deserialize<CertifiedFingerprintManifest>(bytes);
        if (manifest is null || manifest.Schema != 1 || manifest.Tools != tools)
            return new(StringComparer.Ordinal);
        if (manifest.Modules is null || manifest.Modules.Values.Any(module => module is null ||
                module.Raw is null || module.Canonical is null || !module.Raw.ContainsKey(".olean") ||
                !module.Raw.Keys.SequenceEqual(module.Canonical.Keys) || module.Raw.Keys.Any(part =>
                    part is not (".olean" or ".olean.server" or ".olean.private")) ||
                module.Raw.Values.Concat(module.Canonical.Values).Any(hash => !Regex.IsMatch(hash, "^[0-9a-f]{64}$"))))
            throw new InvalidDataException("Invalid certified library fingerprint metadata.");
        return modules.Where(pair => manifest.Modules.TryGetValue(pair.Key, out var fingerprint) &&
                Same(fingerprint.Raw, ConsumerModuleParts(pair.Value)))
            .ToDictionary(pair => pair.Key, pair => manifest.Modules[pair.Key], StringComparer.Ordinal);
    }

    void RequireCertifiedFingerprints(Dictionary<string, CertifiedFingerprintModule> reused,
        Dictionary<string, string> modules, string tools)
    {
        if (reused.Count == 0) return;
        CheckedAuditExecutable();
        if (tools != CanonicalFingerprintTools(auditExecutableSha!) ||
            Sha(Path.Combine(library!, CertifiedFingerprintsName)) != certifiedFingerprintsSha ||
            reused.Any(pair => !Same(pair.Value.Raw, ConsumerModuleParts(modules[pair.Key]))))
            throw new InvalidDataException("Certified library fingerprint inputs changed during normalization.");
    }

    sealed record FingerprintInput(string Name, string Source, SortedDictionary<string, string> Parts, string Key);

    SortedDictionary<string, string>? RestoreConsumerFingerprint(string key, string directory,
        SortedDictionary<string, string> raw)
    {
        if (!RestoreSuccess(key, directory)) return null;
        try
        {
            var parts = JsonSerializer.Deserialize<SortedDictionary<string, string>>(
                File.ReadAllText(Path.Combine(directory, "fingerprints.json")));
            if (parts is null || !parts.Keys.SequenceEqual(raw.Keys) ||
                !parts.Values.All(value => Regex.IsMatch(value, "^[0-9a-f]{64}$"))) return null;
            TouchEntry(Path.Combine(SuccessCacheRoot, key));
            return parts;
        }
        catch (Exception error) when (error is IOException or JsonException) { return null; }
    }

    // Remove only persisted linter diagnostics; declarations, strings and every other
    // environment extension are serialized unchanged, in the original module-part order.
    static Dictionary<string, SortedDictionary<string, string>> NormalizeConsumerParts(
        string session, string executable, Dictionary<string, string> modules)
    {
        if (modules.Count == 0) return new(StringComparer.Ordinal);
        var temporary = Path.Combine(Path.GetTempPath(), "leancil-normalize-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(temporary);
        try
        {
            var paths = modules.Select((pair, index) => (Name: pair.Key, Source: pair.Value,
                Destination: Path.Combine(temporary, index + ".olean"),
                Suffixes: new[] { "", ".server", ".private" }
                    .Where(suffix => File.Exists(pair.Value + suffix)).ToArray())).ToArray();
            if (paths.Any(item => !item.Suffixes.Contains("")))
                throw new InvalidDataException("Missing module fingerprint input.");
            var input = Path.Combine(temporary, "modules.json");
            File.WriteAllText(input, JsonSerializer.Serialize(paths.Select(item => new object[]
            {
                item.Name,
                new object[]
                {
                    item.Suffixes.Select(suffix => item.Source + suffix).ToArray(),
                    item.Suffixes.Select(suffix => item.Destination + suffix).ToArray()
                }
            })));
            Run([executable, "--fingerprints", input], session,
                progress: "Fingerprinting portable consumer modules");
            return paths.ToDictionary(item => item.Name, item =>
            {
                var parts = ConsumerModuleParts(item.Destination);
                if (!parts.Keys.ToHashSet(StringComparer.Ordinal)
                        .SetEquals(item.Suffixes.Select(suffix => ".olean" + suffix)))
                    throw new InvalidDataException("Incomplete normalized module parts: " + item.Name);
                return parts;
            }, StringComparer.Ordinal);
        }
        finally { Directory.Delete(temporary, true); }
    }

    static void TraceConsumerFingerprints(string session, DateTimeOffset started, TimeSpan elapsed,
        int reused, int serialized)
    {
        CacheProgress($"canonical module fingerprints ({reused} reused, {serialized} serialized)");
        Trace("Canonical module fingerprints", started, session, elapsed, 0, "",
            ["reused", reused.ToString(), "serialized", serialized.ToString(),
                "normalization-processes", serialized > 0 ? "1" : "0"]);
    }

    // Receipts reuse only the linter-stripped byte transformation. Source/import binding,
    // certificate eligibility and replay remain the callers' independent obligations.
    Dictionary<string, SortedDictionary<string, string>> PortableConsumerModuleParts(
        string session, Dictionary<string, string> modules, bool publishReceipts = true)
    {
        var started = DateTimeOffset.UtcNow;
        var elapsed = System.Diagnostics.Stopwatch.StartNew();
        var executable = CheckedAuditExecutable();
        var canonicalTools = UseSuccessCache || certifiedFingerprintsSha is not null
            ? CanonicalFingerprintTools(auditExecutableSha!) : "";
        var certified = CertifiedFingerprintParts(modules, canonicalTools);
        var pending = modules.Where(pair => !certified.ContainsKey(pair.Key)).ToDictionary(StringComparer.Ordinal);
        if (!UseSuccessCache || modules.Count == 0)
        {
            var normalized = NormalizeConsumerParts(session, executable, pending);
            RequireCertifiedFingerprints(certified, modules, canonicalTools);
            foreach (var (name, fingerprint) in certified) normalized.Add(name, fingerprint.Canonical);
            TraceConsumerFingerprints(session, started, elapsed.Elapsed, certified.Count, pending.Count);
            return normalized;
        }
        // Local receipts also bind this verifier binary; the supplied base independently
        // authenticates its transformation table through its trusted manifest digest.
        var tools = ContentKey(VerificationPolicy + "\n" + canonicalTools);
        var inputs = pending.Select(pair =>
        {
            var parts = ConsumerModuleParts(pair.Value);
            if (!parts.ContainsKey(".olean")) throw new InvalidDataException("Missing module: " + pair.Key);
            var key = ContentKey(tools + "\n" + pair.Key) + "-" + ContentKey(JsonSerializer.Serialize(parts));
            return new FingerprintInput(pair.Key, pair.Value, parts, key);
        }).ToArray();
        var temporary = Path.Combine(Path.GetTempPath(), "leancil-fingerprints-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(temporary);
        try
        {
            var results = certified.ToDictionary(pair => pair.Key, pair => pair.Value.Canonical,
                StringComparer.Ordinal);
            var missing = new List<(FingerprintInput Input, string Source, string Receipt)>();
            foreach (var (item, index) in inputs.Select((item, index) => (item, index)))
            {
                var receipt = Path.Combine(temporary, "receipts", index.ToString());
                if (RestoreConsumerFingerprint(item.Key, receipt, item.Parts) is { } restored)
                {
                    results.Add(item.Name, restored);
                    continue;
                }
                var source = Path.Combine(temporary, index + ".input.olean");
                foreach (var (part, hash) in item.Parts)
                {
                    var suffix = part[".olean".Length..];
                    File.Copy(item.Source + suffix, source + suffix);
                    if (Sha(source + suffix) != hash)
                        throw new InvalidDataException("Module changed while copying fingerprint inputs: " + item.Name);
                }
                missing.Add((item, source, receipt));
            }
            if (missing.Count > 0)
            {
                var normalized = NormalizeConsumerParts(session, executable,
                    missing.ToDictionary(item => item.Input.Name, item => item.Source, StringComparer.Ordinal));
                foreach (var item in missing)
                {
                    var parts = normalized[item.Input.Name];
                    if (!parts.Keys.SequenceEqual(item.Input.Parts.Keys))
                        throw new InvalidDataException("Incomplete normalized module parts: " + item.Input.Name);
                    results.Add(item.Input.Name, parts);
                }
            }
            CheckedAuditExecutable();
            if (canonicalTools != CanonicalFingerprintTools(auditExecutableSha!))
                throw new InvalidDataException("Fingerprint tools changed during normalization.");
            foreach (var item in inputs)
                if (!Same(item.Parts, ConsumerModuleParts(item.Source)))
                    throw new InvalidDataException("Module changed during fingerprint normalization: " + item.Name);
            foreach (var item in missing)
            {
                if (!Same(item.Input.Parts, ConsumerModuleParts(item.Source)))
                    throw new InvalidDataException("Fingerprint input snapshot changed: " + item.Input.Name);
                if (publishReceipts)
                {
                    Directory.CreateDirectory(item.Receipt);
                    File.WriteAllText(Path.Combine(item.Receipt, "fingerprints.json"),
                        JsonSerializer.Serialize(results[item.Input.Name]));
                    PublishSuccess(item.Input.Key, item.Receipt);
                }
            }
            if (publishReceipts && UseSuccessCache && Directory.Exists(SuccessCacheRoot)) EvictStaleSupport();
            RequireCertifiedFingerprints(certified, modules, canonicalTools);
            TraceConsumerFingerprints(session, started, elapsed.Elapsed,
                certified.Count + inputs.Length - missing.Count, missing.Count);
            return results;
        }
        finally { Directory.Delete(temporary, true); }
    }

    // Lake reuses restored artifacts by its traces; bind the tools and variables traces do not cover.
    string ConsumerToolsIdentity() => ContentKey(Sha(LeanExecutable) + "\n" +
        Sha(Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker")) + "\n" +
        Sha(Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "lake.exe" : "lake")) + "\n" +
        JsonSerializer.Serialize(ConsumerCacheEnvironment()));

    // Union of the certified extraction-independent support of every workspace in one session.
    sealed class ConsumerSupportExport
    {
        public readonly object Gate = new();
        public readonly string Staging = Path.Combine(Path.GetTempPath(), "leancil-consumer-export-" + Guid.NewGuid().ToString("N"));
        public readonly SortedDictionary<string, SortedDictionary<string, string>> Modules = new(StringComparer.Ordinal);
        public readonly SortedDictionary<string, string[]> Imports = new(StringComparer.Ordinal);
        public readonly SortedDictionary<string, SortedDictionary<string, string>> Files = new(StringComparer.Ordinal);
        public readonly HashSet<string> Conflicts = new(StringComparer.Ordinal);
        public SortedDictionary<string, string>? Sources;
    }

    // Called only after the workspace's replay, audits, rechecks and source-stability checks passed.
    void AddExportedSupport(ConsumerSupportExport export, string session, string root, SortedDictionary<string, string> inputs,
        Dictionary<string, string> independent, Dictionary<string, string[]> graph, string? collected,
        bool publishReceipts = true, Action? requireStable = null)
    {
        var fingerprints = PortableConsumerModuleParts(session, independent, publishReceipts);
        requireStable?.Invoke();
        var record = collected is null ? null : ReadConsumerSupportRecord(Path.Combine(collected, ConsumerSupportRecordName));
        var sources = PortableConsumerSources(root, inputs);
        lock (export.Gate)
        {
            export.Sources ??= sources;
            if (!Same(export.Sources, sources)) throw new InvalidDataException("Consumer sources changed between workspaces.");
            foreach (var (name, parts) in fingerprints)
            {
                if (export.Modules.TryGetValue(name, out var known))
                {
                    // Workspaces restore shared support, so differing bytes are left to receivers to replay.
                    if (!Same(known, parts)) export.Conflicts.Add(name);
                    continue;
                }
                export.Modules[name] = parts;
                export.Imports[name] = graph[name];
                if (record is null || !record.TryGetValue(name, out var module)) continue;
                var files = new SortedDictionary<string, string>(StringComparer.Ordinal);
                foreach (var file in module.Files)
                {
                    var target = Within(export.Staging, file);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(Within(collected!, file), target, true);
                    files[file] = Sha(target);
                }
                export.Files[name] = files;
            }
        }
    }

    void WriteExportedSupport(ConsumerSupportExport export)
    {
        var destination = Environment.GetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT");
        if (string.IsNullOrWhiteSpace(destination) || export.Sources is null || export.Modules.Count == 0) return;
        // A conflicting module invalidates its importers, as on receivers.
        var dropped = DependentModules(export.Imports, export.Conflicts);
        var modules = new SortedDictionary<string, SortedDictionary<string, string>>(
            export.Modules.Where(pair => !dropped.Contains(pair.Key)).ToDictionary(), StringComparer.Ordinal);
        if (modules.Count == 0) return;
        var files = new SortedDictionary<string, SortedDictionary<string, string>>(
            export.Files.Where(pair => modules.ContainsKey(pair.Key)).ToDictionary(), StringComparer.Ordinal);
        var manifest = new ConsumerSupportManifest(3, VerificationPolicy, libraryKey!, ConsumerToolchainIdentity(),
            export.Sources, modules, new(modules.Keys.ToDictionary(name => name, name => export.Imports[name]), StringComparer.Ordinal),
            ConsumerToolsIdentity(), files);
        var json = JsonSerializer.Serialize(manifest, Json) + "\n";
        var digest = ContentKey(json);
        Directory.CreateDirectory(destination);
        var path = Path.GetFullPath(Path.Combine(destination, digest + ".json"));
        // Files first: a manifest is never visible without the artifacts it names.
        var directory = Path.ChangeExtension(path, ".files");
        var staging = directory + "." + Guid.NewGuid().ToString("N");
        try
        {
            foreach (var file in files.Values.SelectMany(module => module.Keys))
            {
                var target = Within(staging, file);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Within(export.Staging, file), target);
            }
            Directory.CreateDirectory(staging);
            try { MoveCacheDirectory(staging, directory); }
            catch (IOException) when (Directory.Exists(directory)) { }
        }
        finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
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

    sealed record TrustedSupport(ConsumerSupportManifest Manifest, string Path);

    // Paths are separated by the platform path separator and digests by commas, pairwise.
    // Each manifest is authenticated by its own independently trusted digest.
    TrustedSupport[] TrustedConsumerSupport(string root, SortedDictionary<string, string> inputs)
    {
        if (freshProofs || freshLibrary) return [];
        var paths = (Environment.GetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT") ?? "")
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
        var digests = (Environment.GetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256") ?? "")
            .Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
        if (paths.Length == 0 && digests.Length == 0) return [];
        if (paths.Length != digests.Length)
            throw new InvalidDataException("Consumer support manifest digest mismatch or missing trusted digest.");
        var sources = PortableConsumerSources(root, inputs);
        string? toolchain = null;
        var trusted = new List<TrustedSupport>();
        for (var i = 0; i < paths.Length; i++)
        {
            var bytes = File.ReadAllBytes(paths[i]);
            if (Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes)) != digests[i])
                throw new InvalidDataException("Consumer support manifest digest mismatch or missing trusted digest.");
            ConsumerSupportManifest? manifest;
            try { manifest = JsonSerializer.Deserialize<ConsumerSupportManifest>(bytes); }
            catch (JsonException) { manifest = null; }
            if (manifest is null || manifest.Schema != 3 ||
                manifest.Sources is null || manifest.Modules is null || manifest.Imports is null ||
                manifest.Files is null || manifest.Tools is null ||
                manifest.Files.Values.Any(files => files is null) ||
                manifest.Modules.Any(pair => pair.Value is null ||
                    !manifest.Imports.TryGetValue(pair.Key, out var imports) || imports is null))
                throw new InvalidDataException("Invalid consumer support manifest.");
            if (manifest.Policy != VerificationPolicy || manifest.Library != libraryKey || !Same(manifest.Sources, sources) ||
                manifest.Toolchain != (toolchain ??= ConsumerToolchainIdentity())) continue;
            trusted.Add(new(manifest, Path.GetFullPath(paths[i])));
        }
        return [.. trusted];
    }

    // Opt-in: copies trusted producer artifacts so Lake can skip rebuilding them. Replay is still
    // skipped only for modules whose resulting bytes match a manifest fingerprint.
    void RestorePortableSupport(string session, TrustedSupport[] trusted)
    {
        if (trusted.Length == 0 || Environment.GetEnvironmentVariable(RestoreConsumerSupportVariable) != "true") return;
        var tools = ConsumerToolsIdentity();
        var restored = 0;
        foreach (var (manifest, path) in trusted)
        {
            if (manifest.Tools != tools) continue;
            var directory = Path.ChangeExtension(path, ".files");
            if (!Directory.Exists(directory)) continue;
            foreach (var (module, files) in manifest.Files)
            {
                // Restore whole modules only; a missing file keeps the module fresh.
                if (files.Count == 0 || files.Keys.Any(file => File.Exists(Within(session, file)) || !File.Exists(Within(directory, file))))
                    continue;
                foreach (var (file, hash) in files)
                {
                    var target = Within(session, file);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(Within(directory, file), target);
                    if (Sha(target) != hash) throw new InvalidDataException("Consumer support file digest mismatch: " + file);
                }
                restored++;
            }
        }
        if (restored > 0) CacheProgress($"portable consumer support library ({restored} modules)");
    }

    static Dictionary<string, string> ConsumerSupportModules(IEnumerable<IEnumerable<string>> manifests,
        Dictionary<string, string> modules)
    {
        var names = manifests.SelectMany(manifest => manifest).ToHashSet(StringComparer.Ordinal);
        return modules.Where(pair => names.Contains(pair.Key)).ToDictionary(StringComparer.Ordinal);
    }

    HashSet<string> ImportedConsumerSupport(string session, TrustedSupport[] trusted,
        Dictionary<string, string> modules, bool publishReceipts = true)
    {
        if (trusted.Length == 0) return [];
        var fingerprints = PortableConsumerModuleParts(session,
            ConsumerSupportModules(trusted.Select(support => support.Manifest.Modules.Keys), modules),
            publishReceipts);
        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var (manifest, _) in trusted)
        {
            // Invalidate the entire dependent closure of changed or missing modules.
            // Unused producer modules need not be built by a different method gate.
            var invalid = manifest.Modules.Where(pair => !fingerprints.TryGetValue(pair.Key, out var parts) ||
                !Same(pair.Value, parts)).Select(pair => pair.Key).ToHashSet(StringComparer.Ordinal);
            var graph = manifest.Modules.Keys.ToDictionary(name => name, name => manifest.Imports[name],
                StringComparer.Ordinal);
            foreach (var import in graph.Values.SelectMany(imports => imports).Distinct(StringComparer.Ordinal))
                if (!manifest.Modules.ContainsKey(import) &&
                    !File.Exists(Path.Combine(Toolchain, "lib/lean", import.Replace('.', '/') + ".olean")))
                    invalid.Add(import);
            invalid = DependentModules(graph, invalid);
            result.UnionWith(manifest.Modules.Keys.Where(name => !invalid.Contains(name) &&
                !IsCertifiedLibraryModule(name) &&
                name is not ("Extracted" or "ExtractedSymbols" or "ExtractionAudit") && !SelectionModules.Is(name) &&
                !name.StartsWith("LeanCILProof", StringComparison.Ordinal)));
        }
        return result;
    }


    // Every requested module is reported as replayed or rejected; a checker process failure throws.
    Dictionary<string, string> ReplayConsumerModules(string session, IEnumerable<string> modules, string leanPath)
    {
        var targets = modules.ToArray();
        var profile = Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") == "true";
        // A rejected or ineligible joint replay falls through to per-module replay, which attributes failures.
        if (!profile && (targets.Length > 1 || (targets.Length == 1 && auditExecutable is not null)) &&
            ReplayModulesJointly(session, targets, leanPath, "Joint kernel replay of consumer proof and dependencies")) return [];
        return ReplayConsumerModulesSeparately(session, targets, leanPath, profile);
    }
}
