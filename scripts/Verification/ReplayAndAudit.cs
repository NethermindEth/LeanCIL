using System.Runtime.ExceptionServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

// Kernel replay, olean theorem/axiom auditing and extraction manifest checks.
partial class Program
{
    string LeanExecutable => Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean");

    // Pin the sysroot that `lake env` would supply, so direct Lean runs use the trusted toolchain.
    IReadOnlyDictionary<string, string> LeanEnvironment => new Dictionary<string, string> { ["LEAN_SYSROOT"] = Toolchain };

    readonly byte[] bootstrapReplaySource = File.ReadAllBytes(At("CIL/Replay.lean"));

    // Per-module replay re-imports each module's dependencies; one shared import of
    // everything outside the targets makes large sets several times cheaper.
    // Imported target declarations cannot be skipped as already-checked duplicate theorems.
    // False when the set is ineligible or any declaration is rejected; callers then replay per module.
    bool ReplayModulesJointly(string cwd, string[] targets, string leanPath, string progress)
    {
        var runner = Path.Combine(Path.GetTempPath(), "leancil-joint-replay-" + Guid.NewGuid().ToString("N") + ".lean");
        var targetsPath = Path.ChangeExtension(runner, ".json");
        try
        {
            File.WriteAllText(targetsPath, JsonSerializer.Serialize(targets));
            string[] command;
            if (auditExecutable is not null)
                command = [CheckedAuditExecutable(), "--replay", targetsPath];
            else
            {
                // Bootstrap certification cannot trust the native auditor before authenticating it.
                if (Convert.ToHexStringLower(SHA256.HashData(bootstrapReplaySource)) != Sha(At("CIL/Replay.lean")))
                    throw new InvalidDataException("Kernel replay source changed before certification.");
                File.WriteAllText(runner, Encoding.UTF8.GetString(bootstrapReplaySource) +
                    "\n#eval do\n  let json ← IO.FS.readFile (String.fromUTF8! (ByteArray.mk #[" +
                    string.Join(",", System.Text.Encoding.UTF8.GetBytes(targetsPath)) +
                    "]))\n  let args ← IO.ofExcept <| (Lean.Json.parse json).bind Lean.fromJson?\n" +
                    "  CIL.Replay.replayModulesJointly args\n");
                command = [LeanExecutable, runner];
            }
            var result = Execute(command, cwd, leanPath, progress: progress, environment: LeanEnvironment);
            if (auditExecutable is not null) CheckedAuditExecutable();
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

    // Joint replay shares imported dependencies; rejected target sets retain the toolchain fallback.
    Dictionary<string, string> ReplayConsumerModulesSeparately(string session, string[] targets,
        string leanPath, bool profile)
    {
        var expected = SeparateReplayTargets(targets);
        var threads = ReplayWorkerCount();
        var runner = Path.Combine(Path.GetTempPath(), "leancil-replay-" + Guid.NewGuid().ToString("N") + ".lean");
        var targetsPath = Path.ChangeExtension(runner, ".json");
        var native = !profile && auditExecutable is not null;
        try
        {
            // A literal target list exceeds Lean's recursion limit for large module sets.
            File.WriteAllText(targetsPath, JsonSerializer.Serialize(targets));
            // Use the pinned toolchain's checker, not a consumer implementation
            // of kernel replay. Explicit targets avoid repeated search-path scans.
            if (!native) File.WriteAllText(runner, """
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
                "]))\n  let args ← IO.ofExcept <| (Lean.Json.parse json).bind Lean.fromJson?\n" +
                "  replayConsumerModules args " +
                profile.ToString().ToLowerInvariant() + "\n");
            // Unlike leanchecker, the lean frontend defaults to hardware
            // concurrency rather than honoring LEAN_NUM_THREADS itself.
            string[] command = native ? [CheckedAuditExecutable(), "--replay-separately", targetsPath]
                : [LeanExecutable, "-j" + threads, runner];
            var environment = new Dictionary<string, string>(LeanEnvironment) { ["LEAN_NUM_THREADS"] = threads };
            var result = Execute(command, session, leanPath, progress: profile
                ? "Profiled kernel replay of consumer modules" : "Kernel replay of consumer proof and dependencies",
                environment: environment);
            if (native) CheckedAuditExecutable();
            try { return ParseExpectedReplayResults(expected, result.Code, result.Stdout); }
            catch (InvalidDataException)
            {
                throw new InvalidOperationException(
                    $"Command failed ({result.Code}): {string.Join(' ', command)}\n{result.Output}");
            }
        }
        finally { File.Delete(runner); File.Delete(targetsPath); }
    }

    enum ReplayRejectionKind
    {
        unknownConstant, alreadyDeclared, declTypeMismatch, declHasMVars, declHasFVars,
        funExpected, typeExpected, letTypeMismatch, exprTypeMismatch, appTypeMismatch,
        invalidProj, thmTypeIsNotProp, constructorMismatch, recursorMismatch
    }

    sealed record ReplayRejection(string Declaration, ReplayRejectionKind Kind);

    /// <summary>Only a complete exact diagnostic stream can attribute a kernel rejection.</summary>
    static Dictionary<string, ReplayRejection> ParseReplayDiagnostics(string[] targets, int exitCode, string stdout)
    {
        var expected = SeparateReplayTargets(targets);
        HashSet<string> reported = new(StringComparer.Ordinal);
        Dictionary<string, ReplayRejection> rejections = new(StringComparer.Ordinal);
        bool completed = false;
        if (exitCode != 0) throw new InvalidDataException("Replay diagnostics did not complete.");
        foreach (var line in stdout.Split('\n',
            StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
        {
            if (!line.StartsWith('{')) continue;
            if (completed) throw new InvalidDataException("Record after replay diagnostic completion.");
            JsonDocument document;
            try { document = JsonDocument.Parse(line); }
            catch (JsonException error) { throw new InvalidDataException("Malformed replay diagnostic.", error); }
            using (document)
            {
                Dictionary<string, JsonElement> fields = new(StringComparer.Ordinal);
                foreach (var field in document.RootElement.EnumerateObject())
                    if (!fields.TryAdd(field.Name, field.Value))
                        throw new InvalidDataException("Duplicate replay diagnostic property.");
                if (fields.TryGetValue("complete", out var complete))
                {
                    if (fields.Count != 1 || complete.ValueKind != JsonValueKind.True)
                        throw new InvalidDataException("Invalid replay diagnostic completion.");
                    completed = true;
                    continue;
                }
                string Text(string key) => fields.TryGetValue(key, out var value) &&
                    value.ValueKind == JsonValueKind.String && !string.IsNullOrWhiteSpace(value.GetString())
                    ? value.GetString()! : throw new InvalidDataException("Missing replay diagnostic " + key);
                var module = Text("module");
                if (!expected.Contains(module) || !reported.Add(module))
                    throw new InvalidDataException("Unexpected or duplicate replay diagnostic module.");
                var outcome = Text("outcome");
                switch (outcome)
                {
                    case "accepted" when fields.Count == 2: break;
                    case "unavailable" when fields.Count == 3:
                        _ = Text("error");
                        break;
                    case "rejected" when fields.Count == 4:
                        var declaration = Text("declaration");
                        var kindText = Text("kind");
                        if (!Enum.TryParse<ReplayRejectionKind>(kindText, out var kind) ||
                            !Enum.IsDefined(kind) || kind.ToString() != kindText)
                            throw new InvalidDataException("Unknown replay rejection kind.");
                        rejections.Add(module, new(declaration, kind));
                        break;
                    default: throw new InvalidDataException("Invalid replay diagnostic outcome.");
                }
            }
        }
        if (!completed || reported.Count != expected.Count)
            throw new InvalidDataException("Incomplete replay diagnostic stream.");
        return rejections;
    }

    /// <summary>Diagnostic execution cannot replace the caller's terminal replay failure.</summary>
    Dictionary<string, ReplayRejection> DiagnoseReplayFailures(string session, string[] targets, string leanPath)
    {
        _ = SeparateReplayTargets(targets);
        if (targets.Length == 0 || auditExecutable is null) return new(StringComparer.Ordinal);
        var environment = new Dictionary<string, string>(LeanEnvironment)
        {
            ["LEAN_NUM_THREADS"] = ReplayWorkerCount()
        };
        var input = Path.Combine(Path.GetTempPath(), "leancil-diagnose-" + Guid.NewGuid().ToString("N") + ".json");
        try
        {
            File.WriteAllText(input, JsonSerializer.Serialize(targets));
            var result = Execute([CheckedAuditExecutable(), "--diagnose-replay", input], session, leanPath,
                progress: "Diagnosing rejected kernel replay", environment: environment);
            CheckedAuditExecutable();
            return ParseReplayDiagnostics(targets, result.Code, result.Stdout);
        }
        finally { File.Delete(input); }
    }

    /// <summary>Isolated replay uses a positive configured worker count or two workers.</summary>
    static string ReplayWorkerCount()
    {
        var configuredThreads = Environment.GetEnvironmentVariable("LEAN_NUM_THREADS");
        var threads = string.IsNullOrWhiteSpace(configuredThreads) ? "2" : configuredThreads;
        if (!uint.TryParse(threads, out var count) || count == 0)
            throw new InvalidDataException("LEAN_NUM_THREADS must be a positive integer.");
        return threads;
    }

    /// <summary>Every replay target is a nonempty unique exact module name.</summary>
    static HashSet<string> SeparateReplayTargets(string[] targets)
    {
        // Growing the set one entry at a time would discard large-object arrays and force full collections.
        var expected = new HashSet<string>(targets.Length, StringComparer.Ordinal);
        foreach (var target in targets)
            if (string.IsNullOrWhiteSpace(target) || !expected.Add(target))
                throw new InvalidDataException("Replay targets must have unique nonempty names");
        return expected;
    }

    /// <summary>Exactly one valid result is required for each requested module.</summary>
    static Dictionary<string, string> ParseSeparateReplayResults(string[] targets, int exitCode, string stdout)
        => ParseExpectedReplayResults(SeparateReplayTargets(targets), exitCode, stdout);

    static Dictionary<string, string> ParseExpectedReplayResults(HashSet<string> expected, int exitCode, string stdout)
    {
        var reported = new HashSet<string>(expected.Count, StringComparer.Ordinal);
        var failures = new Dictionary<string, string>(StringComparer.Ordinal);
        // Reading lines in place avoids a line array and a string per line, about 110 bytes per record.
        foreach (var range in stdout.AsSpan().Split('\n'))
        {
            var line = stdout.AsMemory(range).Trim();
            if (line.IsEmpty || line.Span[0] != '{') continue;
            var (module, error) = SeparateReplayRecord(line);
            if (!expected.Contains(module) || !reported.Add(module))
                throw new InvalidDataException("Unexpected or duplicate replay result");
            if (error is not null) failures.Add(module, error);
        }
        if (reported.Count != expected.Count || (exitCode == 0) != (failures.Count == 0))
            throw new InvalidDataException("Incomplete replay results");
        return failures;
    }

    /// <summary>A result has one module and exactly one typed success or failure field.</summary>
    static (string Module, string? Error) SeparateReplayRecord(ReadOnlyMemory<char> line)
    {
        JsonDocument document;
        try { document = JsonDocument.Parse(line); }
        catch (JsonException error) { throw new InvalidDataException("Malformed replay result", error); }
        using (document)
        {
            const int moduleField = 1, elapsedField = 2, errorField = 4;
            int fields = 0;
            JsonElement module = default, elapsed = default, error = default;
            foreach (var property in document.RootElement.EnumerateObject())
            {
                int field = property.NameEquals("module") ? moduleField
                    : property.NameEquals("milliseconds") ? elapsedField
                    : property.NameEquals("error") ? errorField
                    : throw new InvalidDataException("Unknown replay result field");
                if ((fields & field) != 0) throw new InvalidDataException("Duplicate replay result field");
                fields |= field;
                switch (field)
                {
                    case moduleField: module = property.Value; break;
                    case elapsedField: elapsed = property.Value; break;
                    case errorField: error = property.Value; break;
                }
            }
            var name = module.ValueKind == JsonValueKind.String ? module.GetString() : null;
            if (fields != (moduleField | elapsedField) && fields != (moduleField | errorField) ||
                string.IsNullOrWhiteSpace(name))
                throw new InvalidDataException("Invalid replay result shape");
            if ((fields & elapsedField) != 0)
            {
                if (elapsed.ValueKind != JsonValueKind.Number || !elapsed.TryGetUInt64(out _))
                    throw new InvalidDataException("Invalid replay elapsed time");
                return (name, null);
            }
            var message = error.ValueKind == JsonValueKind.String ? error.GetString() : null;
            if (string.IsNullOrEmpty(message)) throw new InvalidDataException("Invalid replay error");
            return (name, message);
        }
    }


    void ReplayCheckedModules(string[] targets, string leanPath, string progress)
    {
        if ((targets.Length > 1 || (targets.Length == 1 && auditExecutable is not null)) &&
            ReplayModulesJointly(Root, targets, leanPath, progress)) return;
        Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"),
            .. targets], leanPath: leanPath, progress: progress);
    }

    static SortedDictionary<string, string> ModuleArtifacts(string session,
        CheckedLibraryContents? checkedLibrary = null)
    {
        var compiled = Path.Combine(session, ".lake/build/lib/lean");
        if (!Directory.Exists(compiled)) return new(StringComparer.Ordinal);
        var files = Directory.EnumerateFiles(compiled, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
            .Select(path => (Name: Path.GetRelativePath(compiled, path).Replace('\\', '/'), Path: path));
        if (checkedLibrary is null || checkedLibrary.Library != session) return HashFiles(files);
        var artifacts = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var (name, path) in files)
            artifacts.Add(name, checkedLibrary.Files.TryGetValue(CompiledLibraryPrefix + name, out var hash)
                ? hash : Sha(path));
        return artifacts;
    }

    // Publish a deterministic manifest only after every file has been hashed successfully.
    static SortedDictionary<string, string> HashFiles(IEnumerable<(string Name, string Path)> files)
    {
        var entries = files.ToArray();
        var hashes = new string[entries.Length];
        var failures = new ExceptionDispatchInfo?[entries.Length];
        const int maximumWorkers = 4;
        Parallel.For(0, entries.Length,
            new ParallelOptions { MaxDegreeOfParallelism = Math.Min(maximumWorkers, Environment.ProcessorCount) },
            index =>
            {
                try { hashes[index] = Sha(entries[index].Path); }
                catch (Exception error) { failures[index] = ExceptionDispatchInfo.Capture(error); }
            });
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);
        for (var index = 0; index < entries.Length; index++)
        {
            // Preserve ordinary I/O exceptions so invalid-cache handling still applies.
            failures[index]?.Throw();
            result.Add(entries[index].Name, hashes[index]);
        }
        return result;
    }

    static string ModuleName(string artifact) => artifact.Split(".olean", 2)[0].Replace('/', '.');


    // Read the module name, not the whole line: a trailing comment does not change an import.
    // Shared by standalone proofs and consumer dependency traversal.
    [GeneratedRegex(@"^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([A-Za-z_][A-Za-z0-9_'.]*)(?=[ \t]*(?:--|/-|\r?$))", RegexOptions.Multiline)]
    private static partial Regex SourceImport { get; }

    // Proofs opt in to PDB names and locations with `import ExtractedSymbols` or its keyed form.
    static bool ImportsSymbols(string proof) => SourceImport.Matches(proof).Any(import =>
        import.Groups[1].Value is var module && (module == "ExtractedSymbols" || SelectionModules.IsSymbols(module)));

    static string SymbolsFor(string output) => Path.Combine(output, "Symbols.lean") is var path && File.Exists(path) ? path
        : throw new InvalidOperationException(MissingSymbols(output));

    static string MissingSymbols(string output)
    {
        var identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
        return "The proof imports ExtractedSymbols, but extraction found no matching portable PDB; build the assembly with its .pdb next to it and extract again, or remove the import.\n" +
            "  Assembly: " + Path.GetFullPath(identity.GetProperty("assemblyPath").GetString()!, output) + "\n" +
            "  Method: " + identity.GetProperty("entry").GetString();
    }

    // Inside the extractor, its own commands run in this process instead of starting another runtime.
    static Sha256Digest? RunExtractor(string[] command, Func<Sha256Digest, Sha256Digest>? receiveDigest = null)
    {
        if (TryRunExtractorInProcess(command, out var inProcessDigest)) return inProcessDigest;
        if (command is ["dotnet", _, "check", ..])
        {
            var result = Execute([.. command, "--format", "json"]);
            if (result.Code != 0)
                throw new InvalidOperationException($"Command failed ({result.Code}): {result.Output}");
            var json = JsonSerializer.Deserialize<JsonElement>(result.Stdout);
            var digest = Sha256Digest.Parse(json.GetProperty("identitySha256").GetString(), "extractor check result");
            return receiveDigest?.Invoke(digest) ?? digest;
        }
        Run(command);
        return null;
    }

    static Sha256Digest CheckManifest(string[] command, Func<Sha256Digest, Sha256Digest>? receiveDigest = null) =>
        RunExtractor(command, receiveDigest)
        ?? throw new InvalidDataException("Extraction check returned no manifest digest.");

    static string[] Extract(string mode, string assembly, string? identity, string entry, string output, string profile = "scalar") =>
        ["dotnet", ExtractorPath, mode, assembly, entry, output, profile,
            .. identity is null ? Array.Empty<string>() : ["--assembly", identity]];

    sealed record GeneratedExtraction(string Assembly, string Entry, string Output, string Profile = "scalar",
        string[]? InitializedTypes = null, string[]? TypeArguments = null);

    // Share immutable assembly bytes and signature validation, retaining fresh modules per request
    // and the extractor's final check that every assembly, symbol and profile input is unchanged.
    static void ExtractBatch(string mode, string? identity, IEnumerable<GeneratedExtraction> requests,
        string? extractor = null)
    {
        var path = Path.Combine(Path.GetTempPath(), "leancil-extractions-" + Guid.NewGuid().ToString("N") + ".json");
        try
        {
            File.WriteAllText(path, JsonSerializer.Serialize(requests.Select(request => new
            {
                assembly = request.Assembly, identity, entry = request.Entry, output = request.Output,
                profile = request.Profile, initializedTypes = request.InitializedTypes,
                typeArguments = request.TypeArguments
            })));
            Run(["dotnet", extractor ?? ExtractorPath, "generated-extraction-batch", mode, path]);
        }
        finally { File.Delete(path); }
    }

    // This module imports only the extracted program, never the user proof. The audit
    // checks its compiled theorem against the complete validator application for that
    // program; a declaration with the right name but type True is insufficient.
    const string ExtractionAuditSource = """
        import Extracted
        run_cmd do
          match (← Lean.getEnv).find? `Extracted.translation_valid with
          | some (.thmInfo _) => pure ()
          | _ => throwError "Expected extraction certificate theorem"
        theorem ExtractionAudit.valid :
            CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts Extracted.assemblies
              Extracted.platformDefinitions Extracted.methodEvidence Extracted.imports Extracted.program Extracted.managedDeclarations :=
              Extracted.translation_valid
        #print Extracted.imports
        """;

    static readonly string[] ApprovedAxioms = ["propext", "Quot.sound", "Classical.choice"];

    sealed record AuditRequest(string name, object? type = null, string[]? axioms = null,
        bool statement = false, bool refutation = false, string[]? allowedModules = null, bool term = false,
        object? expected = null);
    /// <summary>
    /// The contract a refutation theorem refutes, the program constant and method index it names when the audit
    /// could read them, and the theorem's position.
    /// </summary>
    internal sealed record AuditRefutation(string contract, string? program, int? method, int line, int column);

    /// <summary>
    /// A method of an extraction by signature, with the identity and digest of the assembly defining it.
    /// </summary>
    internal sealed record ExtractedMethod(string signature, string assembly, string assemblySha256);

    /// <summary>
    /// A verified refutation: the contract it refutes, the extracted method it refutes it for, and the theorem's
    /// position.
    /// </summary>
    internal sealed record VerifiedRefutation(string contract, ExtractedMethod method, int line, int column);

    /// <summary>The program constant of an extraction, which a refutation of one of its methods names.</summary>
    const string ExtractedProgram = "Extracted.program";

    /// <summary>
    /// The refutation `audited` states, bound to the method of `identity`, the verified extraction's manifest, that
    /// it names, or null when it states none. A refutation must name `program`, the extraction's program constant,
    /// and one of its methods, callees included, so a counterexample about another program is never reported
    /// against this extraction. When `required`, the request asked for a refutation and the theorem must be one.
    /// </summary>
    static VerifiedRefutation? ExtractedRefutation(AuditedTheorem audited, JsonElement identity,
        string program = ExtractedProgram, bool required = false)
    {
        var methods = identity.GetProperty("methods");
        if (audited.refutes is not { } refutes)
        {
            if (!required) return null;
            throw new InvalidOperationException($"{audited.name
                } was accepted as a refutation but states no counterexample predicate the audit reads.");
        }
        if (refutes.program != program || refutes.method is not { } index || index >= methods.GetArrayLength())
        {
            var named = refutes.program ?? "a program that is not a constant";
            var subject = $"{audited.name} refutes {refutes.contract} for {named}, method {
                refutes.method?.ToString() ?? "that is not a numeral"}";
            throw new InvalidOperationException(
                $"{subject}; a refutation states {program} and one of its {methods.GetArrayLength()} methods.");
        }
        var method = methods[index];
        // A method's assembly is its pin index: 0 the extracted assembly, k its k-th reference.
        var pin = method.GetProperty("assembly").GetInt32();
        var (assembly, digest) = pin == 0
            ? (identity.GetProperty("assemblyIdentity"), identity.GetProperty("assemblySha256"))
            : (identity.GetProperty("references")[pin - 1].GetProperty("assemblyIdentity"),
                identity.GetProperty("references")[pin - 1].GetProperty("sha256"));
        return new(refutes.contract, new(method.GetProperty("signature").GetString()!, assembly.GetString()!,
            digest.GetString()!), refutes.line, refutes.column);
    }
    sealed record AuditedTheorem(string name, string? error, string[]? axioms, string? statement,
        AuditRefutation? refutes,
        JsonElement? term = null, string? termError = null, bool? matches = null, string? mismatch = null);

    /// <summary>
    /// What a gate asks of a verified theorem's statement: its <c>term</c>, to compare other statements with, or
    /// that the kernel accept the theorem at <c>Expected</c>, the term of another theorem, or, when <c>Refuted</c>, at
    /// the counterexample predicate of the contract whose <c>Holds</c> that term states.
    /// </summary>
    sealed record StatementRequest(bool Term, string? Expected = null, bool Refuted = false)
    {
        /// <summary>The audit request fields, with <c>Expected</c> as the JSON the audit decodes.</summary>
        internal AuditRequest Apply(AuditRequest audit) => audit with
        {
            term = Term,
            expected = Expected is null ? null
                : new { term = JsonDocument.Parse(Expected).RootElement, refuted = Refuted }
        };
    }

    /// <summary>
    /// The statement of a verified theorem as another audit decodes it (<c>term</c>, or <c>termError</c> saying why
    /// there is none), and whether the kernel accepted the theorem at the statement it was compared with.
    /// </summary>
    sealed record StatementIdentity(JsonElement? term, string? termError, bool? matches, string? mismatch);

    /// <summary>
    /// A theorem that verified but that the kernel did not accept at the statement its request expected, so it
    /// does not prove, or refute, that statement.
    /// </summary>
    internal sealed class StatementMismatchException(string? mismatch) : InvalidOperationException(
        $"Verified statement does not match the requested contract: {mismatch}");

    static StatementIdentity Identity(AuditedTheorem audited) =>
        new(audited.term, audited.termError, audited.matches, audited.mismatch);
    sealed record AuditConstantRequest(string name, object value, object? type = null, string[]? axioms = null);
    sealed record AuditedInterfaces(string? error);
    sealed record AuditedClosure(string name, string? error, string? kind, string? canonical);
    sealed record AuditNamespaces(string[] prefixes, string[] axioms);
    sealed record AuditedNamespaces(int count, Dictionary<string, int> prefixes, Dictionary<string, int> modules, string[] axioms,
        AuditedTheorem[] rejected, string? error);
    sealed record AuditedOleans(Dictionary<string, string> modules, AuditedTheorem[] theorems, AuditedTheorem[] constants,
        AuditedInterfaces? interfaces = null, AuditedClosure[]? closures = null, AuditedNamespaces? namespaces = null,
        string[]? replayed = null, bool? fused = null);

    static readonly JsonSerializerOptions AuditJson = new() { DefaultIgnoreCondition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull };

    static object AuditConstant(string name) => new { @const = name };

    // The certificate must prove the validator for exactly the emitted tables and program.
    static AuditRequest ExtractionCertificate(string theorem, string prefix = "") => new(theorem,
        new { app = new[] { AuditConstant("CIL.Extraction.TranslationValid") }.Concat(
            new[] { "rawLayouts", "computedLayouts", "assemblies", "platformDefinitions", "methodEvidence", "imports",
                "program", "managedDeclarations" }
                .Select(name => AuditConstant(prefix + "Extracted." + name))) },
        ApprovedAxioms);

    static AuditRequest ProofTheorem(string theorem) => new(theorem, axioms: ApprovedAxioms, statement: true, refutation: true);

    string? auditExecutable;
    string? auditExecutableSha;

    string CheckedAuditExecutable()
    {
        // The manifest bound this executable's hash when the library was validated.
        if (auditExecutable is null || auditExecutableSha is null || !File.Exists(auditExecutable))
            throw new InvalidOperationException("Theorem audit executable is missing");
        return auditExecutable;
    }

    // Reads the kernel-replayed oleans only: no imported elaborator, notation, extension or initializer runs.
    AuditedOleans AuditOleans(string leanPath, string[] modules, AuditRequest[] theorems, AuditConstantRequest[]? constants = null,
        string[]? interfaces = null, string[]? closures = null, AuditNamespaces? namespaces = null,
        string[]? replayTargets = null, string? replayProgress = null)
    {
        var executable = CheckedAuditExecutable();
        var request = Path.Combine(Path.GetTempPath(), "leancil-audit-" + Guid.NewGuid().ToString("N") + ".json");
        var result = Path.ChangeExtension(request, ".result.json");
        try
        {
            constants ??= [];
            interfaces ??= [];
            closures ??= [];
            File.WriteAllText(request, JsonSerializer.Serialize(new { modules, theorems, constants, interfaces,
                closures = closures.Select(name => new { name }), namespaces, replayTargets }, AuditJson));
            Run([executable, request, result], leanPath: leanPath, environment: LeanEnvironment,
                progress: replayTargets is null ? null :
                    replayProgress ?? "Joint kernel replay of consumer proof and dependencies");
            CheckedAuditExecutable();
            var audited = JsonSerializer.Deserialize<AuditedOleans>(File.ReadAllText(result))
                ?? throw new InvalidDataException("Missing theorem audit result");
            if (audited.theorems.Length != theorems.Length || audited.theorems.Zip(theorems).Any(pair => pair.First.name != pair.Second.name) ||
                audited.constants.Length != constants.Length || audited.constants.Zip(constants).Any(pair => pair.First.name != pair.Second.name) ||
                modules.Any(module => !audited.modules.ContainsKey(module)) || audited.interfaces is null || audited.closures is null ||
                audited.closures.Length != closures.Length || audited.closures.Zip(closures).Any(pair => pair.First.name != pair.Second) ||
                (namespaces is not null && (audited.namespaces?.prefixes is null || audited.namespaces.modules is null ||
                    audited.namespaces.axioms is null || audited.namespaces.rejected is null)) ||
                (replayTargets is not null && (audited.replayed is null || audited.fused is null ||
                    !audited.replayed.SequenceEqual(replayTargets))))
                throw new InvalidDataException("Incomplete theorem audit result");
            if (replayTargets is not null) LogAuditFused(audited.fused, modules);
            return audited;
        }
        finally { File.Delete(request); File.Delete(result); }
    }

    // The audited module must be the artifact that was hashed and replayed, not a shadow on the search path.
    // Lean reports the file with links followed, so both sides are compared that way.
    static void RequireAuditedModule(AuditedOleans audited, string module, string path)
    {
        if (!SameLocation(audited.modules[module], path))
            throw new InvalidDataException($"Audited module {module} resolved to {audited.modules[module]}, not {path}");
    }

    static void RequireAuditedConstants(AuditedOleans audited)
    {
        foreach (AuditedTheorem constant in audited.constants)
            if (constant.error is not null) throw new InvalidOperationException(constant.error);
    }

    static string[] AuditedAxioms(AuditedTheorem audited)
    {
        if (audited.error is not null) throw new InvalidOperationException(audited.error);
        var axioms = audited.axioms ?? throw new InvalidDataException("Missing transitive theorem axiom audit");
        if (axioms.Any(a => !ApprovedAxioms.Contains(a)))
            throw new InvalidOperationException("Unapproved proof axioms: " + string.Join(", ", axioms));
        return axioms;
    }

    // Names the drivers generate or resolve from the toolchain and framework. Case variants collide on Windows and macOS.
    internal static class ContractModules
    {
        static readonly string[] ReservedRoots = ["CIL", "Lean", "Init", "Std", "Lake", "Extracted", "ExtractedImports", "Proof", "Audit",
            "ExtractionAudit", "ExtractedSymbols", "Symbols", "Examples", "Tests", "lakefile",
            "StrictBinding", "BindingAudit"];

        internal static bool Name(string? value) => value is not null && !value.Split('.').Contains("_root_", StringComparer.Ordinal) &&
            Regex.IsMatch(value, @"\A[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\z");

        internal static bool Interface(string? value) => Name(value) && value!.Split('.')[0] is var root &&
            !ReservedRoots.Contains(root, StringComparer.OrdinalIgnoreCase) && !root.StartsWith("LeanCIL", StringComparison.OrdinalIgnoreCase);
    }

    /// <summary>
    /// `Extracted.KEY` and `ExtractedSymbols.KEY` name one method's extraction, so proofs of different methods
    /// share a package. Verification builds each as a re-export of the extraction it checks: a key selects
    /// which extraction a proof expects, never what is certified.
    /// </summary>
    internal static class SelectionModules
    {
        const int DigestLength = 8;

        /// <summary>
        /// The key of the extraction `identity` describes: the method's type and name, then a digest of the
        /// assembly name, entry, profile name and initialization assumptions. Rebuilds and versions keep it.
        /// </summary>
        internal static string Key(JsonElement identity)
        {
            var assembly = identity.GetProperty("assemblyIdentity").GetString()!.Split(',')[0].Trim();
            var entry = identity.GetProperty("entry").GetString()!;
            var profile = identity.GetProperty("profile").GetProperty("Name").GetString()!;
            string[] initialized = identity.TryGetProperty("initializedTypes", out var types)
                ? [.. types.EnumerateArray().Select(type => type.GetString()!)] : [];
            var digest = ContentKey(string.Join("\n", [assembly, entry, profile, .. initialized]))[..DigestLength];
            var member = entry[..entry.IndexOf('(')];
            member = member[(member.LastIndexOf(' ') + 1)..];
            var type = member[..member.IndexOf("::", StringComparison.Ordinal)];
            type = type.Split('<')[0];
            type = type[(type.LastIndexOfAny(['.', '/']) + 1)..];
            var readable = Regex.Replace(type + "_" + member[(member.IndexOf("::", StringComparison.Ordinal) + 2)..],
                "[^A-Za-z0-9_]", "_");
            return (char.IsAsciiLetter(readable[0]) ? "" : "M") + readable + "_" + digest;
        }

        /// <summary>Whether `module` names a keyed extraction module rather than a source of the package.</summary>
        internal static bool Is(string module) =>
            module.StartsWith("Extracted.", StringComparison.Ordinal) ||
            module.StartsWith("ExtractedSymbols.", StringComparison.Ordinal);

        internal static bool IsSymbols(string module) =>
            module.StartsWith("ExtractedSymbols.", StringComparison.Ordinal);

        /// <summary>The source of a keyed module: the plain module it stands for, so it adds no declaration.</summary>
        internal static string Source(string module) =>
            "import " + (IsSymbols(module) ? "ExtractedSymbols" : "Extracted") + "\n";

        /// <summary>
        /// The keyed modules `imports` names, after rejecting a key of another extraction: a proof written for one
        /// method must not be checked against another one's program.
        /// </summary>
        internal static string[] Selected(IEnumerable<string> imports, JsonElement identity, string source)
        {
            var key = Key(identity);
            var selected = imports.Where(Is).Distinct(StringComparer.Ordinal).ToArray();
            foreach (var module in selected)
                if (module != "Extracted." + key && module != "ExtractedSymbols." + key)
                    throw new InvalidDataException(source + " imports " + module +
                        ", which names another extraction. This extraction of " +
                        identity.GetProperty("entry").GetString() + " under the " +
                        identity.GetProperty("profile").GetProperty("Name").GetString() + " profile is Extracted." +
                        key + "; import that, or select the method the proof was written for.");
            return selected;
        }
    }

    // One read of identity.json and of the import sources it pins; staging, keys and reports all derive from it.
    internal sealed record ExtractionIdentity(string Output, string Sha256, JsonElement Root, SortedDictionary<string, string> Sources)
    {
        internal string GeneratedSha256 => Root.GetProperty("generatedSha256").GetString()
            ?? throw new InvalidDataException("Missing generated source digest.");

        internal void RequireDigest(Sha256Digest checkedDigest)
        {
            if (Sha256 != checkedDigest.ToString())
                throw new InvalidDataException("Extraction identity changed during verification.");
        }

        // Deep diagnostics also require the original manifest to remain present and byte-identical.
        internal bool ManifestUnchanged() => File.ReadAllBytes(Path.Combine(Output, "identity.json")).AsSpan()
            .SequenceEqual(Encoding.UTF8.GetBytes(Root.GetRawText()));

        internal JsonElement[] Imports => Root.TryGetProperty("imports", out JsonElement imports) ? [.. imports.EnumerateArray()] : [];
        internal JsonElement[] Graph => Root.TryGetProperty("importGraph", out JsonElement graph) ? [.. graph.EnumerateArray()] : [];

        internal static string Resolve(string output, string recorded) => Path.GetFullPath(recorded, output);

        internal static ExtractionIdentity Read(string output)
        {
            byte[] bytes = File.ReadAllBytes(Path.Combine(output, "identity.json"));
            JsonElement root = JsonSerializer.Deserialize<JsonElement>(bytes);
            SortedDictionary<string, string> sources = new(StringComparer.Ordinal);
            if (root.TryGetProperty("importModules", out JsonElement modules))
                foreach (JsonProperty module in modules.EnumerateObject())
                {
                    if ((module.Name != "ExtractedImports" && !ContractModules.Interface(module.Name)) ||
                        sources.Keys.Any(name => string.Equals(name, module.Name, StringComparison.OrdinalIgnoreCase)))
                        throw new InvalidDataException("Invalid imported interface module: " + module.Name);
                    string source = File.ReadAllText(Path.Combine(output, module.Name.Replace('.', Path.DirectorySeparatorChar) + ".lean"));
                    if (ContentKey(source) != module.Value.GetString()) throw new InvalidDataException("Imported interface source hash mismatch: " + module.Name);
                    sources.Add(module.Name, source);
                }
            return new(output, Convert.ToHexStringLower(SHA256.HashData(bytes)), root, sources);
        }
    }

    Dictionary<string, string[]> ContractModuleImports(string destination, SortedDictionary<string, string> sources)
    {
        string input = Path.Combine(destination, "LeanCILHeader" + Guid.NewGuid().ToString("N") + ".json");
        string runner = Path.ChangeExtension(input, ".lean");
        try
        {
            File.WriteAllText(input, JsonSerializer.Serialize(sources.Values));
            string result;
            if (auditExecutable is null)
            {
                // Editor workspaces parse headers before a certified library exists.
                File.WriteAllText(runner, File.ReadAllText(At("CIL/Interface/Headers.lean")) +
                    "\ndef main (args : List String) : IO Unit := do\n" +
                    "  let [input] := args | throw (IO.userError \"Expected source manifest\")\n" +
                    "  CIL.Interface.writeSourceHeaders input\n");
                result = Run([LeanExecutable, "--run", runner, input], destination, environment: LeanEnvironment);
            }
            else
            {
                var executable = CheckedAuditExecutable();
                result = Run([executable, "--headers", input], destination, environment: LeanEnvironment);
                CheckedAuditExecutable();
            }
            string[] lines = result.Split('\n', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
            if (lines.Length != sources.Count) throw new InvalidDataException("Incomplete contract interface import graph.");
            return sources.Keys.Zip(lines).ToDictionary(pair => pair.First,
                pair => JsonSerializer.Deserialize<string[]>(pair.Second) ?? throw new InvalidDataException("Invalid contract import graph."), StringComparer.Ordinal);
        }
        finally { File.Delete(input); File.Delete(runner); }
    }
    string[] StageImportSources(ExtractionIdentity extraction, string destination)
    {
        SortedDictionary<string, string> sources = extraction.Sources;
        if (sources.Count == 0) return [];
        Dictionary<string, string[]> dependencies = ContractModuleImports(destination, sources);
        foreach ((string module, string[] imports) in dependencies)
            if (module != "ExtractedImports")
                foreach (string dependency in imports)
                    if ((!sources.ContainsKey(dependency) || dependency == "ExtractedImports") && !TrustedContractModule(dependency))
                        throw new InvalidDataException("Undeclared contract interface dependency: " + dependency);
        List<string> ordered = [];
        HashSet<string> complete = new(StringComparer.Ordinal);
        HashSet<string> active = new(StringComparer.Ordinal);
        void Stage(string module)
        {
            if (complete.Contains(module)) return;
            if (!active.Add(module)) throw new InvalidDataException("Cyclic contract interface module imports: " + module);
            foreach (string dependency in dependencies[module])
                if (sources.ContainsKey(dependency)) Stage(dependency);
            string path = Path.Combine(destination, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
            if (File.Exists(path)) throw new InvalidDataException("Contract interface module shadows an existing source: " + module);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, sources[module], new UTF8Encoding(false));
            active.Remove(module);
            ordered.Add(module);
            complete.Add(module);
        }
        foreach (string module in sources.Keys) Stage(module);
        return ordered.ToArray();
    }

    static SortedDictionary<string, string> ContractInterfaceArtifacts(string directory, string[] modules)
    {
        if (modules.Length == 0) return new(StringComparer.Ordinal);
        HashSet<string> names = new(modules, StringComparer.Ordinal);
        var artifacts = HashFiles(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal))
            .Select(path => (Relative: Path.GetRelativePath(directory, path).Replace('\\', '/'), Path: path))
            .Where(artifact => names.Contains(ModuleName(artifact.Relative)))
            .Select(artifact => (artifact.Relative, artifact.Path)));
        foreach (string module in modules)
            if (!artifacts.ContainsKey(module.Replace('.', '/') + ".olean"))
                throw new InvalidDataException("Published contract interface artifact is missing: " + module);
        return artifacts;
    }

    static void RequireContractInterfaceArtifacts(string directory, string[] modules,
        SortedDictionary<string, string> accepted)
    {
        if (!Same(accepted, ContractInterfaceArtifacts(directory, modules)))
            throw new InvalidDataException("Published contract interface artifacts changed after their closure audit.");
    }

    bool TrustedContractModule(string module) =>
        ((module == "CIL" || module.StartsWith("CIL.", StringComparison.Ordinal)) && File.Exists(At(module.Replace('.', '/') + ".lean"))) ||
        File.Exists(Path.Combine(Toolchain, "lib/lean", module.Replace('.', '/') + ".olean"));

    // Validation and closures come from leancil-audit on replayed oleans, so interface code cannot forge them.
    bool TryReplayContractInterfaces(ExtractionIdentity extraction, string[] modules, string leanPath,
        Func<string, string> artifact, Dictionary<string, AuditedClosure>? checkedClosures = null)
    {
        if (!modules.Any(module => module != "ExtractedImports") ||
            Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") == "true") return false;
        try
        {
            CheckContractInterfaces(extraction, modules, leanPath, artifact, modules, checkedClosures);
            return true;
        }
        // Duplicate declarations and replay failures retain the independent checker diagnostics.
        catch (InvalidOperationException) { return false; }
    }

    void CheckContractInterfaces(ExtractionIdentity extraction, string[] modules, string leanPath,
        Func<string, string> artifact, string[]? replayTargets = null, Dictionary<string, AuditedClosure>? checkedClosures = null)
    {
        string[] interfaces = modules.Where(module => module != "ExtractedImports").ToArray();
        JsonElement[] imports = extraction.Imports;
        if (interfaces.Length == 0 && imports.Length == 0) return;
        if (interfaces.Length == 0) throw new InvalidDataException("Contract imports without a published interface module");
        string[] constants = imports.Select(import => import.GetProperty("contractConstant").GetString()!).Distinct(StringComparer.Ordinal).ToArray();
        AuditedOleans audited = AuditOleans(leanPath, interfaces, [], interfaces: interfaces, closures: constants,
            replayTargets: replayTargets);
        foreach (string module in interfaces) RequireAuditedModule(audited, module, artifact(module));
        if (audited.interfaces?.error is { } invalid) throw new InvalidDataException(invalid);
        Dictionary<string, AuditedClosure> closures = audited.closures!.ToDictionary(closure => closure.name, StringComparer.Ordinal);
        foreach (JsonElement import in imports)
        {
            string constant = import.GetProperty("contractConstant").GetString()!;
            AuditedClosure closure = closures[constant];
            if (closure.error is not null) throw new InvalidDataException(closure.error);
            if (ContentKey(closure.canonical!) != import.GetProperty("closureDigest").GetString())
                throw new InvalidDataException("Published contract canonical closure digest mismatch: " + constant);
            if (closure.kind != import.GetProperty("contractKind").GetString())
                throw new InvalidDataException("Published contract canonical type mismatch: " + constant);
        }
        if (checkedClosures is not null)
            foreach (var (name, closure) in closures) checkedClosures.Add(name, closure);
    }

    static JsonElement[] ImportGraph(string output) => ExtractionIdentity.Read(output).Graph;

    // acceptedVia and sourceBundleDigest name a node whose export forced full verification re-checked.
    sealed record DeploymentDependency(string assemblyIdentity, string implementationSha256, string interfaceDigest,
        string[] dependencies, bool conditional,
        [property: System.Text.Json.Serialization.JsonIgnore(
            Condition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull)]
        string? acceptedVia = null,
        [property: System.Text.Json.Serialization.JsonIgnore(
            Condition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull)]
        string? sourceBundleDigest = null);

    static DeploymentDependency[] DeploymentDependencies(JsonElement identity) =>
        identity.TryGetProperty("importGraph", out JsonElement graph) ? graph.EnumerateArray().Select(node =>
            new DeploymentDependency(node.GetProperty("assemblyIdentity").GetString()!,
                node.GetProperty("implementationSha256").GetString()!, node.GetProperty("interfaceDigest").GetString()!,
                node.GetProperty("dependencies").EnumerateArray().Select(dependency => dependency.GetProperty("assemblyIdentity").GetString()!).ToArray(),
                node.GetProperty("dependencies").GetArrayLength() > 0)).ToArray() : [];

    static bool ReferenceOnlyImports(ExtractionIdentity extraction) =>
        extraction.Imports.Any(import => import.GetProperty("isReferenceAssembly").GetBoolean()) ||
        extraction.Graph.Any(node => node.GetProperty("isReferenceAssembly").GetBoolean());

    static void RequireImplementationImports(ExtractionIdentity extraction)
    {
        if (ReferenceOnlyImports(extraction))
            throw new InvalidDataException("Reference-only contract input: caller proof checked for authoring only; no verification report or success receipt is certified.");
    }

    static string SemanticExtractionIdentity(ExtractionIdentity extraction)
    {
        JsonElement identity = extraction.Root;
        JsonElement[] graph = extraction.Graph;
        return ContentKey(JsonSerializer.Serialize(new
        {
            assembly = identity.GetProperty("assemblySha256"), generated = identity.GetProperty("generatedSha256"),
            profile = identity.GetProperty("profile"), interfaces = extraction.Sources,
            dependencyGraph = graph.Any(node => node.GetProperty("dependencies").GetArrayLength() > 0) ? graph.Select(node => new
            {
                assemblyIdentity = node.GetProperty("assemblyIdentity"), implementationSha256 = node.GetProperty("implementationSha256"),
                interfaceDigest = node.GetProperty("interfaceDigest"), dependencies = node.GetProperty("dependencies")
            }).ToArray() : [],
            imports = extraction.Imports.Select(import => new
            {
                slot = import.GetProperty("slot"), identity = import.GetProperty("identity"),
                profile = import.GetProperty("profile"), interfaceDigest = import.GetProperty("interfaceDigest"),
                closureDigest = import.GetProperty("closureDigest"), constant = import.GetProperty("contractConstant"),
                kind = import.GetProperty("contractKind"), staticIdentities = import.GetProperty("staticIdentities")
            })
        }));
    }

    // Certification fields are sidecar text outside every pinned digest; sidecarSha256 names the bytes they came from.
    sealed record PublishedImport(int slot, string identity, string profile, string implementationSha256,
        string interfaceDigest, string acceptedVia, string certificationTheorem, string certificationStatement,
        string certificationStatementDigest, JsonElement staticIdentities, string deploymentObligation,
        string? sidecarSha256 = null, bool certificationAuthenticated = false, string? sourceBundleDigest = null,
        JsonElement? typedSignature = null, JsonElement? layouts = null, string[]? typeArguments = null,
        JsonElement[]? initializationAssumptions = null);

    static PublishedImport[] PublishedImports(JsonElement extraction) => extraction.TryGetProperty("imports", out JsonElement imports)
        ? imports.EnumerateArray().Select(import => new PublishedImport(import.GetProperty("slot").GetInt32(),
            import.GetProperty("identity").GetString()!, import.GetProperty("profile").GetString()!,
            import.GetProperty("implementationSha256").GetString()!, import.GetProperty("interfaceDigest").GetString()!,
            "published-certification", import.GetProperty("certificationTheorem").GetString()!,
            import.GetProperty("certificationStatement").GetString()!, import.GetProperty("certificationStatementDigest").GetString()!,
            import.GetProperty("staticIdentities"),
            "This conditional caller proof is not a deployment guarantee: an unsatisfiable imported contract can make it vacuous. " +
            "Deployment must use these exact implementation bytes and discharge the published contract at this identity, signature and profile. " +
            "Published interface sources execute code with verifier permissions during compilation.",
            sidecarSha256: import.GetProperty("sidecarSha256").GetString()!,
            typedSignature: import.TryGetProperty("typedSignature", out JsonElement typed) ? typed : null,
            layouts: import.TryGetProperty("publishedLayouts", out JsonElement layouts) ? layouts : null,
            typeArguments: import.TryGetProperty("typeArguments", out JsonElement arguments) ? arguments.Deserialize<string[]>() : null,
            initializationAssumptions: InitializationAssumptions(import))).ToArray()
        : [];

    static bool HasContractImports(ExtractionIdentity extraction) =>
        extraction.Sources.ContainsKey("ExtractedImports") == (extraction.Imports.Length > 0) ? extraction.Imports.Length > 0
            : throw new InvalidDataException("Contract import slots and the generated import premise disagree");

    // With imports, only a claim conditional on exactly the generated import premise is certified.
    static AuditRequest ProofTheorem(string theorem, ExtractionIdentity extraction) => !HasContractImports(extraction) ? ProofTheorem(theorem)
        : ProofTheorem(theorem) with { type = new { app = new object[] { AuditConstant("CIL.Safety.HoldsGiven"),
            AuditConstant("Extracted.program"), AuditConstant("Extracted.ImportsHold"), "_" } } };

    // The premise is rebuilt from identity.json: each slot's root contract at its canonical numeral, so
    // interface instances, notation or shadowing namespaces cannot retarget or weaken it.
    static AuditConstantRequest[] ImportPremise(ExtractionIdentity extraction)
    {
        if (!HasContractImports(extraction)) return [];
        int methods = extraction.Root.GetProperty("methods").GetArrayLength();
        object[] slots = [.. extraction.Imports.Select(import => (object)new { app = new object[] {
            AuditConstant("CIL.Safety." + (import.GetProperty("contractKind").GetString() == "method" ? "MethodContract" : "OutcomeContract") + ".Holds"),
            "_", "_", AuditConstant(import.GetProperty("contractConstant").GetString()!), new { bvar = 0 },
            new { nat = methods + import.GetProperty("slot").GetInt32() } } })];
        object body = slots.Length == 0 ? AuditConstant("True")
            : slots.SkipLast(1).Reverse().Aggregate(slots[^1], (rest, slot) => new { app = new[] { AuditConstant("And"), slot, rest } });
        object program = AuditConstant("CIL.Program");
        return [new("Extracted.ImportsHold", new { lam = new[] { program, body } }, new { forall = new[] { program, new { sort = 0 } } })];
    }

    static string[] ContractImportAssumptions(JsonElement extraction) =>
        extraction.TryGetProperty("imports", out JsonElement imports) ? imports.EnumerateArray().Select(import =>
            "_root_.CIL.Safety." + (import.GetProperty("contractKind").GetString() == "method" ? "MethodContract" : "OutcomeContract") +
            ".Holds _root_." + import.GetProperty("contractConstant").GetString() + " linked " +
            (extraction.GetProperty("methods").GetArrayLength() + import.GetProperty("slot").GetInt32())).ToArray() : [];

}
