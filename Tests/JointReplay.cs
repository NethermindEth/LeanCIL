#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ConsumerTraceDirectory.cs

using System.Diagnostics;
using System.Text.Json;

if (args is not ([] or ["--audit-only"] or ["--results-only"] or ["--diagnostics-only"]))
    throw new ArgumentException("Usage: JointReplay.cs [--audit-only|--results-only|--diagnostics-only]");
CheckSeparateReplayResults();
CheckReplayDiagnostics();
CheckReplayWorkers();
if (args is ["--results-only"]) return;
using var verification = new Program();
var root = At("artifacts/JointReplay");
if (Directory.Exists(root)) Directory.Delete(root, true);
Directory.CreateDirectory(root);
var environment = new Dictionary<string, string> { ["LEAN_SYSROOT"] = verification.Toolchain };

void CheckReplayWorkers()
{
    var original = Environment.GetEnvironmentVariable("LEAN_NUM_THREADS");
    try
    {
        foreach (var configured in new string?[] { null, "", " ", "8" })
        {
            Environment.SetEnvironmentVariable("LEAN_NUM_THREADS", configured);
            if (ReplayWorkerCount() != (configured == "8" ? "8" : "2"))
                throw new InvalidOperationException("Isolated replay worker count changed.");
        }
        foreach (var configured in new[] { "0", "-1", "invalid" })
        {
            Environment.SetEnvironmentVariable("LEAN_NUM_THREADS", configured);
            try { ReplayWorkerCount(); }
            catch (InvalidDataException) { continue; }
            throw new InvalidOperationException("Invalid isolated replay worker count was accepted.");
        }
    }
    finally { Environment.SetEnvironmentVariable("LEAN_NUM_THREADS", original); }
    Console.WriteLine("PASS isolated replay worker configuration");
}

void CheckSeparateReplayResults()
{
    const string success = """{"module":"A","milliseconds":1}""";
    const string failure = """{"module":"A","error":"rejected"}""";
    void Reject(string[] targets, int code, string output)
    {
        try { ParseSeparateReplayResults(targets, code, output); }
        catch (InvalidDataException) { return; }
        throw new InvalidOperationException("Invalid replay result was accepted: " + output);
    }
    if (ParseSeparateReplayResults(["A"], 0, "progress\r\n  " + success + " \r\nfinished").Count != 0 ||
        ParseSeparateReplayResults(["A"], 1, failure)["A"] != "rejected" ||
        ParseSeparateReplayResults([], 0, "progress\n").Count != 0)
        throw new InvalidOperationException("Valid replay results changed");
    var mixed = ParseSeparateReplayResults(["A", "B"], 7,
        success + "\n" + """{"error":"kernel rejected B","module":"B"}""");
    if (mixed.Count != 1 || mixed["B"] != "kernel rejected B")
        throw new InvalidOperationException("Replay failure ownership changed");
    if (ParseSeparateReplayResults(["A"], 0,
        """{"milliseconds":18446744073709551615,"module":"A"}""").Count != 0)
        throw new InvalidOperationException("Maximum elapsed value was rejected");
    if (ParseSeparateReplayResults(["A"], 0, """{"mo\u0064ule":"A","milliseconds":1}""").Count != 0)
        throw new InvalidOperationException("Escaped field name was not read as its unescaped name");
    Reject(["A"], 0, success + "\n" + success);
    Reject(["A"], 1, failure + "\n" + failure);
    Reject(["A"], 1, success + "\n" + failure);
    Reject(["A"], 0, success + "\n" + success.Replace("A", "B", StringComparison.Ordinal));
    Reject(["A"], 1, success + "\n" + failure.Replace("A", "B", StringComparison.Ordinal));
    Reject(["A", "B"], 0, success);
    Reject(["A"], 1, success);
    Reject(["A"], 0, failure);
    Reject(["A"], 0, "");
    Reject(["A"], 0, success.Replace("A", "a", StringComparison.Ordinal));
    Reject([], 0, success);
    Reject([], 1, "");
    Reject(["A", "A"], 0, success);
    Reject([""], 0, "");
    Reject([" "], 0, "");
    try { SeparateReplayTargets(["A", "A"]); throw new Exception("Duplicate input targets accepted"); }
    catch (InvalidDataException) { }
    foreach (var malformed in new[]
    {
        "{", "{}", "{invalid", success + " trailing", """{"milliseconds":0}""",
        """{"module":"A"}""", """{"module":null,"milliseconds":0}""",
        """{"module":"","milliseconds":0}""", """{"module":" ","milliseconds":0}""",
        """{"module":"A","module":"A","milliseconds":0}""",
        """{"module":"A","mo\u0064ule":"A","milliseconds":0}""",
        """{"module":"A","milliseconds":0,"milliseconds":1}""",
        """{"module":"A","error":"one","error":"two"}""",
        """{"module":"A","milliseconds":0,"extra":true}""",
        """{"module":"A","milliseconds":0,"error":"rejected"}"""
    }) Reject(["A"], 0, success + "\n" + malformed);
    foreach (var invalidElapsed in new[] { "-1", "1.5", "1.0", "1e0", "18446744073709551616",
        "null", "true", "\"1\"", "[]", "{}" })
        Reject(["A"], 0, "{\"module\":\"A\",\"milliseconds\":" + invalidElapsed + "}");
    foreach (var invalidError in new[] { "null", "true", "1", "\"\"", "[]", "{}" })
        Reject(["A"], 1, "{\"module\":\"A\",\"error\":" + invalidError + "}");
    Console.WriteLine("PASS separate replay exact records, target coverage, field types and exit status");

    long previousBytes = 0;
    double previousMilliseconds = 0;
    // Each sample parses the same number of records, so the larger sizes stay well under a second.
    const int recordsPerSample = 65536;
    // A parse that allocates a line array, line strings or field-name strings exceeds this per record.
    const int maxBytesPerRecord = 256;
    foreach (int count in new[] { 256, 1024, 4096, 16384 })
    {
        var targets = Enumerable.Range(0, count).Select(index => "Module" + index).ToArray();
        var output = string.Join('\n', targets.Select(module => JsonSerializer.Serialize(new { module, milliseconds = 1 })));
        for (int warm = 0; warm < 4; warm++) ParseSeparateReplayResults(targets, 0, output);
        long before = GC.GetAllocatedBytesForCurrentThread();
        ParseSeparateReplayResults(targets, 0, output);
        long bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        int repetitions = recordsPerSample / count;
        // The fastest sample is the parse itself; slower samples add scheduler and collector delays.
        double milliseconds = double.MaxValue;
        for (int sample = 0; sample < 9; sample++)
        {
            var timer = Stopwatch.StartNew();
            for (int repeat = 0; repeat < repetitions; repeat++) ParseSeparateReplayResults(targets, 0, output);
            milliseconds = Math.Min(milliseconds, timer.Elapsed.TotalMilliseconds / repetitions);
        }
        if (bytes > (long)maxBytesPerRecord * count)
            throw new InvalidOperationException(
                $"Separate replay parsing allocated {bytes} bytes for {count} records, " +
                $"over {maxBytesPerRecord} per record");
        if (previousBytes != 0 && (bytes > previousBytes * 6 || milliseconds > previousMilliseconds * 6 + 1))
            throw new InvalidOperationException(
                $"Separate replay parsing exceeded its growth bound at {count}: {bytes} allocated bytes and " +
                $"{milliseconds:F3} ms against {previousBytes} bytes and {previousMilliseconds:F3} ms");
        Console.WriteLine($"PASS replay parsing {count}: {bytes} allocated bytes, {milliseconds:F3} ms");
        previousBytes = bytes;
        previousMilliseconds = milliseconds;
    }
}

void CheckReplayDiagnostics()
{
    const string accepted = """{"module":"A","outcome":"accepted"}""";
    const string rejected =
        """{"module":"A","outcome":"rejected","declaration":"A.bad","kind":"declTypeMismatch"}""";
    const string complete = """{"complete":true}""";
    void Reject(string[] targets, int code, string output)
    {
        try { ParseReplayDiagnostics(targets, code, output); }
        catch (InvalidDataException) { return; }
        throw new InvalidOperationException("Invalid diagnostic accepted: " + output);
    }
    if (ParseReplayDiagnostics(["A"], 0, accepted + "\n" + complete).Count != 0 ||
        ParseReplayDiagnostics(["A"], 0, rejected + "\n" + complete)["A"].Declaration != "A.bad" ||
        ParseReplayDiagnostics([], 0, complete).Count != 0 ||
        ParseReplayDiagnostics(["A"], 0,
            """{"module":"A","outcome":"unavailable","error":"resource"}""" + "\n" + complete).Count != 0)
        throw new InvalidOperationException("Valid diagnostic rejected");
    Reject(["A"], 1, rejected + "\n" + complete);
    Reject(["A"], 0, rejected);
    Reject(["A"], 0, complete + "\n" + rejected);
    Reject(["A"], 0, rejected + "\n" + rejected + "\n" + complete);
    Reject(["A", "B"], 0, rejected + "\n" + complete);
    Reject(["B"], 0, rejected + "\n" + complete);
    Reject(["A", "A"], 0, rejected + "\n" + complete);
    foreach (var kind in new[] { "\"0\"", "0", "null", "\"other\"", "\"interrupted\"",
        "\"deterministicTimeout\"", "\"excessiveMemory\"", "\"deepRecursion\"" })
        Reject(["A"], 0, rejected.Replace("\"declTypeMismatch\"", kind, StringComparison.Ordinal) +
            "\n" + complete);
    foreach (var record in new[] { "{", "{}", "{\"complete\":false}",
        accepted.Replace("\"A\"", "null", StringComparison.Ordinal),
        rejected.Replace("\"A.bad\"", "\"\"", StringComparison.Ordinal),
        rejected.Replace("\"kind\":", "\"kind\":0,\"kind\":", StringComparison.Ordinal),
        accepted[..^1] + ",\"extra\":true}" })
        Reject(["A"], 0, record + "\n" + complete);
    long previous = 0;
    foreach (int count in new[] { 64, 256, 1024 })
    {
        var targets = Enumerable.Range(0, count).Select(index => "M" + index).ToArray();
        var output = string.Join('\n', targets.Select(module => JsonSerializer.Serialize(new
        {
            module, outcome = "rejected", declaration = module + ".bad", kind = "declTypeMismatch"
        }))) + "\n" + complete;
        ParseReplayDiagnostics(targets, 0, output);
        var before = GC.GetAllocatedBytesForCurrentThread();
        if (ParseReplayDiagnostics(targets, 0, output).Count != count) throw new Exception("Lost records");
        var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        if (previous != 0 && bytes > previous * 6) throw new Exception("Diagnostic parsing allocation growth");
        Console.WriteLine($"PASS diagnostic parser {count}: {bytes} allocated bytes");
        previous = bytes;
    }
}

void Compile(string module, string source)
{
    var path = Path.Combine(root, module + ".lean");
    File.WriteAllText(path, source);
    Run([verification.LeanExecutable, "--root=" + root, "-o", Path.Combine(root, module + ".olean"), path],
        root, root, environment: environment);
}

// A <- B <- C, plus a forged module whose theorem skipped kernel checking.
Compile("JointA", "theorem JointA.base : 1 + 1 = 2 := rfl\n");
Compile("JointB", "import JointA\ntheorem JointB.step : 1 + 1 = 2 := JointA.base\n");
Compile("JointC", "import JointB\ntheorem JointC.top : 1 + 1 = 2 := JointB.step\n");
Compile("JointMissingImport", "import JointA\ntheorem JointMissingImport.valid : True := trivial\n");
File.WriteAllText(Path.Combine(root, "JointMalformed.olean"), "Not an olean");
Compile("JointForged", """
    import Lean
    set_option debug.skipKernelTC true
    run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
      name := `JointForged.false
      levelParams := []
      type := Lean.mkConst ``False
      value := Lean.mkConst ``True.intro
    })
    """);

// JointE1 and JointE2 each store their own on-demand JointD.f equation lemmas.
Compile("JointD", "def JointD.f : Nat -> Nat\n  | 0 => 1\n  | n + 1 => n\n");
Compile("JointE1", "import JointD\ntheorem JointE1.use (n : Nat) : JointD.f (n + 1) = n := JointD.f.eq_2 n\n");
Compile("JointE2", "import JointD\ntheorem JointE2.use (n : Nat) : JointD.f (n + 1) = n := JointD.f.eq_2 n\n");
// Unrelated modules declaring one name with different statements.
Compile("JointClash1", "theorem JointClash.same : True := trivial\n");
Compile("JointClash2", "theorem JointClash.same : 1 = 1 := rfl\n");
Compile("JointClean", "theorem JointDuplicate.same : True := True.intro\n");
Compile("JointUnapproved", "axiom JointUnapproved.oracle : True\n" +
    "theorem JointDuplicate.same : True := JointUnapproved.oracle\n");
// A same-named predicate of another module is no contract, so stating it is no refutation.
Compile("JointOwnRefuted", "def CIL.Safety.MethodContract.Refuted : Prop := True\n" +
    "theorem JointOwnRefuted.test : CIL.Safety.MethodContract.Refuted := trivial\n");
Compile("JointVisible", "theorem JointVisible.correctness : True := True.intro\n");
Compile("JointHidden", """
    import Lean
    set_option debug.skipKernelTC true
    run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
      name := `JointHidden.correctness
      levelParams := []
      type := Lean.mkConst ``True
      value := Lean.mkConst `JointVisible.correctness
    })
    """);

// Deferred kernel checks: a forged definition under a well-typed theorem, and a well-typed
// theorem resting on a forged one, must still fail replay.
Compile("JointForgedDefinition", """
    import Lean
    set_option debug.skipKernelTC true
    run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl {
      name := `JointForgedDefinition.value
      levelParams := []
      type := Lean.mkConst ``Nat
      value := Lean.mkConst ``Bool.true
      hints := .abbrev
      safety := .safe
    })
    """);
Compile("JointForgedDefinitionUse", "import JointForgedDefinition\n" +
    "theorem JointForgedDefinitionUse.same : JointForgedDefinition.value = JointForgedDefinition.value := rfl\n");
Compile("JointForgedChain", "import JointForged\ntheorem JointForgedChain.use : False := JointForged.false\n");

void CheckIsolatedDiagnostics()
{
    if (args is not ["--diagnostics-only"]) verification.Library(Inputs(At("CIL.lean")));
    var executable = args is ["--diagnostics-only"]
        ? At(".lake/build/bin/leancil-audit" + (OperatingSystem.IsWindows() ? ".exe" : ""))
        : verification.CheckedAuditExecutable();
    string[] targets = ["JointA", "JointForged", "JointForgedDefinition", "JointForgedChain",
        "JointHidden", "JointMalformed"];
    var input = Path.Combine(root, "diagnostic-targets.json");
    File.WriteAllText(input, JsonSerializer.Serialize(targets));
    var result = Execute([executable, "--diagnose-replay", input], root, root, environment: environment);
    var rejected = ParseReplayDiagnostics(targets, result.Code, result.Stdout);
    if (rejected.Count != 3 || rejected["JointForged"].Declaration != "JointForged.false" ||
        rejected["JointForgedDefinition"].Declaration != "JointForgedDefinition.value" ||
        rejected["JointHidden"].Declaration != "JointHidden.correctness")
        throw new InvalidOperationException("Isolated diagnostic ownership changed: " + result.Output);
    Console.WriteLine("PASS isolated typed rejection, imported dependency exclusion and unavailable olean");
}

if (args is ["--diagnostics-only"])
{
    CheckIsolatedDiagnostics();
    return;
}

void CheckFusedReplay()
{
    var shadow = Path.Combine(root, "Shadow");
    Directory.CreateDirectory(shadow);
    File.WriteAllText(Path.Combine(shadow, "Init.olean"), "Not an olean");
    if (verification.library is null) verification.Library(Inputs(At("CIL.lean")));
    var library = Path.Combine(verification.library!, ".lake/build/lib/lean");
    var leanPath = shadow + Path.PathSeparator + root + Path.PathSeparator + library;
    // A refutation of the library's contract predicate needs the library on the search path.
    var refutationSource = Path.Combine(root, "JointRefutation.lean");
    File.WriteAllText(refutationSource, """
        import CIL.Safety.MethodContract
        open CIL.Safety
        def JointRefutation.returns : MethodContract Unit where
          args _ := []
          pre _ _ := True
          footprint _ := []
          post _ _ _ _ := True
        theorem JointRefutation.test : JointRefutation.returns.Refuted [] 0 :=
          .of_fault (input := ()) (initial := Memory.empty) (observed := 1)
            (fault := ⟨0, 0, .invalidState⟩) trivial (by decide) rfl
        """);
    Run([verification.LeanExecutable, "--root=" + root, "-o", Path.Combine(root, "JointRefutation.olean"),
        refutationSource], root, root + Path.PathSeparator + library, environment: environment);

    System.Text.Json.JsonElement Audit(string[] targets, string module, string theorem, bool fused,
        bool rejected = false, bool metadata = false, string[]? axioms = null)
    {
        var request = Path.Combine(root, "fused-request.json");
        var result = Path.Combine(root, "fused-result.json");
        var specification = new Dictionary<string, object>
        {
            ["modules"] = new[] { module }, ["replayTargets"] = targets,
            ["theorems"] = new[]
            {
                new { name = theorem, axioms = axioms ?? [], statement = true, refutation = true }
            }
        };
        if (metadata)
            specification["namespaces"] = new { prefixes = new[] { "JointA" }, axioms = Array.Empty<string>() };
        File.WriteAllText(request, System.Text.Json.JsonSerializer.Serialize(specification));
        Run([verification.CheckedAuditExecutable(), request, result], root, leanPath, environment: environment);
        var audited = System.Text.Json.JsonSerializer.Deserialize<System.Text.Json.JsonElement>(
            File.ReadAllText(result));
        if (audited.GetProperty("fused").GetBoolean() != fused ||
            !audited.GetProperty("replayed").EnumerateArray().Select(value => value.GetString()).SequenceEqual(targets))
            throw new InvalidOperationException("Fused audit selected the wrong environment or replay targets");
        var checkedTheorem = audited.GetProperty("theorems")[0];
        if (checkedTheorem.TryGetProperty("error", out var error) != rejected ||
            (rejected && !error.GetString()!.Contains("JointUnapproved.oracle")))
            throw new InvalidOperationException("Fused audit did not preserve the theorem's own axiom closure");
        return audited;
    }

    Audit(["JointA"], "JointA", "JointA.base", fused: true);
    Audit(["JointA"], "JointA", "JointA.base", fused: false, metadata: true);
    Console.WriteLine("PASS fused and metadata fallback audit cannot shadow toolchain modules");
    Audit(["JointClean", "JointUnapproved"], "JointUnapproved", "JointDuplicate.same",
        fused: false, rejected: true);
    Audit(["JointUnapproved", "JointClean"], "JointUnapproved", "JointDuplicate.same",
        fused: false, rejected: true);
    Console.WriteLine("PASS duplicate theorem bodies retain their own rejected axiom closure in both orders");
    // The library's refutation lemmas use the two standard axioms.
    var refutation = Audit(["JointRefutation"], "JointRefutation", "JointRefutation.test", fused: false,
        axioms: ["propext", "Quot.sound"]);
    if (refutation.GetProperty("theorems")[0].GetProperty("refutes").GetProperty("line").GetInt32() != 8)
        throw new InvalidOperationException("Fused fallback lost the refutation's source location");
    var own = Audit(["JointOwnRefuted"], "JointOwnRefuted", "JointOwnRefuted.test", fused: false);
    if (own.GetProperty("theorems")[0].TryGetProperty("refutes", out var ownRefutes) &&
        ownRefutes.ValueKind != JsonValueKind.Null)
        throw new InvalidOperationException("A same-named predicate of another module counted as a refutation");
    Console.WriteLine("PASS refutation audit retains original source locations and refuses same-named predicates");

    var forgedRequest = Path.Combine(root, "forged-fused.json");
    File.WriteAllText(forgedRequest, """
        {"modules":["JointForged"],"replayTargets":["JointForged"],
         "theorems":[{"name":"JointForged.false","axioms":[]}]}
        """);
    var forged = Execute([verification.CheckedAuditExecutable(), forgedRequest,
        Path.Combine(root, "forged-fused-result.json")], root, leanPath, environment: environment);
    if (forged.Code == 0 || !(forged.Stdout + forged.Stderr).Contains("while replaying declaration"))
        throw new InvalidOperationException("Fused replay accepted a forged theorem body");
    Console.WriteLine("PASS fused replay rejects forged theorem bodies before auditing");

    void Scoped(string[] targets, string[] modules, object[] requests, bool duplicate = false)
    {
        var request = Path.Combine(root, "scoped-request.json");
        var result = Path.Combine(root, "scoped-result.json");
        File.WriteAllText(request, System.Text.Json.JsonSerializer.Serialize(new
        {
            modules, replayTargets = targets, theorems = requests
        }));
        var run = Execute([verification.CheckedAuditExecutable(), request, result], root, leanPath,
            environment: environment);
        if (duplicate)
        {
            if (run.Code == 0 || !run.Output.Contains("requires unique replay declarations"))
                throw new InvalidOperationException("Scoped replay accepted ambiguous theorem ownership");
            return;
        }
        if (run.Code != 0) throw new InvalidOperationException(run.Output);
        var audited = System.Text.Json.JsonSerializer.Deserialize<System.Text.Json.JsonElement>(
            File.ReadAllText(result));
        var theorems = audited.GetProperty("theorems").EnumerateArray().ToArray();
        if (!audited.GetProperty("fused").GetBoolean() || theorems[0].TryGetProperty("error", out _) ||
            (theorems.Length > 1 && !theorems[1].GetProperty("error").GetString()!.Contains("import closure")))
            throw new InvalidOperationException("Scoped fused audit lost request-local visibility");
    }

    object Scope(string theorem, params string[] modules) =>
        new { name = theorem, axioms = Array.Empty<string>(), allowedModules = modules };
    Scoped(["JointA", "JointB", "JointC"], ["JointB", "JointC"],
        [Scope("JointB.step", "JointA", "JointB"), Scope("JointC.top", "JointA", "JointB")]);
    Scoped(["JointC"], ["JointC"], [Scope("JointA.base", "JointA")]);
    Scoped(["JointVisible", "JointHidden"], ["JointVisible", "JointHidden"],
        [Scope("JointVisible.correctness", "JointVisible"), Scope("JointHidden.correctness", "JointHidden")]);
    foreach (var targets in new[] { new[] { "JointClean", "JointUnapproved" },
        new[] { "JointUnapproved", "JointClean" } })
        Scoped(targets, targets, [Scope("JointDuplicate.same", "JointClean")], duplicate: true);
    Console.WriteLine("PASS fused scopes preserve target/external owners and reject duplicate proof bodies");
}

void CheckReplays(bool native)
{
    if (native) verification.Library(Inputs(At("CIL.lean")));
    Console.WriteLine(native ? "CHECK native joint replay" : "CHECK bootstrap joint replay");
    if (!verification.ReplayModulesJointly(root, ["JointA", "JointB", "JointC"], root, "Joint replay check"))
        throw new InvalidOperationException("Import-closed targets did not replay jointly");
    Console.WriteLine("PASS import-closed targets replay jointly");

    if (verification.ReplayConsumerModules(root, ["JointC"], root).Count != 0)
        throw new InvalidOperationException("Single target with external dependencies failed replay");
    var singleFailure = verification.ReplayConsumerModules(root, ["JointForged"], root);
    if (singleFailure.Keys.SingleOrDefault() != "JointForged" ||
        !singleFailure["JointForged"].Contains("while replaying declaration"))
        throw new InvalidOperationException("Single-target forgery was not rejected and attributed");
    Console.WriteLine("PASS single target replays with external dependencies and rejects forged declarations");

    if (!verification.ReplayModulesJointly(root, ["JointD", "JointE1", "JointE2"], root, "Joint replay check"))
        throw new InvalidOperationException("Identical on-demand equation lemmas blocked joint replay");
    Console.WriteLine("PASS identical on-demand equation lemmas in several targets replay jointly");

    Dictionary<string, string> CheckFallback(string[] targets, string rejection)
    {
        var previousTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
        var trace = ConsumerTraceDirectory.Create(root, "Fallback");
        try
        {
            Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
            var failures = verification.ReplayConsumerModules(root, targets, root);
            var records = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
                .Select(line => System.Text.Json.JsonSerializer.Deserialize<System.Text.Json.JsonElement>(line))
                .ToArray();
            var joint = records.Single(item => item.GetProperty("stage").GetString() ==
                "Joint kernel replay of consumer proof and dependencies");
            if (joint.GetProperty("exitCode").GetInt32() == 0 ||
                !File.ReadAllText(Path.Combine(trace, joint.GetProperty("transcript").GetString()!))
                    .Contains(rejection, StringComparison.Ordinal) ||
                records.Count(item => item.GetProperty("stage").GetString() ==
                    "Kernel replay of consumer proof and dependencies") != 1)
                throw new InvalidOperationException("Expected joint rejection followed by isolated replay: " + rejection);
            return failures;
        }
        finally { Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousTrace); }
    }

    if (CheckFallback(["JointClash1", "JointClash2"], "declared by more than one replay target").Count != 0)
        throw new InvalidOperationException("Per-module fallback rejected valid modules");
    Console.WriteLine("PASS one name with different statements falls back to per-module replay");

    // JointA arrives through the untargeted JointB, so its theorems would be skipped as duplicates.
    if (CheckFallback(["JointA", "JointC"], "is already imported").Count != 0)
        throw new InvalidOperationException("Per-module fallback rejected valid modules");
    Console.WriteLine("PASS target loaded through an untargeted import falls back to per-module replay");

    if (verification.ReplayModulesJointly(root, ["JointA", "JointForged"], root, "Joint replay check"))
        throw new InvalidOperationException("Joint replay accepted a forged declaration");
    var dependency = Path.Combine(root, "JointA.olean");
    File.Move(dependency, dependency + ".hidden");
    try
    {
        var failures = verification.ReplayConsumerModules(root,
            ["JointVisible", "JointForged", "JointHidden", "JointMalformed", "JointAbsent", "JointMissingImport"], root);
        if (!failures.Keys.Order(StringComparer.Ordinal).SequenceEqual(
                new[] { "JointAbsent", "JointForged", "JointHidden", "JointMalformed", "JointMissingImport" }) ||
            !failures["JointForged"].Contains("while replaying declaration"))
            throw new InvalidOperationException("Isolated replay lost failure attribution: " +
                string.Join(", ", failures.Keys));
    }
    finally { File.Move(dependency + ".hidden", dependency); }
    Console.WriteLine("PASS isolated replay rejects forged and hidden declarations and malformed or missing imports");
    string[] forgedDefinition = ["JointForgedDefinition", "JointForgedDefinitionUse"];
    var definitionFailures = CheckFallback(forgedDefinition, "JointForgedDefinition.value");
    if (definitionFailures.Keys.SingleOrDefault() != "JointForgedDefinition" ||
        !definitionFailures["JointForgedDefinition"].Contains("JointForgedDefinition.value"))
        throw new InvalidOperationException("Forged definition was not rejected by name: " +
            string.Join(", ", definitionFailures.Keys));
    if (verification.ReplayModulesJointly(root, ["JointForged", "JointForgedChain"], root, "Joint replay check"))
        throw new InvalidOperationException("Joint replay accepted a valid theorem resting on a forged one");
    Console.WriteLine("PASS concurrent checks reject forged definitions and forged theorem dependencies");
}

void CheckReplayedClosures()
{
    var source = Path.Combine(root, "JointContract.lean");
    File.WriteAllText(source, """
        import CIL.Safety.MethodContract
        def CIL.Forged.expected : Nat := 7
        namespace JointContract
        private def expected : Nat := CIL.Forged.expected
        def contract : CIL.Safety.MethodContract Unit Unit where
          args _ := []
          results _ := []
          pre _ _ := True
          footprint _ := []
          post _ _ _ _ := expected = 7
        axiom unapproved : Prop
        def badContract : CIL.Safety.MethodContract Unit Unit where
          args _ := []
          results _ := []
          pre _ _ := True
          footprint _ := []
          post _ _ _ _ := unapproved
        theorem valid : True := trivial
        #print axioms valid
        end JointContract
        """);
    var leanPath = root + Path.PathSeparator + Path.Combine(verification.library!, ".lake/build/lib/lean");
    Run([verification.LeanExecutable, "--root=" + root, "-o", Path.ChangeExtension(source, ".olean"), source],
        root, leanPath, environment: environment);
    var results = new List<System.Text.Json.JsonElement>();
    foreach (var replay in new[] { false, true })
    {
        var request = new Dictionary<string, object>
        {
            ["modules"] = new[] { "JointContract" },
            ["theorems"] = new[] { new { name = "JointContract.valid", axioms = Array.Empty<string>() } },
            ["closures"] = new[] { new { name = "JointContract.contract" }, new { name = "JointContract.badContract" } }
        };
        if (replay) request["replayTargets"] = new[] { "JointContract" };
        var input = Path.Combine(root, "closure-request.json");
        var output = Path.Combine(root, "closure-result.json");
        File.WriteAllText(input, System.Text.Json.JsonSerializer.Serialize(request));
        Run([verification.CheckedAuditExecutable(), input, output], root, leanPath, environment: environment);
        var result = System.Text.Json.JsonSerializer.Deserialize<System.Text.Json.JsonElement>(File.ReadAllText(output));
        if (replay && !result.GetProperty("fused").GetBoolean())
            throw new InvalidOperationException("Contract closure unnecessarily reimported replayed modules");
        results.Add(result.GetProperty("closures"));
    }
    if (results[0].GetRawText() != results[1].GetRawText() ||
        !results[1][0].GetProperty("canonical").GetString()!.Contains("Forged", StringComparison.Ordinal) ||
        !results[1][1].GetProperty("error").GetString()!.Contains("unapproved", StringComparison.Ordinal))
        throw new InvalidOperationException("Replayed ownership changed closure bytes or trusted a namespace prefix");
    Console.WriteLine("PASS replayed contract closures match imported metadata and reject unapproved axioms");
}

void CheckReplayedInterfaces()
{
    var leanPath = root + Path.PathSeparator + Path.Combine(verification.library!, ".lake/build/lib/lean");
    foreach (var (module, declarations, rejected) in new[]
    {
        ("JointInterface", "private def hidden : Nat := 7\ndef value : Nat := hidden", false),
        ("JointUnusedInterface", "private axiom unused : Prop\ndef value : Nat := 7", true),
        ("JointSpoofedInterface", "axiom CIL.Spoofed.unused : Prop\ndef value : Nat := 7", true),
        ("JointModuleInterface", "private def hidden : Nat := 7\npublic def value : Nat := hidden", false),
        ("JointModuleUnusedInterface", "private axiom unused : Prop\npublic def value : Nat := 7", true),
        ("JointEquationInterface", "def sequence : Nat → Nat | 0 => 1 | n + 1 => n\n" +
            "theorem equation (n : Nat) : sequence (n + 1) = n := sequence.eq_2 n\n#print axioms equation", false)
    })
    {
        var source = Path.Combine(root, module + ".lean");
        var header = module.StartsWith("JointModule", StringComparison.Ordinal)
            ? "module\n" : "";
        File.WriteAllText(source, header + declarations + "\n");
        Run([verification.LeanExecutable, "--root=" + root, "-o", Path.ChangeExtension(source, ".olean"), source],
            root, leanPath, environment: environment);
        var verdicts = new List<string>();
        foreach (var replay in new[] { false, true })
        {
            var request = new Dictionary<string, object>
            {
                ["modules"] = new[] { module },
                ["interfaces"] = new[] { module }
            };
            if (replay) request["replayTargets"] = new[] { module };
            var input = Path.Combine(root, "interface-request.json");
            var output = Path.Combine(root, "interface-result.json");
            File.WriteAllText(input, System.Text.Json.JsonSerializer.Serialize(request));
            Run([verification.CheckedAuditExecutable(), input, output], root, leanPath, environment: environment);
            var result = System.Text.Json.JsonSerializer.Deserialize<System.Text.Json.JsonElement>(
                File.ReadAllText(output));
            if (replay && !result.GetProperty("fused").GetBoolean())
                throw new InvalidOperationException("Interface validation unnecessarily reimported replayed modules");
            var verdict = result.GetProperty("interfaces");
            if (verdict.TryGetProperty("error", out _) != rejected)
                throw new InvalidOperationException("Interface declaration validation changed: " + module);
            verdicts.Add(verdict.GetRawText());
        }
        if (verdicts[0] != verdicts[1])
            throw new InvalidOperationException("Replayed interface verdict differs from imported metadata: " + module);
    }
    var wrapper = Path.Combine(root, "JointInterfaceWrapper.lean");
    File.WriteAllText(wrapper, "import JointInterface\n");
    Run([verification.LeanExecutable, "--root=" + root, "-o", Path.ChangeExtension(wrapper, ".olean"), wrapper],
        root, leanPath, environment: environment);
    var importedInput = Path.Combine(root, "imported-interface-request.json");
    var importedOutput = Path.Combine(root, "imported-interface-result.json");
    File.WriteAllText(importedInput, System.Text.Json.JsonSerializer.Serialize(new
    {
        modules = new[] { "JointInterfaceWrapper" },
        interfaces = new[] { "JointInterface" },
        replayTargets = new[] { "JointInterfaceWrapper" }
    }));
    Run([verification.CheckedAuditExecutable(), importedInput, importedOutput], root, leanPath,
        environment: environment);
    var imported = System.Text.Json.JsonSerializer.Deserialize<System.Text.Json.JsonElement>(
        File.ReadAllText(importedOutput));
    if (imported.GetProperty("fused").GetBoolean() || imported.GetProperty("interfaces").TryGetProperty("error", out _))
        throw new InvalidOperationException("Untargeted imported interface lost metadata fallback");
    Console.WriteLine("PASS replayed interfaces check private and unused declarations despite namespace spoofing");
}

var originalReplayByte = verification.bootstrapReplaySource[0];
try
{
    verification.bootstrapReplaySource[0] ^= 1;
    try
    {
        verification.ReplayModulesJointly(root, ["JointA"], root, "Changed replay source check");
        throw new InvalidOperationException("Changed bootstrap replay source was accepted");
    }
    catch (InvalidDataException error) when (error.Message.Contains("Kernel replay source changed")) { }
}
finally { verification.bootstrapReplaySource[0] = originalReplayByte; }
Console.WriteLine("PASS bootstrap replay source must match its initial snapshot");

if (args is ["--audit-only"]) verification.Library(Inputs(At("CIL.lean")));
else
{
    CheckReplays(native: false);
    CheckReplays(native: true);
}
CheckIsolatedDiagnostics();
CheckFusedReplay();
CheckReplayedClosures();
CheckReplayedInterfaces();
