#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ConsumerTraceDirectory.cs

using var verification = new Program();
var root = At("artifacts/JointReplay");
if (Directory.Exists(root)) Directory.Delete(root, true);
Directory.CreateDirectory(root);
var environment = new Dictionary<string, string> { ["LEAN_SYSROOT"] = verification.Toolchain };

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
Compile("JointRefutation", "def CIL.Safety.MethodContract.Holds : Prop := False\n" +
    "theorem JointRefutation.test : ¬ CIL.Safety.MethodContract.Holds := fun h => h\n");
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

void CheckFusedReplay()
{
    var shadow = Path.Combine(root, "Shadow");
    Directory.CreateDirectory(shadow);
    File.WriteAllText(Path.Combine(shadow, "Init.olean"), "Not an olean");
    var leanPath = shadow + Path.PathSeparator + root;

    System.Text.Json.JsonElement Audit(string[] targets, string module, string theorem, bool fused,
        bool rejected = false, bool metadata = false)
    {
        var request = Path.Combine(root, "fused-request.json");
        var result = Path.Combine(root, "fused-result.json");
        File.WriteAllText(request, System.Text.Json.JsonSerializer.Serialize(new
        {
            modules = new[] { module }, replayTargets = targets,
            theorems = new[] { new { name = theorem, axioms = Array.Empty<string>(), statement = true, refutation = true } },
            interfaces = metadata ? new[] { module } : Array.Empty<string>()
        }));
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
    var refutation = Audit(["JointRefutation"], "JointRefutation", "JointRefutation.test", fused: false);
    if (refutation.GetProperty("theorems")[0].GetProperty("refutes").GetProperty("line").GetInt32() != 2)
        throw new InvalidOperationException("Fused fallback lost the refutation's source location");
    Console.WriteLine("PASS refutation audit retains original source locations");

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

CheckReplays(native: false);
CheckReplays(native: true);
CheckFusedReplay();
CheckReplayedClosures();
