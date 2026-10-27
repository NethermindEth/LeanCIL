#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

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

    if (verification.ReplayModulesJointly(root, ["JointClash1", "JointClash2"], root, "Joint replay check"))
        throw new InvalidOperationException("Joint replay merged one name with different statements");
    if (verification.ReplayConsumerModules(root, ["JointClash1", "JointClash2"], root).Count != 0)
        throw new InvalidOperationException("Per-module fallback rejected valid modules");
    Console.WriteLine("PASS one name with different statements falls back to per-module replay");

    // JointA arrives through the untargeted JointB, so its theorems would be skipped as duplicates.
    if (verification.ReplayModulesJointly(root, ["JointA", "JointC"], root, "Joint replay check"))
        throw new InvalidOperationException("Joint replay accepted a target loaded through an untargeted import");
    if (verification.ReplayConsumerModules(root, ["JointA", "JointC"], root).Count != 0)
        throw new InvalidOperationException("Per-module fallback rejected valid modules");
    Console.WriteLine("PASS target loaded through an untargeted import falls back to per-module replay");

    if (verification.ReplayModulesJointly(root, ["JointA", "JointForged"], root, "Joint replay check"))
        throw new InvalidOperationException("Joint replay accepted a forged declaration");
    var failures = verification.ReplayConsumerModules(root, ["JointA", "JointForged"], root);
    if (failures.Keys.SingleOrDefault() != "JointForged" ||
        !failures["JointForged"].Contains("while replaying declaration"))
        throw new InvalidOperationException("Forged declaration was not attributed to its module: " +
            string.Join(", ", failures.Keys));
    Console.WriteLine("PASS forged declaration rejected and attributed to its module");
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
