#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs

using var verification = new Program();
var root = At("artifacts/JointReplay");
if (Directory.Exists(root)) Directory.Delete(root, true);
Directory.CreateDirectory(root);
var environment = new Dictionary<string, string> { ["LEAN_SYSROOT"] = verification.Toolchain };

void Compile(string module, string source)
{
    var path = Path.Combine(root, module + ".lean");
    File.WriteAllText(path, source);
    Run([verification.LeanExecutable, "--root=" + root, "-o", Path.Combine(root, module + ".olean"), path], root, root, environment: environment);
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

if (!verification.ReplayConsumerModulesJointly(root, ["JointA", "JointB", "JointC"], root))
    throw new InvalidOperationException("Import-closed targets did not replay jointly");
Console.WriteLine("PASS import-closed targets replay jointly");

// JointA arrives through the untargeted JointB, so its theorems would be skipped as duplicates.
if (verification.ReplayConsumerModulesJointly(root, ["JointA", "JointC"], root))
    throw new InvalidOperationException("Joint replay accepted a target loaded through an untargeted import");
if (verification.ReplayConsumerModules(root, ["JointA", "JointC"], root).Count != 0)
    throw new InvalidOperationException("Per-module fallback rejected valid modules");
Console.WriteLine("PASS target loaded through an untargeted import falls back to per-module replay");

if (verification.ReplayConsumerModulesJointly(root, ["JointA", "JointForged"], root))
    throw new InvalidOperationException("Joint replay accepted a forged declaration");
var failures = verification.ReplayConsumerModules(root, ["JointA", "JointForged"], root);
if (failures.Keys.SingleOrDefault() != "JointForged" || !failures["JointForged"].Contains("while replaying declaration"))
    throw new InvalidOperationException("Forged declaration was not attributed to its module: " + string.Join(", ", failures.Keys));
Console.WriteLine("PASS forged declaration rejected and attributed to its module");
