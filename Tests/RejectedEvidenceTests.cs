#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs

var directory = At("artifacts/RejectedEvidenceTests");
Directory.CreateDirectory(directory);
var invalid = Path.Combine(directory, "Invalid.lean");
var valid = Path.Combine(directory, "Valid.lean");
File.WriteAllText(invalid, """
    import CIL
    namespace Extracted
    theorem invalid : (1 : Nat) = 2 := by decide +kernel
    end Extracted
    """.ReplaceLineEndings("\n") + "\n");
File.WriteAllText(valid, File.ReadAllText(invalid).Replace("= 2", "= 1", StringComparison.Ordinal));
var rejected = new RejectedEvidence(directory);
rejected.Add(invalid, "PASS isolated rejection", "decide", "is false");
rejected.Add(invalid, "PASS repeated generated names remain isolated", "decide", "is false");
rejected.Check();

var leaking = Path.Combine(directory, "Leaking.lean");
var independent = Path.Combine(directory, "Independent.lean");
File.WriteAllText(leaking, """
    import CIL
    namespace Extracted
    @[simp] theorem forged : (2 : Nat) = 1 := by decide +kernel
    end Extracted
    """ + "\n");
File.WriteAllText(independent, """
    import CIL
    namespace Extracted
    theorem stillFalse : (2 : Nat) = 1 := by simp
    end Extracted
    """ + "\n");
var isolation = new RejectedEvidence(directory);
isolation.Add(leaking, "PASS invalid attributed theorem is rejected", "decide", "is false");
isolation.Add(independent, "PASS failed theorem and its simp attribute do not escape", "unsolved goals");
isolation.Check();

foreach (var (path, marker) in new[] { (valid, "decide"), (invalid, "absent diagnostic marker") })
{
    var batch = new RejectedEvidence(directory);
    batch.Add(invalid, "PASS initial rejection", "decide");
    batch.Add(path, "Unexpected successful negative test", marker);
    try
    {
        batch.Check();
    }
    catch (InvalidOperationException exception) when (
        exception.Message.StartsWith("Expected rejection missing: " + Path.GetFullPath(path), StringComparison.Ordinal))
    {
        continue;
    }
    throw new InvalidOperationException("A neighboring rejection satisfied the wrong case: " + path);
}
Console.WriteLine("PASS valid evidence and mismatched diagnostics cannot borrow another case's rejection");

CheckEvidenceBatchFailures(valid);

static void CheckEvidenceBatchFailures(string original)
{
    var output = At("artifacts/RejectedEvidenceTests/GeneratedBatches");
    Directory.CreateDirectory(output);
    var source = File.ReadAllText(original);
    foreach (var (name, suffix, marker) in new[]
    {
        ("invalid-proof", "\ntheorem invalid_evidence : False := by decide +kernel\n" +
            "#print axioms invalid_evidence\n", "is false"),
        ("unchecked-declaration", """

            import Lean
            set_option debug.skipKernelTC true
            run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
              name := `forged_evidence
              levelParams := []
              type := Lean.mkConst ``False
              value := Lean.mkConst ``True.intro
            })
            #print axioms forged_evidence
            """, "declaration type mismatch")
    })
    {
        var directory = Path.Combine(output, "BatchFailure-" + name);
        Directory.CreateDirectory(directory);
        var invalid = Path.Combine(directory, "Invalid.lean");
        File.WriteAllText(invalid, source + suffix);
        var rejected = new GeneratedEvidence(directory);
        rejected.Add(original, "Unexpected success before rejected evidence", "invalid");
        rejected.Add(invalid, "Unexpected invalid evidence success", "invalid");
        var checker = Path.Combine(fixtureVerification!.Toolchain, "bin",
            OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
        var command = name == "unchecked-declaration" ? checker + " PositiveBatch" : "lake env lean";
        try
        {
            rejected.Check();
            throw new Exception("Invalid generated evidence batch was accepted: " + name);
        }
        catch (InvalidOperationException exception) when (
            exception.Message.Contains(marker, StringComparison.Ordinal) &&
            exception.Message.Contains(command, StringComparison.Ordinal) &&
            (name != "invalid-proof" || exception.Message.Contains("decide", StringComparison.Ordinal)))
        {
            Console.WriteLine("PASS evidence batch rejects " + name);
        }
    }
}
