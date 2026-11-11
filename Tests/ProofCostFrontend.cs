#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// Failed imports and earlier commands must not publish a successful measurement.
var directory = At("artifacts/ProofCostFrontend");
Directory.CreateDirectory(directory);
var fixtures = new (string Name, string? Error, string Source)[]
{
    ("ValidCostImport", null, """
        import Lean

        theorem measured : True := True.intro
        #print axioms measured

        theorem auxiliary (value : Nat) : value = value := by
          as_aux_lemma => rfl
        #print axioms auxiliary

        theorem subsequent : True := True.intro
        #print axioms subsequent

        /-- error: expected cost diagnostic -/
        #guard_msgs in
        run_cmd Lean.logError "expected cost diagnostic"
        """),
    ("MissingCostImport", "ProofCostMissingImport", """
        import Lean
        import ProofCostMissingImport

        #guard_msgs in
        example : True := by trivial
        """),
    ("RejectedCostProof", "Type mismatch", """
        import Lean

        theorem rejected : False := by
          as_aux_lemma => exact True.intro

        theorem subsequent : True := True.intro
        #print axioms subsequent
        """),
    ("TimedOutCostProof", "maximum number of heartbeats", """
        import Lean

        set_option maxHeartbeats 1 in
        theorem timedOut (value : Nat) : value = value := by
          as_aux_lemma => rfl

        theorem subsequent : True := True.intro
        #print axioms subsequent
        """)
};
foreach (var (name, error, contents) in fixtures)
{
    var source = Path.Combine(directory, name + ".lean");
    var report = Path.Combine(directory, name + ".json");
    var compiled = Path.Combine(directory, name + ".olean");
    File.WriteAllText(source, contents);
    File.Delete(report);
    File.Delete(compiled);
    var result = Execute(["lake", "env", "lean", "--run", At("scripts/ProofCost.lean"),
        name, source, report, compiled]);
    if (error is not null)
    {
        if (result.Code == 0 || !result.Output.Contains(error, StringComparison.Ordinal) ||
            File.Exists(report) || File.Exists(compiled))
            throw new InvalidOperationException(name + " produced a measurement:\n" + result.Output);
    }
    else
    {
        if (result.Code != 0 || !File.Exists(compiled))
            throw new InvalidOperationException("A valid proof was not measured:\n" + result.Output);
        using var measured = JsonDocument.Parse(File.ReadAllText(report));
        var commands = measured.RootElement.GetProperty("commands").EnumerateArray().ToArray();
        foreach (var (label, constants) in new[] { ("measured", 1), ("auxiliary", 2), ("subsequent", 1) })
        {
            var command = commands.Single(command => command.GetProperty("label").GetString() == label);
            if (command.GetProperty("constants").GetInt32() != constants ||
                command.GetProperty("proofObjects").GetInt64() <= 0 ||
                command.GetProperty("kernelHeartbeats").GetInt64() <= 0)
                throw new InvalidOperationException("Missing theorem measurement: " + label);
        }
        if (commands.Where(command => command.GetProperty("kind").GetString() == "command")
            .Any(command => command.GetProperty("constants").GetInt32() != 0))
            throw new InvalidOperationException("A diagnostic command counted declarations again.");
    }
}
Console.WriteLine("PASS cost measurement includes auxiliary proofs and rejects failed imports and commands");
