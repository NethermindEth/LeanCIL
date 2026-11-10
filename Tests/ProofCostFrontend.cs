#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// A diagnostic assertion must not erase an import failure and publish an empty measurement.
var directory = At("artifacts/ProofCostFrontend");
Directory.CreateDirectory(directory);
foreach (var broken in new[] { false, true })
{
    var name = broken ? "MissingCostImport" : "ValidCostImport";
    var source = Path.Combine(directory, name + ".lean");
    var report = Path.Combine(directory, name + ".json");
    var compiled = Path.Combine(directory, name + ".olean");
    File.WriteAllText(source, broken ? """
        import Lean
        import ProofCostMissingImport

        #guard_msgs in
        example : True := by trivial
        """ : """
        import Lean

        /-- A valid module contributes a real theorem to the measurement. -/
        theorem measured : True := True.intro
        #print axioms measured
        """);
    File.Delete(report);
    File.Delete(compiled);
    var result = Execute(["lake", "env", "lean", "--run", At("scripts/ProofCost.lean"),
        name, source, report, compiled]);
    if (broken)
    {
        if (result.Code == 0 || !result.Output.Contains("ProofCostMissingImport", StringComparison.Ordinal) ||
            File.Exists(report) || File.Exists(compiled))
            throw new InvalidOperationException("A missing import produced a measurement:\n" + result.Output);
    }
    else
    {
        if (result.Code != 0 || !File.Exists(compiled))
            throw new InvalidOperationException("A valid proof was not measured:\n" + result.Output);
        using var measured = JsonDocument.Parse(File.ReadAllText(report));
        if (!measured.RootElement.GetProperty("commands").EnumerateArray().Any(command =>
            command.GetProperty("kind").GetString() == "theorem" &&
            command.GetProperty("constants").GetInt32() > 0))
            throw new InvalidOperationException("A valid measurement contains no theorem declarations.");
    }
}
Console.WriteLine("PASS cost measurement rejects missing imports before diagnostic assertions");
