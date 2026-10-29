#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs
#:include TailCallFixtures.cs

using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ConstrainedCalls");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "Tests.ConstrainedEvidence");

foreach (var (name, type, expected) in new[]
{
    ("Implicit", "CounterValue", 42),
    ("Explicit", "ExplicitCounterValue", 43),
    ("Mutating", "CounterValue", 43),
    ("MutatingExplicit", "ExplicitCounterValue", 44)
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"ConstrainedCalls::{name}(Examples.{type}&)", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨4, 1, []⟩, true, []⟩ else none
          cells := fun _ offset => ⟨if offset == 0 then 42 else 0, true⟩
          views := [⟨0, 0, 4, true, true⟩]
          nextIdentity := 1 }
        theorem constrained_result :
            (CIL.Safety.invoke Extracted.program 32 0 [.reference (.address ⟨0, 0⟩)]
              inputMemory).map Prod.snd = .ok [.scalar (.i32 {{expected}})] := rfl
        #print axioms constrained_result
        """);

    const string call = ".call 2 1";
    if (!source.Contains(call, StringComparison.Ordinal)) throw new Exception("Missing constrained call mutation target");
    var forged = Path.Combine(root, name + "-wrong-target.lean");
    // Keep the exact emitted definitions and constrained obligations; unrelated certificates
    // are covered by the complete positive extraction above, not recomputed for each mutation.
    var obligations = Regex.Matches(source,
        @"(?m)^theorem method\d+_constrained_validated : [^\r\n]+\r?$");
    var methodCount = Regex.Matches(source, @"(?m)^def method\d+ : Method :=").Count;
    if (methodCount == 0 || obligations.Count != methodCount)
        throw new Exception("Unexpected constrained obligation count");
    var declarations = Regex.Replace(source,
        @"(?m)^(?:@\[[^\r\n]*\] )?theorem [^\r\n]*(?:\r?\n[ \t]+[^\r\n]*)*\r?\n", "");
    declarations = Regex.Replace(declarations, @"(?m)^#print axioms [^\r\n]*\r?\n", "");
    var narrowed = declarations.Replace("end Extracted", string.Join("\n", obligations.Select(match =>
        match.Value + "\n#print axioms " + Regex.Match(match.Value, @"theorem (\w+)").Groups[1].Value)) +
        "\nend Extracted", StringComparison.Ordinal);
    var control = CheckedEvidenceControl(source, narrowed, obligations.Select(match =>
        Regex.Match(match.Value, @"theorem (\w+)").Groups[1].Value), 0);
    File.AppendAllText(proof, "\n" + control);
    evidence.Add(proof, "PASS compiled constrained call, certificate and obligation eligibility: " + name);
    File.WriteAllText(forged, narrowed.Replace(call, ".call 0 1", StringComparison.Ordinal));
    rejected.Add(forged, "PASS forged constrained target: " + name, "ConstrainedCallsValid");
}

AddTailCallFixtures(assembly, root, evidence, rejected);
evidence.Check();
rejected.Check();

foreach (var (mutation, marker) in new[]
{
    ("prefix", "adjacent concrete constrained receiver"),
    ("branch", "Branch bypasses constrained receiver prefix"),
    ("constraint", "Unsupported generic method constraints")
})
{
    var dll = Path.Combine(root, mutation + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.ConstrainedCalls").Methods.Single(method => method.Name == "Read");
        var prefix = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Constrained);
        if (mutation == "prefix") { prefix.OpCode = OpCodes.Nop; prefix.Operand = null; }
        else if (mutation == "branch")
            method.Body.GetILProcessor().InsertBefore(prefix, Instruction.Create(OpCodes.Br, prefix.Next));
        else module.GetType("Examples.CounterValue").Interfaces.Clear();
        module.Write(dll);
    }
    var extractionRejection = Execute(["dotnet", ExtractorPath, "extract", dll,
        "ConstrainedCalls::Implicit(Examples.CounterValue&)", Path.Combine(root, "Reject-" + mutation)]);
    if (extractionRejection.Code == 0 || !extractionRejection.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect constrained rejection: " + mutation + "\n" + extractionRejection.Output);
    Console.WriteLine("PASS constrained extraction rejection: " + mutation);
}
