#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ConstrainedCalls");
Directory.CreateDirectory(root);
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.SymbolicExecution", "Tests.ConstrainedEvidence"]);

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
    var result = Run(["lake", "env", "lean", proof]);
    if (result.Contains("sorryAx", StringComparison.Ordinal)) throw new Exception("Untrusted constrained proof");
    Console.WriteLine("PASS compiled constrained call and certificate: " + name);

    const string call = ".call 2 1";
    if (!source.Contains(call, StringComparison.Ordinal)) throw new Exception("Missing constrained call mutation target");
    var forged = Path.Combine(root, name + "-wrong-target.lean");
    File.WriteAllText(forged, source.Replace(call, ".call 0 1", StringComparison.Ordinal));
    var rejected = Execute(["lake", "env", "lean", forged]);
    if (rejected.Code == 0 || !rejected.Output.Contains("ConstrainedCallsValid", StringComparison.Ordinal))
        throw new Exception("Forged constrained target was not rejected by its certificate: " + rejected.Output);
    Console.WriteLine("PASS forged constrained target: " + name);
}

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
    var rejected = Execute(["dotnet", ExtractorPath, "extract", dll,
        "ConstrainedCalls::Implicit(Examples.CounterValue&)", Path.Combine(root, "Reject-" + mutation)]);
    if (rejected.Code == 0 || !rejected.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect constrained rejection: " + mutation + "\n" + rejected.Output);
    Console.WriteLine("PASS constrained extraction rejection: " + mutation);
}
