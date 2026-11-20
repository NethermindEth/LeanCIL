#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs

using System.Reflection;
using System.Runtime.InteropServices;

var runtimeFixture = Assembly.LoadFrom(At("Examples/Assembly/bin/Examples.dll"))
    .GetType("Examples.StackAllocation", throwOnError: true)!;
foreach (var (method, inputs, expected) in new (string, object[], int)[]
{
    ("ZeroInitialized", [], 0), ("WrittenBeforeRead", [42], 42),
    ("FillAndRead", [4, 42], 42), ("Length", [0], 0)
})
{
    if (!Equals(runtimeFixture.GetMethod(method)!.Invoke(null, inputs), expected))
        throw new Exception("Runtime stack allocation differed: " + method);
}
Console.WriteLine($"PASS runtime stack allocation: .NET {Environment.Version}, " +
    RuntimeInformation.ProcessArchitecture);

var root = At("artifacts/StackAllocation");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.Safety.Execution");
CheckLeanFixture("Tests.StackAllocation");

foreach (var (name, signature, arguments, budget, predicate) in new[]
{
    ("zero", "ZeroInitialized()", "[]", 32,
        "result.map Prod.snd = .ok [.scalar (.i32 0)]"),
    ("empty", "Length(System.Int32)", "[.scalar (.i32 0)]", 0,
        "result.map Prod.snd = .ok [.scalar (.i32 0)]"),
    ("written", "WrittenBeforeRead(System.Int32)", "[.scalar (.i32 42)]", 32,
        "result.map Prod.snd = .ok [.scalar (.i32 42)]"),
    ("fill", "FillAndRead(System.Int32,System.Int32)", "[.scalar (.i32 4), .scalar (.i32 42)]", 32,
        "result.map Prod.snd = .ok [.scalar (.i32 42)]"),
    ("uninitialized", "UninitializedRead()", "[]", 32,
        "match result with | .error ⟨_, _, .memory .uninitialized _ _⟩ => True | _ => False"),
    ("escaped", "EscapingStorage()", "[]", 32,
        "match result with | .error ⟨_, _, .memory .expiredLifetime _ _⟩ => True | _ => False"),
    ("budget", "ZeroInitialized()", "[]", 0,
        "(result.map Prod.snd).mapError (·.fault) = .error (.stackAllocationFailure 16 0)")
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", At("Examples/Assembly/bin/Examples.dll"),
        "StackAllocation::" + signature, output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun _ => none
          cells := fun _ _ => ⟨0, false⟩
          views := []
          nextIdentity := 0
          stackLimit := {{budget}} }
        private def result := CIL.Safety.invoke Extracted.program 160 0 {{arguments}} inputMemory
        theorem allocation_result : ({{predicate}}) := by first | rfl | exact True.intro
        #print axioms allocation_result
        """);
    evidence.Add(proof, "PASS compiled stack allocation: " + name);

    if (name == "fill")
    {
        using var module = Mono.Cecil.ModuleDefinition.ReadModule(runtimeFixture.Assembly.Location);
        var method = module.GetType("Examples.StackAllocation").Methods.Single(item => item.Name == "FillAndRead");
        var instructions = method.Body.Instructions;
        var constructorPc = instructions.IndexOf(instructions.Single(instruction =>
            instruction.OpCode.Code == Mono.Cecil.Cil.Code.Newobj));
        // The generated model fact names the constructor's width and capability, and each forgery changes one.
        foreach (var (operation, accepted) in new[]
        {
            (".spanFromReference 4 true", true), (".spanFromReference 8 true", false),
            (".spanFromReference 4 false", false)
        })
        {
            var stated = Path.Combine(root, "stated-span.lean");
            File.WriteAllText(stated, ForgeModelFact(source, constructorPc, $".memory ({operation})"));
            var checkedFact = Execute(["lake", "env", "lean", stated], cwd: FixturePackage());
            var passed = accepted
                ? checkedFact.Code == 0 && !checkedFact.Output.Contains("sorryAx", StringComparison.Ordinal)
                : checkedFact.Code != 0 && ModelFactMismatch(constructorPc)(checkedFact.Output);
            if (!passed) throw new Exception($"Stack span model fact {operation}: {checkedFact.Output}");
            Console.WriteLine($"PASS stack span model fact {(accepted ? "accepted" : "refused")}: {operation}");
        }
        // A modelled construction keeps its call, so its own operation in the call's place is refused.
        var forgedSpan = Path.Combine(root, "forged-span.lean");
        File.WriteAllText(forgedSpan,
            ForgeModelEmission(source, constructorPc, ".memory (.spanFromReference 4 true)"));
        var rejectedSpan = Execute(["lake", "env", "lean", forgedSpan], cwd: FixturePackage());
        if (rejectedSpan.Code == 0 || !rejectedSpan.Output.Contains("RuntimeModelsAgree", StringComparison.Ordinal))
            throw new Exception($"Substituted stack span instruction was not refused: {rejectedSpan.Output}");
        Console.WriteLine("PASS substituted stack span instruction refused");
    }

    if (name != "uninitialized") continue;
    // The method is defined from its decoder, so a method that claims localsinit is a forged decoder's value, which
    // no longer matches the closed definition's declared signature.
    if (!DecodedOriginal(source, 0).Contains("initLocals := false,", StringComparison.Ordinal))
        throw new Exception("Missing uninitialized allocation");
    var forged = Path.Combine(root, "forged-initialization.lean");
    File.WriteAllText(forged,
        ForgeDecodedMethod(source, 0, "declared := { method.declared with initLocals := true }"));
    var rejected = Execute(["lake", "env", "lean", forged], cwd: FixturePackage());
    if (rejected.Code == 0 || !rejected.Output.Contains("DeclaredValid", StringComparison.Ordinal))
        throw new Exception("Forged localsinit was not rejected by the Lean certificate: " + rejected.Output);
    Console.WriteLine("PASS forged stack initialization rejected");
}

evidence.Check(replay: false);
