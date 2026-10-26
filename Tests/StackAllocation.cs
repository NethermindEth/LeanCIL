#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
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
        const string span = ".spanFromReference 4 true";
        if (!source.Contains(span, StringComparison.Ordinal)) throw new Exception("Missing span constructor");
        foreach (var replacement in new[] { ".spanFromReference 8 true", ".spanFromReference 4 false" })
        {
            var forgedSpan = Path.Combine(root, "forged-span.lean");
            File.WriteAllText(forgedSpan, source.Replace(span, replacement, StringComparison.Ordinal));
            var rejectedSpan = Execute(["lake", "env", "lean", forgedSpan], cwd: FixturePackage());
            if (rejectedSpan.Code == 0 || !rejectedSpan.Output.Contains("ScalarFlowValid", StringComparison.Ordinal))
                throw new Exception("Forged span constructor was not rejected: " + rejectedSpan.Output);
            Console.WriteLine("PASS forged stack span rejected: " + replacement);
        }
    }

    if (name != "uninitialized") continue;
    const string operation = ".stackAlloc false";
    if (!source.Contains(operation, StringComparison.Ordinal)) throw new Exception("Missing uninitialized allocation");
    var forged = Path.Combine(root, "forged-initialization.lean");
    File.WriteAllText(forged, source.Replace(operation, ".stackAlloc true", StringComparison.Ordinal));
    var rejected = Execute(["lake", "env", "lean", forged], cwd: FixturePackage());
    if (rejected.Code == 0 || !rejected.Output.Contains("FeatureFlowValid", StringComparison.Ordinal))
        throw new Exception("Forged localsinit was not rejected by the Lean certificate: " + rejected.Output);
    Console.WriteLine("PASS forged stack initialization rejected");
}

evidence.Check(replay: false);
