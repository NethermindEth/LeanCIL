#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Diagnostics;

var output = At("artifacts/VerificationReuse");
Directory.CreateDirectory(output);
var proof = Path.Combine(output, "Contract.lean");
var baseline = File.ReadAllText(At("Examples/Proofs/Add.lean"));
File.WriteAllText(proof, baseline);
var assembly = At("Examples/Assembly/bin/Examples.dll");
const string entry = "Arithmetic::Add(ulong,ulong)";
using var verifier = new Program();
var timer = Stopwatch.StartNew();
verifier.Verify(assembly, "Examples", entry, proof, output);
var first = timer.ElapsedMilliseconds;
timer.Restart();
verifier.Verify(assembly, "Examples", entry, proof, output);
var repeated = timer.ElapsedMilliseconds;
if (verifier.extractionCacheHits == 0 || verifier.proofCacheHits == 0)
    throw new Exception("Repeated verification did not reuse certified artifacts");
verifier.Verify(assembly, "Examples", entry, proof, output, check: true);
var proofHits = verifier.proofCacheHits;
File.WriteAllText(proof, baseline + "\n-- A changed proof must be checked again.\n");
verifier.Verify(assembly, "Examples", entry, proof, output);
if (verifier.proofCacheHits != proofHits) throw new Exception("Changed proof reused old certification");
File.WriteAllText(proof, """
    import Extracted
    import Lean
    set_option debug.skipKernelTC true
    run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
      name := `ExampleProof.helper
      levelParams := []
      type := Lean.mkConst ``False
      value := Lean.mkConst ``True.intro
    })
    set_option debug.skipKernelTC false
    theorem ExampleProof.correctness : False := ExampleProof.helper
    """);
for (var attempt = 0; attempt < 2; attempt++)
{
    try
    {
        verifier.Verify(assembly, "Examples", entry, proof, output);
        throw new Exception("Unchecked theorem was accepted");
    }
    catch (InvalidOperationException error) when (error.Message.Contains("while replaying declaration")) { }
    if (File.Exists(Path.Combine(output, "verified.json"))) throw new Exception("Failed proof retained a successful report");
}
File.WriteAllText(proof, baseline);
using var second = new Program();
timer.Restart();
second.Verify(assembly, "Examples", entry, proof, output);
var newSession = timer.ElapsedMilliseconds;
if (second.extractionCacheHits == 0 || second.proofCacheHits == 0 || second.supportCacheHits == 0)
    throw new Exception("New verifier session did not reuse certified dependencies and proofs");
Console.WriteLine($"PASS certified reuse, proof-edit invalidation, repeated unchecked-theorem rejection and new-session reuse; first={first}ms repeat={repeated}ms new-session={newSession}ms");
