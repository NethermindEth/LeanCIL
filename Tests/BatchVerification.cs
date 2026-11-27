#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/BatchVerification.cs

using System.Diagnostics;
using System.Text.Json;
using Mono.Cecil;

if (args.Length > 0 && args is not ["--benchmark"])
    throw new ArgumentException("Usage: BatchVerification.cs [--benchmark]");
var benchmark = args.Length > 0;
var root = At("artifacts/BatchVerification");
Directory.CreateDirectory(root);
var assembly = At("Examples/Assembly/bin/Examples.dll");
var requests = Enumerable.Range(0, benchmark ? 8 : 2).Select(i =>
{
    var output = Path.Combine(root, "Case" + i);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, $"import Extracted\nimport CIL.Safety.Execution\nnamespace ExampleProof\ntheorem correctness : (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 {i}), .scalar (.i64 1)] CIL.Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 {i + 1})] := rfl\nend ExampleProof\n");
    return new GeneratedVerification("Arithmetic::Add(ulong,ulong)", proof, output);
}).ToArray();
using var verification = new Program();
var previous = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
try
{
    // Compare process batching itself, without a warm theorem cache hiding work.
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
    verification.Library(Inputs(requests[0].Proof));
    double? sequentialSeconds = null;
    if (benchmark)
    {
        // Both timings start after extractor and support dependency setup.
        verification.Verify(assembly, "Examples", requests[0].Entry, requests[0].Proof, Path.Combine(root, "Warmup"));
        var timer = Stopwatch.StartNew();
        foreach (var request in requests)
            verification.Verify(assembly, "Examples", request.Entry, request.Proof, request.Output);
        sequentialSeconds = timer.Elapsed.TotalSeconds;
    }
    var batched = Stopwatch.StartNew();
    var first = requests[0];
    var shared = first with { Theorem = "ExampleProof.same_result", Output = Path.Combine(root, "SharedProof") };
    if (!benchmark)
        File.AppendAllText(first.Proof, """

            namespace ExampleProof
            theorem same_result : (CIL.Safety.invoke Extracted.program 8 0
                [.scalar (.i64 0), .scalar (.i64 1)] CIL.Safety.Memory.empty).map Prod.snd =
                .ok [.scalar (.i64 1)] := correctness
            #print axioms same_result
            end ExampleProof

            """);
    var batch = benchmark ? requests : [.. requests, shared];
    verification.VerifyGeneratedBatch(assembly, "Examples", batch);
    batched.Stop();
    foreach (var request in requests)
        verification.Verify(assembly, "Examples", request.Entry, request.Proof, request.Output, check: true);
    if (!benchmark)
    {
        verification.Verify(assembly, "Examples", shared.Entry, shared.Proof, shared.Output,
            theorem: shared.Theorem, check: true);
        var sharedReport = JsonSerializer.Deserialize<JsonElement>(
            File.ReadAllText(Path.Combine(shared.Output, "verified.json")));
        if (sharedReport.GetProperty("batchTheorem").GetString() != "BatchCase0.ExampleProof.same_result" ||
            Sha(Path.Combine(shared.Output, "Batch.lean")) != Sha(Path.Combine(first.Output, "Batch.lean")))
            throw new InvalidOperationException("Theorems of the same input did not share their checked batch case");
    }
    Console.WriteLine($"PASS {batch.Length} batched proofs, independent certificates and report identities");
    if (benchmark)
    {
        var timing = new { fixtures = requests.Length, sequentialSeconds, batchSeconds = batched.Elapsed.TotalSeconds };
        File.WriteAllText(Path.Combine(root, "timings.json"), JsonSerializer.Serialize(timing, Json));
        Console.WriteLine(JsonSerializer.Serialize(timing));
    }

    var batchPath = Path.Combine(requests[0].Output, "Batch.lean");
    var batchSource = File.ReadAllText(batchPath);
    File.AppendAllText(batchPath, "\n-- tampered\n");
    var rejected = false;
    try
    {
        verification.Verify(assembly, "Examples", requests[0].Entry, requests[0].Proof, requests[0].Output, check: true);
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Stale verification report", StringComparison.Ordinal))
    {
        rejected = true;
    }
    if (!rejected) throw new InvalidOperationException("Changed batch source accepted");
    File.WriteAllText(batchPath, batchSource);
    Console.WriteLine("PASS modified batch source rejected");

    var firstProof = File.ReadAllText(requests[0].Proof);
    var lastProof = File.ReadAllText(requests[^1].Proof);
    var commonMutation = At("Tests/BatchMutation" + Guid.NewGuid().ToString("N") + ".lean");
    try
    {
        foreach (var target in new[] { requests[0].Proof, commonMutation })
        {
            File.WriteAllText(requests[^1].Proof, lastProof + $$"""

                open Lean Elab Command in
                run_cmd do
                  IO.FS.writeFile {{JsonSerializer.Serialize(target.Replace('\\', '/'))}} "-- changed by proof code\n"
                """);
            rejected = false;
            try
            {
                verification.VerifyGeneratedBatch(assembly, "Examples", batch);
            }
            catch (InvalidOperationException error) when (error.Message == "Batch inputs changed during verification")
            {
                rejected = true;
            }
            if (!rejected || batch.Any(r => File.Exists(Path.Combine(r.Output, "verified.json"))))
                throw new InvalidOperationException("Proof code mutated batch inputs without rejecting every report");
            File.WriteAllText(requests[0].Proof, firstProof);
        }
        Console.WriteLine("PASS proof code changing an earlier proof or adding common inputs rejects every report");
    }
    finally
    {
        File.WriteAllText(requests[0].Proof, firstProof);
        File.WriteAllText(requests[^1].Proof, lastProof);
        File.Delete(commonMutation);
    }

    // One failing fixture invalidates the whole attempt, including old reports.
    var wrong = requests.Select((r, i) => i == requests.Length - 1
        ? r with { Entry = "Arithmetic::WrongAdd(ulong,ulong)" } : r).ToArray();
    rejected = false;
    try
    {
        verification.VerifyGeneratedBatch(assembly, "Examples", wrong);
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Batch.lean") && error.Message.Contains("error:"))
    {
        rejected = true;
    }
    if (!rejected || requests.Any(r => File.Exists(Path.Combine(r.Output, "verified.json"))))
        throw new InvalidOperationException("Failing batch retained successful reports");
    Console.WriteLine("PASS incorrect implementation rejects batch and removes all prior success reports");

    // A fixture's own assembly replaces the batch assembly: Add bound to WrongAdd's body must fail.
    var swapped = Path.Combine(root, "SwappedAdd.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var arithmetic = module.GetType("Examples.Arithmetic");
        arithmetic.Methods.Single(m => m.Name == "Add").Name = "OriginalAdd";
        arithmetic.Methods.Single(m => m.Name == "WrongAdd").Name = "Add";
        module.Write(swapped);
    }
    rejected = false;
    try
    {
        verification.VerifyGeneratedBatch(assembly, "Examples", [requests[0], requests[1] with { Assembly = swapped }]);
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Batch.lean") && error.Message.Contains("error:"))
    {
        rejected = true;
    }
    if (!rejected || requests.Any(r => File.Exists(Path.Combine(r.Output, "verified.json"))))
        throw new InvalidOperationException("Fixture assembly override ignored");
    Console.WriteLine("PASS fixture assembly overrides the batch assembly");

    File.WriteAllText(requests[0].Proof, """
        import Extracted
        import Lean
        set_option debug.skipKernelTC true
        run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
          name := `BatchCase0.ExampleProof.helper
          levelParams := []
          type := Lean.mkConst ``False
          value := Lean.mkConst ``True.intro
        })
        set_option debug.skipKernelTC false
        theorem ExampleProof.correctness : False := ExampleProof.helper
        """);
    rejected = false;
    try
    {
        verification.VerifyGeneratedBatch(assembly, "Examples", [requests[0]]);
    }
    catch (InvalidOperationException error) when (error.Message.Contains("while replaying declaration"))
    {
        rejected = true;
    }
    if (!rejected || File.Exists(Path.Combine(requests[0].Output, "verified.json")))
        throw new InvalidOperationException("Unchecked helper bypassed batch kernel replay");
    Console.WriteLine("PASS unchecked transitive helper rejected by batch kernel replay");

    // A genuine counterexample about the empty program refutes nothing in the fixture's extraction.
    File.WriteAllText(requests[0].Proof, """
        import Extracted
        import CIL.Safety.MethodContract

        open CIL.Safety

        /-- Promises a return from any memory. -/
        def ExampleProof.returns : MethodContract Unit :=
          { args := fun _ => [], pre := fun _ _ => True, footprint := fun _ => [], post := fun _ _ _ _ => True }

        /-- The empty program has no method zero, so a call to it faults. -/
        theorem ExampleProof.correctness : ExampleProof.returns.Refuted [] 0 :=
          .of_fault (input := ()) (initial := Memory.empty) (observed := 1)
            (fault := { method := 0, instruction := 0, fault := .invalidState }) trivial (by decide) rfl
        """);
    rejected = false;
    try
    {
        verification.VerifyGeneratedBatch(assembly, "Examples", [requests[0]]);
    }
    catch (InvalidOperationException error)
        when (error.Message.Contains("a refutation states BatchCase0.Extracted.program", StringComparison.Ordinal))
    {
        rejected = true;
    }
    if (!rejected || File.Exists(Path.Combine(requests[0].Output, "verified.json")))
        throw new InvalidOperationException("A batch certificate carried a refutation of another program");
    Console.WriteLine("PASS a batch refuses a counterexample about another program");
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", previous);
}
