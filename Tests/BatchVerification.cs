#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Diagnostics;
using System.Text.Json;

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
    File.WriteAllText(proof, $"import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness : (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 {i}), .scalar (.i64 1)] Examples.empty).map Prod.snd = .ok [.scalar (.i64 {i + 1})] := rfl\nend ExampleProof\n");
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
    verification.VerifyGeneratedBatch(assembly, "Examples", requests);
    batched.Stop();
    foreach (var request in requests)
        verification.Verify(assembly, "Examples", request.Entry, request.Proof, request.Output, check: true);
    Console.WriteLine($"PASS {requests.Length} batched proofs, independent certificates and report identities");
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
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", previous);
}
