#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs

using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

var root = At("artifacts/SupportExtractionCache-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
var assembly = Path.Combine(root, "Examples.dll");
File.Copy(At("Examples/Assembly/bin/Examples.dll"), assembly);
var proof = Path.Combine(root, "Proof.lean");
File.WriteAllText(proof, """
    import Extracted
    import Tests.Support
    namespace ExampleProof
    theorem correctness :
        (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 0), .scalar (.i64 0)]
          CIL.Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 0)] := rfl
    #print axioms correctness
    end ExampleProof
    """);
var saved = new[] { "LEANCIL_CACHE_DIR", "LEANCIL_DISABLE_SUCCESS_CACHE", "LEANCIL_TRACE_DIRECTORY" }
    .ToDictionary(name => name, Environment.GetEnvironmentVariable);
try
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", Path.Combine(root, "Cache"));
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
    const string entry = "Arithmetic::Add(ulong,ulong)";
    var output = Path.Combine(root, "Extraction");

    (string Identity, string Generated) Verify(string name, bool reused)
    {
        var trace = Path.Combine(root, name);
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
        using var verifier = new Program();
        verifier.Verify(assembly, "Examples", entry, proof, output);
        var built = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
            .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
            .Any(stage => stage.GetProperty("stage").GetString() == "Building proof dependencies: " + entry);
        if ((verifier.supportCacheHits == 1, built) != (reused, !reused))
            throw new Exception($"{name}: support cache hit={verifier.supportCacheHits}, built={built}; " +
                $"expected reuse={reused}");
        var identity = ExtractionIdentity.Read(output);
        return (identity.Sha256, identity.Root.GetProperty("generatedSha256").GetString()!);
    }

    var initial = Verify("Initial", reused: false);
    var unchanged = Verify("Unchanged", reused: true);
    if (unchanged != initial) throw new Exception("Unchanged assembly produced a different extraction");

    // Both opcodes return zero for these inputs; the proof and support sources remain identical.
    using (var module = ModuleDefinition.ReadModule(assembly, new ReaderParameters { InMemory = true }))
    {
        var method = module.GetType("Examples.Arithmetic").Methods.Single(method => method.Name == "Add");
        method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Add).OpCode = OpCodes.Sub;
        module.Write(assembly);
    }
    var changed = Verify("Changed", reused: false);
    if (changed.Identity == initial.Identity || changed.Generated == initial.Generated)
        throw new Exception("The changed instruction did not change the extraction identity and generated code");
    Console.WriteLine("PASS unchanged extraction reuses support; changed instruction rebuilds support");
}
finally
{
    foreach (var (name, value) in saved) Environment.SetEnvironmentVariable(name, value);
}
