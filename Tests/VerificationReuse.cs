#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Diagnostics;

var output = At("artifacts/VerificationReuse");
Directory.CreateDirectory(output);
var proof = Path.Combine(output, "Contract.lean");
// The support import makes a new session exercise certified dependency reuse, not only proof reuse.
var baseline = "import Tests.Support\n" + File.ReadAllText(At("Examples/Proofs/Add.lean"));
File.WriteAllText(proof, baseline);
var assembly = At("Examples/Assembly/bin/Examples.dll");
const string entry = "Arithmetic::Add(ulong,ulong)";
// Verify against a supplied certified library, as CI does, under a cache of this run's own: the
// reuse checks must count only certifications this run made, never ones a previous run left.
var isolatedCache = At("artifacts/VerificationReuseCache");
if (Directory.Exists(isolatedCache)) DeleteTree(isolatedCache);
if (string.IsNullOrWhiteSpace(Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY")))
{
    var certifiedBase = At("artifacts/VerificationReuseLibrary");
    if (Directory.Exists(certifiedBase)) DeleteTree(certifiedBase);
    using var producer = new Program();
    Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY_SHA256", producer.PrepareLibrary(certifiedBase));
    Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", certifiedBase);
}
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", isolatedCache);
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
// A module planted in a certified library read in place is never certified, even after the
// library was certified in this session: building it writes into the library, which is rejected
// as changed, and a later session that finds it already built reports its kernel replay failure.
var plantedLibrary = Path.Combine(Path.GetTempPath(), "leancil-reuse-" + Guid.NewGuid().ToString("N"));
CopyTree(verifier.library!, plantedLibrary);
var suppliedLibrary = Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY");
var suppliedDigest = Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY_SHA256");
Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", plantedLibrary);
Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY_SHA256", Sha(Path.Combine(plantedLibrary, "cache-manifest.json")));
try
{
    const string forgedProof =
        "import Extracted\nimport CIL.ReuseForged\ntheorem ExampleProof.correctness : False := ReuseForged.helper\n";
    using (var planted = new Program())
    {
        File.WriteAllText(proof, baseline);
        planted.Verify(assembly, "Examples", entry, proof, output);
        File.WriteAllText(Path.Combine(planted.library!, "CIL", "ReuseForged.lean"), """
            import Lean
            set_option debug.skipKernelTC true
            run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
              name := `ReuseForged.helper
              levelParams := []
              type := Lean.mkConst ``False
              value := Lean.mkConst ``True.intro
            })
            """);
        File.WriteAllText(proof, forgedProof);
        try
        {
            planted.Verify(assembly, "Examples", entry, proof, output);
            throw new Exception("Unchecked imported helper was accepted");
        }
        catch (InvalidOperationException error) when (error.Message.Contains("changed on disk during verification") &&
            error.Message.Contains("ReuseForged")) { }
        if (File.Exists(Path.Combine(output, "verified.json")))
            throw new Exception("Failed dependency retained a successful report");
    }
    // The library now holds the forged module's outputs, which its manifest does not record.
    using var reopened = new Program();
    var dependencyStage = "";
    try
    {
        reopened.Verify(assembly, "Examples", entry, proof, output, stage: value => dependencyStage = value);
        throw new Exception("Unchecked imported helper already built into the library was accepted");
    }
    catch (InvalidOperationException error) when (error.Message.Contains("while replaying declaration") &&
        error.Message.Contains("ReuseForged.helper") && dependencyStage == "kernel replay") { }
    if (File.Exists(Path.Combine(output, "verified.json"))) throw new Exception("Failed dependency retained a successful report");
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", suppliedLibrary);
    Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY_SHA256", suppliedDigest);
    Directory.Delete(plantedLibrary, true);
}
Console.WriteLine("PASS imported helper built into the library is rejected, and replayed once it is there");
File.WriteAllText(proof, baseline);
using var second = new Program();
timer.Restart();
second.Verify(assembly, "Examples", entry, proof, output);
var newSession = timer.ElapsedMilliseconds;
if (second.extractionCacheHits == 0 || second.proofCacheHits == 0 || second.supportCacheHits == 0)
    throw new Exception("New verifier session did not reuse certified dependencies and proofs");
using var freshProof = new Program { freshProofs = true };
freshProof.Verify(assembly, "Examples", entry, proof, output);
if (freshProof.extractionCacheHits != 0 || freshProof.proofCacheHits != 0 || freshProof.supportCacheHits != 0 ||
    freshProof.libraryKey != second.libraryKey || freshProof.libraryBuild != second.libraryBuild)
    throw new Exception("Fresh proof reused proof/support artifacts or bypassed the existing certified library");
Console.WriteLine("PASS fresh proof bypasses proof/support reuse while retaining the certified library");

// The session holds no compiled Extracted, so a support module importing it cannot be built, certified or
// cached; a support entry therefore never holds a module bound to one extraction.
{
    var supportOutput = At("artifacts/ExtractedSupport");
    Directory.CreateDirectory(supportOutput);
    var supportProof = Path.Combine(supportOutput, "Proof.lean");
    var addProof = File.ReadAllText(At("Examples/Proofs/Add.lean"));
    File.WriteAllText(supportProof, "import Tests.ExtractedSupport\n" + addProof);
    var lakefilePath = At("lakefile.toml");
    var lakefileBytes = File.ReadAllBytes(lakefilePath);
    var supportModule = At("Tests/ExtractedSupport.lean");
    try
    {
        // Registered only while this check runs: a library that imports Extracted fails every full library build.
        File.AppendAllText(lakefilePath, "\n[[lean_lib]]\nname = \"Tests.ExtractedSupport\"\n");
        File.WriteAllText(supportModule,
            "import Extracted\n\ntheorem ExtractedSupport.program : True := True.intro\n");
        using var importing = new Program();
        try
        {
            importing.Verify(assembly, "Examples", entry, supportProof, supportOutput);
            throw new Exception("A support module importing Extracted was built and its proof reported verified");
        }
        catch (InvalidOperationException error) when (error.Message.Contains("unknown module prefix 'Extracted'")) { }
        if (importing.supportCacheHits != 0 || File.Exists(Path.Combine(supportOutput, "verified.json")))
            throw new Exception("A support module importing Extracted was restored or left a successful report");
    }
    finally
    {
        File.WriteAllBytes(lakefilePath, lakefileBytes);
        if (File.Exists(supportModule)) File.Delete(supportModule);
    }
    Console.WriteLine("PASS a support module importing Extracted cannot be built or cached");
}
Console.WriteLine($"PASS certified reuse, proof-edit invalidation, repeated unchecked-theorem rejection and new-session reuse; first={first}ms repeat={repeated}ms new-session={newSession}ms");
