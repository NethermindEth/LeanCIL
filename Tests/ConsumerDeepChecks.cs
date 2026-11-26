#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include MultiAssemblyFixture.cs
#:include DeepImportChecks.cs

using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

long previousAllocated = 0;
foreach (int count in new[] { 64, 256, 1024 })
{
    string[] paths = [.. Enumerable.Range(0, count).SelectMany(index =>
        new[] { $"Module{index}.olean", $"Module{index}.olean.private", $"Module{index}.olean.server" })];
    _ = ConsumerArtifactCounts(paths);
    var allocated = GC.GetAllocatedBytesForCurrentThread();
    for (int repeat = 0; repeat < 32; repeat++)
    {
        var counts = ConsumerArtifactCounts(paths);
        if (counts.Count != count || counts.Values.Any(parts => parts != 3))
            throw new InvalidOperationException("Module family index lost a companion.");
    }
    allocated = GC.GetAllocatedBytesForCurrentThread() - allocated;
    if (previousAllocated > 0 && allocated > previousAllocated * 6)
        throw new InvalidOperationException("Module family indexing allocates faster than linear growth.");
    previousAllocated = allocated;
    Console.WriteLine($"PASS {count} module families indexed 32 times, {allocated} allocated bytes");
    int manifestVisits = 0;
    int keyVisits = 0;
    IEnumerable<IEnumerable<string>> Manifests()
    {
        for (int index = 0; index < count; index++)
        {
            manifestVisits++;
            yield return Keys(index);
        }
    }
    IEnumerable<string> Keys(int index)
    {
        keyVisits++;
        yield return "Module" + index;
    }
    var modules = Enumerable.Range(0, count).ToDictionary(index => "Module" + index, index => "path" + index,
        StringComparer.Ordinal);
    var selected = ConsumerSupportModules(Manifests(), modules);
    if (selected.Count != count || manifestVisits != count || keyVisits != count)
        throw new InvalidOperationException("Portable support selection repeatedly scanned its manifests.");
    Console.WriteLine($"PASS {count} portable manifests selected with {manifestVisits} manifest " +
        $"and {keyVisits} key visits");
}
if (args is ["--inventory"]) return;

MultiAssemblyFixture fixture = new("ConsumerDeepChecks");
var harmlessAncestor = Path.Combine(fixture.Root, "BindingAudit", "Consumer");
Directory.CreateDirectory(Path.Combine(harmlessAncestor, "Client/BindingAudit"));
File.WriteAllText(Path.Combine(harmlessAncestor, "Client/BindingAudit/Helper.lean"), "def helper := 1\n");
RequireConsumerDeepNamespaces([harmlessAncestor]);
var reserved = Path.Combine(harmlessAncestor, "StrictBinding.lean");
File.WriteAllText(reserved, "def helper := 1\n");
ExpectFailure(() => RequireConsumerDeepNamespaces([harmlessAncestor]), "reserved deep-check namespace");
File.Delete(reserved);
Console.WriteLine("PASS namespace checks distinguish source roots from ancestors and nested namespaces");
using Program verification = new();
verification.EnsureExtractorBuilt();
var image = fixture.Build("Input", "ConsumerDeepFixture", """
    public static class Input { public static ulong Value(ulong value) => value + 1; }
    """);
var output = fixture.Artifact("extracted");
Run([.. fixture.Cli, "extract", image, "Input::Value(System.UInt64)", output]);
var package = Path.Combine(fixture.Root, "Consumer");
Directory.CreateDirectory(package);
var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"), $"""
    name = "deep_consumer"
    [[require]]
    name = "leancil"
    git = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}
    rev = "{revision}"
    """);
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
var proof = Path.Combine(package, "Proof.lean");
File.WriteAllText(proof, """
    import Extracted
    import CIL.Safety.Execution
    namespace ExampleProof
    theorem correctness :
        (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 2)] CIL.Safety.Memory.empty).map
          Prod.snd = .ok [.scalar (.i64 3)] := rfl
    #print axioms correctness
    end ExampleProof
    """);
Run(["lake", "update"], package);
var manifest = Path.Combine(fixture.Root, "images.sha256");
File.WriteAllText(manifest, Sha(image) + "  " + Path.GetRelativePath(fixture.Root, image) + "\n");
var inputs = DeepCheckInputs.Read(manifest);
ConsumerRequest request = new(image, output, proof, "ExampleProof.correctness", null);
var selectionRun = new DeepCheckRun(inputs);
var invalidSelection = verification.VerifyConsumerRequests(package,
    [request with { Proof = Path.Combine(fixture.Root, "Outside.lean") }], null, batch: false,
    deepChecks: inputs, deepRun: selectionRun)[0];
if (invalidSelection.Error is null || selectionRun.Attempt is not null)
    throw new InvalidOperationException("Consumer selection failure began a deep attempt.");
var libraryRun = new DeepCheckRun(inputs);
ExpectFailure(() => verification.VerifyConsumer(image, proof, output, "ExampleProof.correctness", package,
    null, stage =>
    {
        if (stage != "Lean library build") return;
        if (libraryRun.Attempt is null) throw new InvalidOperationException("Missing pre-library attempt.");
        throw new InvalidOperationException("diagnostic library failure");
    }, inputs, libraryRun), "diagnostic library failure");
RequireUnattributed(libraryRun);
Console.WriteLine("PASS consumer attempts begin after selection and before library work");
ExpectFailure(() => verification.VerifyConsumerRequests(package, [request], null, batch: true,
    deepChecks: inputs), "one ordinary");
ExpectFailure(() => verification.VerifyConsumerRequests(package, [request], null, batch: false,
    checkOnly: true, deepChecks: inputs), "one ordinary");
ExpectFailure(() => verification.VerifyConsumerRequests(package, [request, request], null, batch: false,
    deepChecks: inputs), "one ordinary");

var priorCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
var priorDisableCache = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", At("artifacts/ConsumerDeepChecksCache"));
Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
try
{
    if (args is ["--replay-diagnostics"])
    {
        foreach (bool mutateOriginal in new[] { false, true })
        {
            var token = Guid.NewGuid().ToString("N");
            File.AppendAllText(proof, "\n-- " + token + "\n");
            var original = File.ReadAllText(proof);
            var run = new DeepCheckRun(inputs);
            SortedDictionary<string, string>? before = null;
            bool diagnosed = false;
            try
            {
                ExpectFailure(() => Verify(verification, deepRun: run, stage: stage =>
                {
                    if (stage == "replay diagnostics")
                    {
                        diagnosed = true;
                        if (mutateOriginal) File.AppendAllText(proof, "\n-- changed during replay\n");
                    }
                    if (stage != "deep-check sources") return;
                    var workspace = Directory.EnumerateDirectories(Path.GetTempPath(), "leancil-consumer-*")
                        .Single(directory => File.Exists(Path.Combine(directory, "LeanCILProof.lean")) &&
                            File.ReadAllText(Path.Combine(directory, "LeanCILProof.lean"))
                                .Contains(token, StringComparison.Ordinal));
                    var generated = Path.Combine(workspace, ".deep-checks/BindingAudit/Bodies.lean");
                    var source = File.ReadAllText(generated);
                    var theorem = source.IndexOf("theorem bodies :", StringComparison.Ordinal);
                    var start = source.LastIndexOf("/--", theorem, StringComparison.Ordinal);
                    File.WriteAllText(generated, source[..start] + """
                        set_option debug.skipKernelTC true in
                        run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
                          name := `BindingAudit.bodies
                          levelParams := []
                          type := Lean.mkConst ``False
                          value := Lean.mkConst ``True.intro
                        })
                        end BindingAudit
                        """);
                    before = Receipts();
                }), mutateOriginal ? "Inputs changed during consumer verification" : "Kernel replay rejected");
            }
            finally { File.WriteAllText(proof, original); }
            if (!diagnosed || before is null) throw new Exception("Consumer diagnostics were not reached");
            if (mutateOriginal) RequireUnattributed(run);
            else
            {
                var failed = run.Attempt!.Failure("kernel replay", "rejected");
                if (failed.facts.Where(fact => fact.status == FailureReports.BindingFailureStatus.Failed)
                    .Select(fact => fact.id).Single() != "body-bytes" ||
                    failed.images.Any(image => image.status == FailureReports.BindingFailureStatus.Failed))
                    throw new Exception("Consumer replay attribution changed");
            }
            RequireNoPublication(before);
            Console.WriteLine("PASS consumer typed replay rejection; original mutation=" + mutateOriginal);
        }
        return;
    }
    if (args is ["--export-support"])
    {
        CheckExportMutation();
        return;
    }
    if (args is ["--export-original"])
    {
        CheckExportMutation(originalProofMutation: true);
        return;
    }
    var ordinary = Verify(verification, deep: false);
    if (ordinary.binding.mode != BindingMode.Default || verification.bindingPreparation is not null)
        throw new InvalidOperationException("Ordinary consumer verification prepared deep checks.");
    var ordinaryReceipts = ProofReceipts();
    if (ordinaryReceipts.Count == 0) throw new InvalidOperationException("Ordinary proof receipt was not published.");
    foreach (var entry in DeepResults()) Directory.Delete(entry, true);
    var deepHits = verification.deepCacheHits;
    CheckDeep(Verify(verification));
    RequireOrdinaryReceipts();
    if (verification.deepCacheHits != deepHits || DeepResults().Length != 1)
        throw new InvalidOperationException("A cold consumer deep request did not publish one deep result.");
    RequireDeepImports(verification.deepImports, "consumer");
    Console.WriteLine("PASS consumer joint deep audit preserves ordinary result receipts");
    bool reusedAudit = false;
    CheckDeep(Verify(verification, stage: stage => reusedAudit |= stage == "theorem audit"));
    if (verification.deepCacheHits != deepHits + 1 || !reusedAudit)
        throw new InvalidOperationException("An unchanged consumer deep request did not reuse its result.");
    Console.WriteLine("PASS an unchanged consumer deep request reuses its result and runs the theorem audit");
    var beforeImportChange = Receipts();
    var importToken = Guid.NewGuid().ToString("N");
    File.AppendAllText(proof, "\n-- " + importToken + "\n");
    ExpectFailure(() => Verify(verification, stage: stage =>
    {
        if (stage != "deep-check sources") return;
        SameLengthChange(Path.Combine(ConsumerSession(importToken),
            ".lake/packages/leancil_generated/.lake/build/lib/lean/Extracted.olean"));
    }), "Deep-check artifact changed");
    RequireNoPublication(beforeImportChange);
    if (verification.deepCacheHits != deepHits + 1)
        throw new InvalidOperationException("A consumer deep result was restored over a changed imported module.");
    Console.WriteLine("PASS a same-length consumer extraction change with its write time restored is not restored");
    var deepEntry = DeepResults().Single();
    var cachedBodies = Path.Combine(deepEntry, "files", "BindingAudit", "Bodies.olean");
    var forged = Path.Combine(fixture.Root, "ConsumerWrongBodies.olean");
    var forgeToken = Guid.NewGuid().ToString("N");
    File.AppendAllText(proof, "\n-- " + forgeToken + "\n");
    var beforeLateFailure = Receipts();
    // A changed generated source misses, so this cold request fails at its last check after build and replay.
    ExpectFailure(() => Verify(verification, stage: stage =>
    {
        if (stage is not ("deep-check sources" or "theorem audit")) return;
        var generated = Path.Combine(ConsumerSession(forgeToken), ".deep-checks", "BindingAudit", "Bodies.lean");
        if (stage == "deep-check sources")
        {
            var source = File.ReadAllText(generated);
            var start = source.IndexOf("theorem bodies :", StringComparison.Ordinal);
            if (start < 0) throw new InvalidOperationException("Missing generated bodies theorem.");
            File.WriteAllText(generated, source[..start] + "theorem bodies : StrictBinding.BodiesBound images [] := " +
                "StrictBinding.claimsHold_nil Bodies.prepared\n#print axioms bodies\nend BindingAudit\n");
        }
        if (stage == "theorem audit" && !File.Exists(forged))
            File.Copy(Path.ChangeExtension(generated, ".olean"), forged);
    }), "Theorem statement mismatch");
    if (!File.Exists(forged)) throw new InvalidOperationException("The forged body module was not built.");
    RequireNoPublication(beforeLateFailure);
    if (verification.deepCacheHits != deepHits + 1 || DeepResults().Single() != deepEntry)
        throw new InvalidOperationException("A cold consumer deep request that failed late published a result.");
    Console.WriteLine("PASS a cold consumer deep request rejected by its theorem audit publishes nothing");
    File.Copy(forged, cachedBodies, true);
    var deepManifest = JsonSerializer.SerializeToUtf8Bytes(CacheFiles(Path.Combine(deepEntry, "files")));
    File.WriteAllBytes(Path.Combine(deepEntry, "receipt.json"), deepManifest);
    File.WriteAllBytes(Path.Combine(deepEntry, "receipt.hmac"), HMACSHA256.HashData(verification.ReceiptKey,
        Encoding.UTF8.GetBytes(Path.GetFileName(deepEntry)).Concat(deepManifest).ToArray()));
    var beforeForged = Receipts();
    ExpectFailure(() => Verify(verification), "Theorem statement mismatch");
    RequireNoPublication(beforeForged);
    if (verification.deepCacheHits != deepHits + 2)
        throw new InvalidOperationException("The forged consumer deep result was not restored.");
    Console.WriteLine("PASS the consumer theorem audit rejects an authenticated restored module stating another fact");
    // A same-length change with its timestamp restored must fail the receipt's content hashes.
    SameLengthChange(cachedBodies);
    var changedBodies = File.ReadAllBytes(cachedBodies);
    // A source changed after the result is staged fails the publication check, so the staged copy is discarded.
    var publicationToken = Guid.NewGuid().ToString("N");
    File.AppendAllText(proof, "\n-- " + publicationToken + "\n");
    var beforePublication = Receipts();
    bool publicationReached = false;
    ExpectFailure(() => Verify(verification, stage: stage =>
    {
        if (stage != "deep result publication") return;
        publicationReached = true;
        File.AppendAllText(Path.Combine(ConsumerSession(publicationToken), ".deep-checks", "BindingAudit",
            "Bodies.lean"), "\n");
    }), "Deep-check source changed");
    if (!publicationReached) throw new InvalidOperationException("The deep result publication stage was not reached.");
    RequireNoPublication(beforePublication);
    if (verification.deepCacheHits != deepHits + 2 || DeepResults().Single() != deepEntry ||
        !File.ReadAllBytes(cachedBodies).SequenceEqual(changedBodies))
        throw new InvalidOperationException("A staged consumer deep result was published after a failed check.");
    Console.WriteLine("PASS a staged consumer deep result is discarded when a later stability check fails");
    CheckDeep(Verify(verification));
    if (verification.deepCacheHits != deepHits + 2 || verification.AuthenticatedSuccess(Path.GetFileName(deepEntry))
            is null || File.ReadAllBytes(cachedBodies).SequenceEqual(changedBodies))
        throw new InvalidOperationException("A rebuilt consumer deep result did not replace the changed entry.");
    Console.WriteLine("PASS a changed cached consumer deep module runs cold and its rebuilt result replaces " +
        "the entry");
    if (args is ["--positive"]) return;
    var combinedRun = new DeepCheckRun(inputs);
    var combinedOriginalProof = File.ReadAllBytes(proof);
    var combinedToken = Guid.NewGuid().ToString("N");
    File.AppendAllText(proof, "\n-- " + combinedToken + "\n");
    bool combinedMutation = false;
    bool originalMutation = false;
    SortedDictionary<string, string>? combinedReceipts = null;
    try
    {
        ExpectFailure(() => Verify(verification, stage: stage =>
        {
            if (stage == "theorem audit" && !originalMutation)
            {
                File.AppendAllText(proof, "\n-- concurrent original proof edit\n");
                originalMutation = true;
            }
            if (stage != "deep-check sources") return;
            var workspace = Directory.EnumerateDirectories(Path.GetTempPath(), "leancil-consumer-*")
                .Single(directory => File.Exists(Path.Combine(directory, "LeanCILProof.lean")) &&
                    File.ReadAllText(Path.Combine(directory, "LeanCILProof.lean"))
                        .Contains(combinedToken, StringComparison.Ordinal));
            var generated = Path.Combine(workspace, ".deep-checks/BindingAudit/Bodies.lean");
            var source = File.ReadAllText(generated);
            var start = source.IndexOf("theorem bodies :", StringComparison.Ordinal);
            if (start < 0) throw new InvalidOperationException("Missing generated bodies theorem.");
            File.WriteAllText(generated, source[..start] + "theorem bodies : True := True.intro\n" +
                "#print axioms bodies\nend BindingAudit\n");
            combinedMutation = true;
            combinedReceipts = Receipts();
        }, deepRun: combinedRun), "Inputs changed during consumer verification");
    }
    finally { File.WriteAllBytes(proof, combinedOriginalProof); }
    if (!combinedMutation || !originalMutation || combinedReceipts is null)
        throw new InvalidOperationException("Missing combined consumer mutation.");
    RequireUnattributed(combinedRun);
    RequireNoPublication(combinedReceipts);
    Console.WriteLine("PASS consumer original-input mutation precedes named rejection attribution");
    if (args is ["--diagnostics"]) return;
    // Without a deep result the fallback must replay the generated modules themselves.
    foreach (var entry in DeepResults()) Directory.Delete(entry, true);
    using (Program restored = new())
    {
        var replay = Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY");
        var previousTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
        var trace = Path.Combine(fixture.Root, "FallbackTrace");
        var previousOutput = Console.Out;
        using var captured = new StringWriter();
        try
        {
            Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", "true");
            Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
            Console.SetOut(captured);
            CheckDeep(Verify(restored));
        }
        finally
        {
            Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", replay);
            Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousTrace);
            Console.SetOut(previousOutput);
            Console.Write(captured.ToString());
        }
        if (!captured.ToString().Contains("CACHE certified consumer extraction preparation", StringComparison.Ordinal))
            throw new InvalidOperationException(
                "Fresh deep consumer did not restore authenticated extraction support.");
        var records = File.ReadLines(Path.Combine(trace, TraceFile)).Select(line =>
            JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
        var fallback = records.Single(record => record.GetProperty("stage").GetString() ==
            "Profiled kernel replay of consumer modules");
        if (fallback.GetProperty("exitCode").GetInt32() != 0 ||
            !File.ReadAllText(Path.Combine(trace, fallback.GetProperty("transcript").GetString()!))
                .Contains("BindingAudit.Bodies", StringComparison.Ordinal))
            throw new InvalidOperationException("Fallback did not replay the body-check module successfully.");
        if (restored.deepCacheHits != 0)
            throw new InvalidOperationException("A consumer without a deep result restored one.");
    }
    RequireOrdinaryReceipts();
    Console.WriteLine("PASS fresh consumer with restored support and no deep result runs fallback deep audit");
    using (Program viewed = new() { viewsStatement = true })
    {
        CheckDeep(Verify(viewed));
        if (viewed.VerifiedStatement is null)
            throw new InvalidOperationException("Consumer deep verification lost the statement view.");
    }
    Console.WriteLine("PASS consumer deep statement view completes before publication");
    var originalProof = File.ReadAllText(proof);
    var beforeAxiom = Receipts();
    try
    {
        File.WriteAllText(proof, originalProof
            .Replace("namespace ExampleProof", "namespace ExampleProof\naxiom uncheckedCorrectness : False",
                StringComparison.Ordinal)
            .Replace(" := rfl", " := False.elim uncheckedCorrectness", StringComparison.Ordinal));
        ExpectFailure(() => Verify(verification), "Unapproved proof axioms");
        RequireNoPublication(beforeAxiom);
    }
    finally { File.WriteAllText(proof, originalProof); }
    Console.WriteLine("PASS consumer deep joint audit rejects an unapproved proof axiom");
    var beforeInvalidDeclaration = Receipts();
    try
    {
        File.WriteAllText(proof, "import Lean\n" + originalProof + """

            open Lean Elab Command in
            run_cmd do
              let environment <- getEnv
              let environment <- IO.ofExcept <| (environment.addDeclCore 0 0 (.thmDecl {
                name := `ConsumerInvalid.unrelated
                levelParams := []
                type := Lean.mkConst ``False
                value := Lean.mkConst ``True.intro
              }) none false).mapError (fun _ => "Could not construct rejection fixture")
              setEnv environment
            """);
        ExpectFailure(() => Verify(verification), "Kernel replay rejected LeanCILProof");
        RequireNoPublication(beforeInvalidDeclaration);
    }
    finally { File.WriteAllText(proof, originalProof); }
    Console.WriteLine("PASS consumer deep replay rejects an invalid unrelated declaration");
    Reject("source", "Deep-check source changed", "theorem audit", session =>
        File.AppendAllText(Path.Combine(session, ".deep-checks/BindingAudit/Bodies.lean"), "\n-- changed\n"));
    Reject("companion", "artifact", "theorem audit", session =>
        File.WriteAllBytes(Path.Combine(session, ".deep-checks/BindingAudit/Bodies.olean.unexpected"), [0]));
    Reject("extraction", "Compiled artifacts changed", "deep checks", session =>
        File.WriteAllBytes(Path.Combine(session,
            ".lake/packages/leancil_generated/.lake/build/lib/lean/Extracted.olean.unexpected"), [0]));
    Reject("foreign extraction", "Compiled artifacts changed", "deep checks", session =>
        File.Copy(Path.Combine(verification.library!, ".lake/build/lib/lean/CIL.olean"), Path.Combine(session,
            ".lake/packages/leancil_generated/.lake/build/lib/lean/Extracted.olean"), true));
    // The session builds no StrictBinding, so the stray artifact joins the library's module family.
    Reject("prepared binding", "prepared StrictBinding library changed", "kernel replay", _ =>
    {
        var built = Directory.CreateDirectory(Path.Combine(verification.session!, ".lake/build/lib/lean"));
        File.WriteAllBytes(Path.Combine(built.FullName, "StrictBinding.olean.unexpected"), [0]);
    });
    File.Delete(Path.Combine(verification.session!, ".lake/build/lib/lean/StrictBinding.olean.unexpected"));
    verification.fullImportAudit = (_, session, _, _) =>
    {
        File.AppendAllText(Path.Combine(session, ".deep-checks/BindingAudit/Images.lean"), "\n-- changed\n");
        return new("composition", "", [], []);
    };
    var receipts = Receipts();
    try { ExpectFailure(() => Verify(verification), "Deep-check source changed"); }
    finally { verification.fullImportAudit = null; }
    RequireNoPublication(receipts);
    Console.WriteLine("PASS full-import callback mutation leaves no new success receipt or report");
    var viewModule = Path.Combine(package, "ViewEffects.lean");
    var viewMarker = Path.Combine(fixture.Root, "view-mutation.txt");
    var configuration = Path.Combine(package, "lakefile.toml");
    var originalConfiguration = File.ReadAllText(configuration);
    originalProof = File.ReadAllText(proof);
    File.WriteAllText(viewModule, $$"""
        import Lean
        initialize do
          let current <- IO.currentDir
          if current.toString.endsWith "certified-result-0" then
            IO.FS.writeFile (current / "../.deep-checks/BindingAudit/Unexpected.lean") "-- changed\n"
            IO.FS.writeFile {{JsonSerializer.Serialize(viewMarker.Replace('\\', '/'))}} "mutated"
        """);
    File.AppendAllText(configuration, "\n[[lean_lib]]\nname = \"ViewEffects\"\n");
    File.WriteAllText(proof, "import ViewEffects\n" + originalProof);
    receipts = Receipts();
    try
    {
        using Program viewed = new() { viewsStatement = true };
        ExpectFailure(() => Verify(viewed), "Deep-check source changed");
        if (!File.Exists(viewMarker)) throw new InvalidOperationException("Statement view mutation did not execute.");
        RequireNoPublication(receipts);
    }
    finally
    {
        File.WriteAllText(proof, originalProof);
        File.WriteAllText(configuration, originalConfiguration);
        File.Delete(viewModule);
    }
    Console.WriteLine("PASS statement-view mutation precedes every successful support publication");

    var portableModule = Path.Combine(package, "PortableSupport.lean");
    // Normalization receipts persist in this test's cache, so only a module new to this run must be serialized.
    File.WriteAllText(portableModule, "theorem portableSupport : True := True.intro\n#print axioms portableSupport\n" +
        "def portableToken : String := \"" + Guid.NewGuid().ToString("N") + "\"\n");
    File.AppendAllText(configuration, "\n[[lean_lib]]\nname = \"PortableSupport\"\n");
    File.WriteAllText(proof, "import PortableSupport\n" + originalProof);
    var portableVariables = new[] { "LEANCIL_EXPORT_CONSUMER_SUPPORT", "LEANCIL_CONSUMER_SUPPORT",
        "LEANCIL_CONSUMER_SUPPORT_SHA256", "LEANCIL_TRACE_DIRECTORY", "LEANCIL_DISABLE_SUCCESS_CACHE" }
        .ToDictionary(name => name, Environment.GetEnvironmentVariable);
    var portableDirectory = Path.Combine(fixture.Root, "PortableSupport");
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
        Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", portableDirectory);
        Verify(verification, deep: false);
        var portableManifest = Directory.GetFiles(portableDirectory, "*.json").Single();
        Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", null);
        Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
        Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", portableManifest);
        Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", Sha(portableManifest));
        var trace = Path.Combine(fixture.Root, "PortableTrace");
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
        var beforePortable = Receipts();
        bool reachedAudit = false;
        ExpectFailure(() => Verify(verification, stage: stage =>
        {
            if (stage != "theorem audit") return;
            reachedAudit = true;
            throw new InvalidDataException("Terminal portable deep rejection");
        }), "Terminal portable deep rejection");
        if (!reachedAudit) throw new InvalidOperationException("Portable deep rejection did not reach the audit.");
        RequireNoPublication(beforePortable);
        var fingerprintTrace = File.ReadLines(Path.Combine(trace, TraceFile))
            .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
            .Single(record => record.GetProperty("stage").GetString() == "Canonical module fingerprints");
        var fingerprintCommand = fingerprintTrace.GetProperty("command").EnumerateArray()
            .Select(value => value.GetString()).ToArray();
        var serializedIndex = Array.IndexOf(fingerprintCommand, "serialized");
        if (serializedIndex < 0 || !int.TryParse(fingerprintCommand[serializedIndex + 1], out var serialized) ||
            serialized == 0)
            throw new InvalidOperationException("Portable deep verification did not normalize imported support.");
        var fingerprintsBefore = Directory.EnumerateFiles(SuccessCacheRoot, "fingerprints.json",
            SearchOption.AllDirectories).ToHashSet(StringComparer.Ordinal);
        var portableReport = Verify(verification, deep: false);
        if (portableReport.consumerSupportSha256 != Sha(portableManifest) ||
            !Directory.EnumerateFiles(SuccessCacheRoot, "fingerprints.json", SearchOption.AllDirectories)
                .Any(path => !fingerprintsBefore.Contains(path)))
            throw new InvalidOperationException("Ordinary portable control did not publish a normalization receipt.");
        Console.WriteLine("PASS rejected deep portable support publishes no normalization receipt; " +
            "ordinary control does");
    }
    finally
    {
        foreach (var (name, value) in portableVariables) Environment.SetEnvironmentVariable(name, value);
        File.WriteAllText(proof, originalProof);
        File.WriteAllText(configuration, originalConfiguration);
        File.Delete(portableModule);
    }
    CheckExportMutation();
    CheckExportMutation(originalProofMutation: true);

    void RequireOrdinaryReceipts()
    {
        if (!Same(ordinaryReceipts, ProofReceipts()))
            throw new InvalidOperationException("Deep consumer verification changed ordinary proof receipts.");
    }
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", priorCache);
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", priorDisableCache);
}

Report Verify(Program program, bool deep = true, Action<string>? stage = null, DeepCheckRun? deepRun = null) =>
    program.VerifyConsumer(image, proof, output, "ExampleProof.correctness", package, null, stage,
        deep ? inputs : null, deepRun);

void CheckExportMutation(bool originalProofMutation = false)
{
    var mutationName = originalProofMutation ? "original-proof" : "deep-source";
    var export = Path.Combine(fixture.Root, "MutatedExport-" + mutationName);
    var trace = Path.Combine(fixture.Root, "ExportTrace-" + mutationName);
    var marker = Path.Combine(fixture.Root, "normalization-mutation-" + mutationName + ".txt");
    var configuration = Path.Combine(package, "lakefile.toml");
    var originalConfiguration = File.ReadAllText(configuration);
    var originalProof = File.ReadAllText(proof);
    var token = Guid.NewGuid().ToString("N");
    var source = Path.Combine(package, "ExportSupport.lean");
    File.WriteAllText(source, "def exportSupport : String := \"" + token + "\"\n");
    File.AppendAllText(configuration, "\n[[lean_lib]]\nname = \"ExportSupport\"\n");
    File.WriteAllText(proof, "import ExportSupport\n" + originalProof + "\n-- " + token + "\n");
    var variables = new[] { "LEANCIL_EXPORT_CONSUMER_SUPPORT", "LEANCIL_CONSUMER_SUPPORT",
        "LEANCIL_CONSUMER_SUPPORT_SHA256", "LEANCIL_TRACE_DIRECTORY" }
        .ToDictionary(name => name, Environment.GetEnvironmentVariable);
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_EXPORT_CONSUMER_SUPPORT", export);
        Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT", null);
        Environment.SetEnvironmentVariable("LEANCIL_CONSUMER_SUPPORT_SHA256", null);
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
        var receipts = Receipts();
        ExpectFailure(() => Verify(verification, stage: stage =>
        {
            if (stage != "support normalization") return;
            var session = Directory.EnumerateDirectories(Path.GetTempPath(), "leancil-consumer-*")
                .Single(candidate => File.Exists(Path.Combine(candidate, "LeanCILProof.lean")) &&
                    File.ReadAllText(Path.Combine(candidate, "LeanCILProof.lean"))
                        .Contains(token, StringComparison.Ordinal));
            var target = originalProofMutation ? proof :
                Path.Combine(session, ".deep-checks/BindingAudit/Bodies.lean");
            File.AppendAllText(target, "\n-- changed\n");
            File.WriteAllText(marker, "mutated");
        }), originalProofMutation ? "Inputs changed during consumer verification" : "Deep-check source changed");
        var normalization = File.ReadLines(Path.Combine(trace, TraceFile))
            .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
            .Single(record => record.GetProperty("stage").GetString() == "Canonical module fingerprints");
        var command = normalization.GetProperty("command").EnumerateArray()
            .Select(value => value.GetString()).ToArray();
        var serializedIndex = Array.IndexOf(command, "serialized");
        if (!File.Exists(marker) || serializedIndex < 0 ||
            !int.TryParse(command[serializedIndex + 1], out var serialized) || serialized == 0)
            throw new InvalidOperationException("Export mutation did not follow actual module normalization.");
        RequireNoPublication(receipts);
        if (Directory.Exists(export) && Directory.EnumerateFiles(export, "*.json").Any())
            throw new InvalidOperationException("Rejected deep export published a support manifest.");
        Console.WriteLine("PASS deep export " + mutationName +
            " normalization mutation leaves no receipts, manifest or verified report");
    }
    finally
    {
        foreach (var (name, value) in variables) Environment.SetEnvironmentVariable(name, value);
        File.WriteAllText(configuration, originalConfiguration);
        File.WriteAllText(proof, originalProof);
        File.Delete(source);
    }
}

static void CheckDeep(Report report)
{
    BindingFact[] audited = [BindingFact.BodyBytes, BindingFact.MetadataRows, BindingFact.StaticData];
    if (report.binding.mode != BindingMode.Deep || report.binding.facts.Length != 14 ||
        report.binding.facts.Any(fact => fact.status !=
            (audited.Contains(fact.id) ? BindingStatus.Reconfirmed : BindingStatus.NotCovered)))
        throw new InvalidOperationException("Consumer deep report has incorrect binding coverage.");
}

SortedDictionary<string, string> Receipts() => Directory.Exists(SuccessCacheRoot)
    ? HashFiles(Directory.EnumerateFiles(SuccessCacheRoot, "receipt.*", SearchOption.AllDirectories)
        .Select(path => (path, path))) : new(StringComparer.Ordinal);

// The consumer session whose staged proof carries `token`.
static string ConsumerSession(string token) => Directory.EnumerateDirectories(Path.GetTempPath(), "leancil-consumer-*")
    .Single(directory => File.Exists(Path.Combine(directory, "LeanCILProof.lean")) &&
        File.ReadAllText(Path.Combine(directory, "LeanCILProof.lean")).Contains(token, StringComparison.Ordinal));

// Published deep results, the only entries that hold generated binding modules.
string[] DeepResults() => Directory.Exists(SuccessCacheRoot)
    ? [.. Directory.EnumerateDirectories(SuccessCacheRoot)
        .Where(entry => Directory.Exists(Path.Combine(entry, "files", "BindingAudit")))] : [];

SortedDictionary<string, string> ProofReceipts() => Directory.Exists(SuccessCacheRoot)
    ? HashFiles(Directory.EnumerateFiles(SuccessCacheRoot, "report.json", SearchOption.AllDirectories)
        .SelectMany(path => new[] { path,
            Path.Combine(Path.GetDirectoryName(Path.GetDirectoryName(path))!, "receipt.json"),
            Path.Combine(Path.GetDirectoryName(Path.GetDirectoryName(path))!, "receipt.hmac") })
        .Select(path => (path, path))) : new(StringComparer.Ordinal);

void RequireNoPublication(SortedDictionary<string, string> receipts)
{
    if (File.Exists(Path.Combine(output, "verified.json")) || !Same(receipts, Receipts()))
        throw new InvalidOperationException("Rejected deep verification published a success receipt or report.");
}

void Reject(string name, string diagnostic, string atStage, Action<string> mutation)
{
    var token = Guid.NewGuid().ToString("N");
    File.AppendAllText(proof, "\n-- " + token + "\n");
    bool mutated = false;
    var run = new DeepCheckRun(inputs);
    SortedDictionary<string, string>? receipts = null;
    ExpectFailure(() => Verify(verification, deepRun: run, stage: stage =>
    {
        if (stage != atStage || mutated) return;
        var session = Directory.EnumerateDirectories(Path.GetTempPath(), "leancil-consumer-*")
            .Single(directory => File.Exists(Path.Combine(directory, "LeanCILProof.lean")) &&
                File.ReadAllText(Path.Combine(directory, "LeanCILProof.lean"))
                    .Contains(token, StringComparison.Ordinal));
        receipts = Receipts();
        mutation(session);
        mutated = true;
    }), diagnostic);
    if (!mutated || receipts is null) throw new InvalidOperationException("Mutation was not exercised: " + name);
    RequireUnattributed(run);
    RequireNoPublication(receipts);
    Console.WriteLine("PASS consumer deep " + name + " mutation leaves no receipt or report");
}

static void RequireUnattributed(DeepCheckRun run)
{
    var failure = run.Attempt?.Failure("verification", "rejected")
        ?? throw new InvalidOperationException("Missing consumer deep attempt.");
    if (failure.facts.Any(fact => fact.status != FailureReports.BindingFailureStatus.NotCovered) ||
        failure.images.Any(item => item.status != FailureReports.BindingFailureStatus.NotCovered))
        throw new InvalidOperationException("An unclassified consumer failure marked a rejected subject.");
}

static void ExpectFailure(Action action, string diagnostic)
{
    try { action(); }
    catch (Exception error) when (error.Message.Contains(diagnostic, StringComparison.Ordinal)) { return; }
    throw new InvalidOperationException("Expected rejection containing " + diagnostic);
}
