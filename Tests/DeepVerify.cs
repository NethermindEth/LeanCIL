#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include MultiAssemblyFixture.cs
#:include DeepImportChecks.cs

using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

using Program verification = new();
bool focusedDiagnostics = args is ["--diagnostics"] or ["--diagnostic", _];
Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
SortedDictionary<string, string> retained = new(StringComparer.Ordinal) { ["Extracted.olean"] = "original" };
SortedDictionary<string, string> extended = new(retained, StringComparer.Ordinal)
{
    ["BindingAudit/Image.olean"] = "image",
    ["BindingAudit/Image.olean.private"] = "private"
};
RequireOnlyAdded(retained, extended, "BindingAudit/Image");
extended["BindingAudit/Image.oleanOther"] = "unexpected";
ExpectFailure(() => RequireOnlyAdded(retained, extended, "BindingAudit/Image"), "Compiled artifacts changed");
extended.Remove("BindingAudit/Image.oleanOther");
extended["Extracted.olean"] = "changed";
ExpectFailure(() => RequireOnlyAdded(retained, extended, "BindingAudit/Image"), "Compiled artifacts changed");
extended.Remove("Extracted.olean");
ExpectFailure(() => RequireOnlyAdded(retained, extended, "BindingAudit/Image"), "Compiled artifacts changed");
double previousInventoryMilliseconds = 0;
foreach (var count in new[] { 64, 512, 4096 })
{
    string[] modules = [.. Enumerable.Range(0, count).Select(index => "BindingAudit/I" + index)];
    SortedDictionary<string, string> built = new(retained, StringComparer.Ordinal);
    foreach (var module in modules) built[module + ".olean"] = "image";
    var milliseconds = double.MaxValue;
    for (var sample = 0; sample < 7; sample++)
    {
        var elapsed = System.Diagnostics.Stopwatch.StartNew();
        for (var repetition = 0; repetition < 64; repetition++) RequireOnlyAdded(retained, built, modules);
        milliseconds = Math.Min(milliseconds, elapsed.Elapsed.TotalMilliseconds);
    }
    if (previousInventoryMilliseconds > 0 && milliseconds > previousInventoryMilliseconds * 20 + 20)
        throw new InvalidOperationException("Artifact addition checks grew faster than n log n");
    previousInventoryMilliseconds = milliseconds;
    Console.WriteLine($"PASS {count} added module families checked 64 times in {milliseconds:F1} ms minimum");
}
if (args is ["--artifact-inventory"]) return;
MultiAssemblyFixture fixture = new("DeepVerify");
verification.EnsureExtractorBuilt();
var image = fixture.Build("Input", "DeepFixture", """
    public static class Input { public static ulong Value(ulong value) => value + 1; }
    """);
var proof = Path.Combine(fixture.Root, "Proof.lean");
File.WriteAllText(proof, """
    import Extracted
    import CIL.Safety.Execution
    import Tests.Support
    namespace ExampleProof
    theorem correctness :
        (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 2)] CIL.Safety.Memory.empty).map
          Prod.snd = .ok [.scalar (.i64 3)] := rfl
    #print axioms correctness
    end ExampleProof
    """);
var manifest = Path.Combine(fixture.Root, "inputs.sha256");
var unused = Path.Combine(fixture.Root, "unused.bin");
File.WriteAllBytes(unused, [1, 2, 3]);
File.WriteAllText(manifest, Sha(image) + "  " + Path.GetRelativePath(fixture.Root, image) + "\n" +
    Sha(unused) + "  " + Path.GetFileName(unused) + "\n");
var inputs = DeepCheckInputs.Read(manifest);
var output = fixture.Artifact("Verified");
const string selector = "Input::Value(System.UInt64)";
if (args is not ["--support-restore"] && !focusedDiagnostics)
using (Program attacked = new())
{
    attacked.Library(Inputs(proof));
    var originalCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", Path.Combine(fixture.Root, "SupportMutationCache"));
        string[]? receipts = null;
        ExpectFailure(() => attacked.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
            stage: stage =>
            {
                if (stage != "kernel replay" || receipts is not null) return;
                receipts = Receipts();
                var artifact = Path.Combine(attacked.session!, ".lake/build/lib/lean/StrictBinding.olean.unexpected");
                File.WriteAllBytes(artifact, [0]);
            }), "prepared StrictBinding library changed");
        if (receipts is null || !receipts.SequenceEqual(Receipts()))
            throw new InvalidOperationException("Rejected support mutation published a successful receipt");
        RequireNoReport();
    }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", originalCache); }
}
if (args is not ["--support-restore"] && !focusedDiagnostics)
    Console.WriteLine("PASS support replay mutation preserves no successful receipt or deep report");
if (args is ["--support-mutation"]) return;
var report = verification.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs);
// Each audited fact names the theorem that states it; every other fact stays not covered.
(BindingFact Fact, string Theorem)[] auditedFacts =
    [(BindingFact.BodyBytes, "BindingAudit.bodies"), (BindingFact.MetadataRows, "BindingAudit.metadataRows"),
     (BindingFact.StaticData, "BindingAudit.staticData")];
if (report.binding.mode != BindingMode.Deep ||
    report.binding.facts.Any(fact => auditedFacts.Any(audited => audited.Fact == fact.id)
        ? fact.status != BindingStatus.Reconfirmed ||
            fact.theorem != auditedFacts.Single(audited => audited.Fact == fact.id).Theorem
        : fact.status != BindingStatus.NotCovered) ||
    report.binding.images.Length != 2 || report.binding.images[0].status != BindingStatus.Reconfirmed ||
    report.binding.images[1].role != ImageRole.Unused ||
    report.binding.images[1].status != BindingStatus.NotCovered ||
    CertificateProblem(File.ReadAllText(Path.Combine(output, "verified.json")), BindingMode.Deep) is not null)
    throw new InvalidOperationException("Deep verification reported facts beyond its joint audit");
Console.WriteLine("PASS standalone verification reports exactly the deep facts it audited");
if (args is not ["--support-restore"]) CheckFailureDiagnostics();
if (focusedDiagnostics) return;
using (Program restoredSupport = new())
{
    bool audited = false;
    var restoredReport = restoredSupport.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
        stage: stage => audited |= stage == "theorem audit");
    var original = restoredSupport.bindingPreparation!;
    if (restoredSupport.supportCacheHits == 0 || !audited || restoredReport.binding.mode != BindingMode.Deep ||
        !restoredReport.binding.facts.SequenceEqual(report.binding.facts) ||
        !restoredReport.binding.images.SequenceEqual(report.binding.images) ||
        !Same(original.BaseArtifacts, ModuleArtifacts(restoredSupport.library!)) ||
        !ModuleArtifactsPreserved(original.SessionArtifacts, ModuleArtifacts(restoredSupport.session!)) ||
        !ModuleArtifactsPreserved(original.CertifiedArtifacts,
            restoredSupport.SessionModules(restoredSupport.session!)))
        throw new InvalidOperationException(
            "Authenticated support reuse changed the binding results or prepared library, or skipped audit");
}
Console.WriteLine("PASS authenticated support restoration preserves prepared families and runs a deep audit");
if (args is ["--support-restore"]) return;

var untrusted = Path.Combine(verification.session!, ".lake/build/lib/lean/Unexpected.olean");
File.WriteAllBytes(untrusted, [0]);
try
{
    ExpectFailure(() => verification.PrepareBindingLibrary(verification.session!), "certified library changed");
}
finally { File.Delete(untrusted); }
const string companionName = "StrictBinding.olean.unexpected";
var companion = Path.Combine(verification.session!, ".lake/build/lib/lean", companionName);
File.WriteAllBytes(companion, [0]);
verification.certifiedModules!.Add(companionName, Sha(companion));
try
{
    ExpectFailure(() => verification.PrepareBindingLibrary(verification.session!),
        "prepared StrictBinding library changed");
}
finally
{
    verification.certifiedModules.Remove(companionName);
    File.Delete(companion);
}
Console.WriteLine("PASS binding preparation rejects uncertified families and prepared-family additions");

var prepared = verification.bindingPreparation!;
var sessionFamilies = prepared.SessionArtifacts.Keys.Select(ModuleName).ToHashSet(StringComparer.Ordinal);
var baseOnly = prepared.BaseArtifacts.Keys.First(name => name.EndsWith(".olean", StringComparison.Ordinal) &&
    !sessionFamilies.Contains(ModuleName(name)));
var baseCompanionName = baseOnly + ".unexpected";
var baseCompanion = Path.Combine(verification.session!, ".lake/build/lib/lean", baseCompanionName);
Directory.CreateDirectory(Path.GetDirectoryName(baseCompanion)!);
File.WriteAllBytes(baseCompanion, [0]);
verification.certifiedModules.Add(baseCompanionName, Sha(baseCompanion));
try
{
    ExpectFailure(() => verification.PrepareBindingLibrary(verification.session!),
        "prepared StrictBinding library changed");
}
finally
{
    verification.certifiedModules.Remove(baseCompanionName);
    File.Delete(baseCompanion);
}
Console.WriteLine("PASS a base-only family's certified session companion is rejected on preparation reuse");
if (args is ["--prepared-inventory"]) return;

var subjects = BindingRequests(new("", [new("Identity", inputs.Images[0].Digest, [])], 1));
// Exercise report projection and scaling with the same literal term shape as the joint audit.
static AuditedTheorem IncompleteCoverage(string theorem, string predicate) => new(theorem, null, [], null, null,
    JsonSerializer.SerializeToElement(new { root = 2, nodes = new object[] {
        new object[] { "const", 0, new[] { "StrictBinding", predicate }, Array.Empty<object>() },
        new object[] { "const", 0, new[] { "Bool", "false" }, Array.Empty<object>() },
        new object[] { "app", 0, 1 } } }));
var conditional = subjects.Where(request => request.CoveragePredicate is not null).ToArray();
AuditedOleans coverageAudit = new(new(), [.. conditional.Select(request =>
    IncompleteCoverage(request.Audit.name, request.CoveragePredicate!))], []);
var withoutRows = DeepBindingSection(inputs, [new("Identity", inputs.Images[0])],
    [.. subjects.Where(request => request.Module != MetadataRowsModule)], report.binding.sources!, coverageAudit);
if (conditional.Select(request => ((BindingSubject.Fact)request.Subject!).Value).Any(subject =>
        withoutRows.facts.Single(fact => fact.id == subject).status != BindingStatus.NotCovered) ||
    withoutRows.facts.Single(fact => fact.id == BindingFact.MetadataRows).status != BindingStatus.NotCovered ||
    withoutRows.facts.Single(fact => fact.id == BindingFact.BodyBytes).theorem != "BindingAudit.bodies")
    throw new InvalidOperationException("A fact without an audited request was reported as reconfirmed");
Console.WriteLine("PASS the deep report reconfirms exactly the subjects of its audited requests");
CheckDeepResultKey();
double previousMilliseconds = 0;
foreach (var count in new[] { 64, 512, 4096 })
{
    DeepCheckInputs.Pin[] pins = [.. Enumerable.Range(0, count)
        .Select(index => new DeepCheckInputs.Pin("Identity" + index, inputs.Images[0]))];
    var milliseconds = double.MaxValue;
    for (var sample = 0; sample < 7; sample++)
    {
        var elapsed = System.Diagnostics.Stopwatch.StartNew();
        for (var repetition = 0; repetition < 64; repetition++)
        {
            var section = DeepBindingSection(inputs, pins, subjects, report.binding.sources!, coverageAudit);
            if (section.images.Length != count + 1)
                throw new InvalidOperationException("Deep report lost an image association");
        }
        milliseconds = Math.Min(milliseconds, elapsed.Elapsed.TotalMilliseconds);
    }
    if (previousMilliseconds > 0 && milliseconds > previousMilliseconds * 20 + 20)
        throw new InvalidOperationException("Deep report construction grew faster than n log n");
    previousMilliseconds = milliseconds;
    Console.WriteLine($"PASS {count} image associations reported 64 times in {milliseconds:F1} ms minimum");
}

CheckDeepResultReuse();
if (args is ["--support-reuse"]) return;

Reject("generated source mutation", "Deep-check source changed", "theorem audit", fresh =>
    File.AppendAllText(Path.Combine(fresh, "BindingAudit", "Images.lean"), "\n-- changed\n"));
Reject("generated artifact mutation", "artifact", "theorem audit", fresh =>
    File.WriteAllBytes(Path.Combine(fresh, "BindingAudit", "Bodies.olean.unexpected"), [0]));
Reject("late source mutation", "Deep-check source changed", "extraction integrity", fresh =>
    File.AppendAllText(Path.Combine(fresh, "BindingAudit", "Bodies.lean"), "\n-- changed\n"));
Reject("added generated source", "Deep-check source changed", "theorem audit", fresh =>
    File.WriteAllText(Path.Combine(fresh, "BindingAudit", "Unexpected.lean"), "import BindingAudit.Bodies\n"));
ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
    stage: stage =>
    {
        if (stage != "deep checks") return;
        var fresh = Directory.EnumerateDirectories(output, "proof-*").Single();
        File.WriteAllBytes(Path.Combine(fresh, "Extracted.olean.unexpected"), [0]);
    }), "Compiled artifacts changed");
RequireNoReport();
Console.WriteLine("PASS a pre-build extraction companion mutation prevents deep report publication");
Reject("wrong body evidence", "Compiled artifacts changed", "theorem audit", fresh => WriteWrongBodies(fresh));
Reject("cold wrong body evidence", "Compiled artifacts changed", "kernel replay", fresh => WriteWrongBodies(fresh),
    Path.Combine(fixture.Root, "ColdRejectCache"));

var wrongManifest = Path.Combine(fixture.Root, "wrong.sha256");
File.WriteAllText(wrongManifest, Sha(unused) + "  " + Path.GetFileName(unused) + "\n");
ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output,
    deepChecks: DeepCheckInputs.Read(wrongManifest)), "No line of");
RequireNoReport();
Console.WriteLine("PASS missing pinned input rejects verification and removes its earlier report");

verification.fullImportAudit = (_, fresh, _, _) =>
{
    File.AppendAllText(Path.Combine(fresh, "BindingAudit", "Images.lean"), "\n-- changed\n");
    return new("composition", "", [], []);
};
try
{
    ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output,
        deepChecks: inputs), "Deep-check source changed");
    RequireNoReport();
}
finally { verification.fullImportAudit = null; }
Console.WriteLine("PASS import callback mutation prevents deep report publication");

var previousCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
var coldProof = Path.Combine(fixture.Root, "ColdProof.lean");
File.WriteAllText(coldProof, File.ReadAllText(proof) + "\n-- Separate proof input.\n");
var coldCache = Path.Combine(fixture.Root, "ColdCache");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", coldCache);
    string[]? receipts = null;
    ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, coldProof, output, deepChecks: inputs,
        stage: stage =>
        {
            if (stage == "deep checks") receipts = Receipts();
            if (stage != "extraction integrity" || receipts is null) return;
            var fresh = Directory.EnumerateDirectories(output, "proof-*").Single();
            File.AppendAllText(Path.Combine(fresh, "BindingAudit", "Images.lean"), "\n-- changed\n");
        }), "Deep-check source changed");
    if (receipts is null || !receipts.SequenceEqual(Receipts()))
        throw new InvalidOperationException("Rejected cold deep verification published a receipt");
    RequireNoReport();
}
finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", previousCache); }
Console.WriteLine("PASS rejected cold deep verification publishes no proof, extraction or deep result receipt");

string[] Receipts() => Directory.Exists(SuccessCacheRoot)
    ? [.. Directory.EnumerateFiles(SuccessCacheRoot, "receipt.json", SearchOption.AllDirectories)
        .Select(path => path + "=" + Sha(path)).Order(StringComparer.Ordinal)] : [];

// The certified library's StrictBinding sources are mutated only in the private copy Tests/DeepSession.cs opens.
var sessionToolchain = Path.Combine(verification.session!, "lean-toolchain");
var originalToolchain = File.ReadAllBytes(sessionToolchain);
try
{
    Reject("prepared toolchain mutation", "Deep-check sources, toolchain", "extraction integrity", _ =>
        File.AppendAllText(sessionToolchain, "\n"));
}
finally { File.WriteAllBytes(sessionToolchain, originalToolchain); }

// Each input of a deep result key, the StrictBinding sources by content alone, selects another key.
void CheckDeepResultKey()
{
    BindingImagePin[] pins = [new("Identity", inputs.Images[0].Digest, [])];
    var requests = BindingRequests(new("", pins, 1));
    string Key(string environment = "environment", string sources = "sources", string toolchain = "toolchain",
        char imported = 'a', char generated = 'b', BindingImagePin[]? pinned = null,
        BindingRequest[]? requested = null) => DeepResultKey(environment, sources, toolchain,
        new(StringComparer.Ordinal) { ["Extracted.olean"] = new string(imported, 64) },
        new(StringComparer.Ordinal) { ["BindingAudit/Bodies.lean"] = new string(generated, 64) },
        pinned ?? pins, requested ?? requests);
    var copy = Path.Combine(fixture.Root, "BindingSources");
    foreach (var source in Directory.EnumerateFiles(At("StrictBinding"), "*.lean", SearchOption.AllDirectories)
        .Append(At("StrictBinding.lean")))
    {
        var destination = Path.Combine(copy, Path.GetRelativePath(Root, source));
        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
        File.Copy(source, destination);
    }
    var original = BindingSourcesKey(copy);
    var edited = Path.Combine(copy, "StrictBinding.lean");
    var written = File.GetLastWriteTimeUtc(edited);
    var bytes = File.ReadAllBytes(edited);
    bytes[^1] ^= 1;
    File.WriteAllBytes(edited, bytes);
    File.SetLastWriteTimeUtc(edited, written);
    string[] changed = [Key("other"), Key(sources: BindingSourcesKey(copy)), Key(toolchain: "other"),
        Key(imported: 'c'), Key(generated: 'c'), Key(pinned: [new("Other", inputs.Images[0].Digest, [])]),
        Key(pinned: [new("Identity", Sha256Digest.Of([1]), [])]), Key(requested: requests[..^1])];
    if (Key() != Key() ||
        changed.Append(Key(sources: original)).Append(Key()).Distinct().Count() != changed.Length + 2)
        throw new InvalidOperationException("A deep result key ignores one of its inputs");
    Console.WriteLine("PASS a same-length StrictBinding change and every other deep result input change the key");
}

// One cache holds every run here, so whether each run restores its deep result is known.
void CheckDeepResultReuse()
{
    var previousCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", Path.Combine(fixture.Root, "ReuseCache"));
        var cold = DeepRun(image, selector, proof, output, inputs);
        Require(cold.DeepHits == 0 && cold.AfterDeepChecks.Contains("kernel replay") &&
            cold.AfterDeepChecks.Contains("theorem audit") && SameFacts(cold.Report),
            "A first deep request in an empty cache did not build, replay and audit its modules");
        RequireDeepImports(verification.deepImports, "standalone");
        var unchanged = DeepRun(image, selector, proof, output, inputs, check: true);
        Require(unchanged.DeepHits == 1 && unchanged.ProofHits == 1 &&
            unchanged.AfterDeepChecks.Contains("theorem audit") &&
            !unchanged.AfterDeepChecks.Contains("kernel replay") && SameFacts(unchanged.Report),
            "An unchanged deep request did not reuse its result under a fresh theorem audit");
        Console.WriteLine("PASS an unchanged deep request reuses its replayed modules and runs the theorem audit");

        var hitsBeforeImport = verification.deepCacheHits;
        ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
            stage: stage =>
            {
                if (stage != "deep-check sources") return;
                var fresh = Directory.EnumerateDirectories(output, "proof-*").Single();
                SameLengthChange(Path.Combine(fresh, "Extracted.olean"));
            }), "Deep-check artifact changed");
        Require(verification.deepCacheHits == hitsBeforeImport,
            "A deep result was restored over a changed imported module");
        RequireNoReport();
        Console.WriteLine("PASS a same-length imported module change with its write time restored is not restored");

        var changedProof = Path.Combine(fixture.Root, "ChangedProof.lean");
        File.WriteAllText(changedProof, File.ReadAllText(proof) + "\n-- A changed proof input.\n");
        var reproved = DeepRun(image, selector, changedProof, output, inputs);
        Require(reproved.DeepHits == 1 && reproved.ProofHits == 0 &&
            reproved.AfterDeepChecks.Contains("kernel replay") &&
            reproved.Output.Contains("\"auditFused\":false", StringComparison.Ordinal) && SameFacts(reproved.Report),
            "A changed proof did not reuse the deep result through the joint replay of the proof");
        Console.WriteLine("PASS a changed proof is replayed jointly while its deep result is reused");

        var entry = Directory.EnumerateDirectories(SuccessCacheRoot).Single(directory =>
            File.Exists(Path.Combine(directory, "files", "BindingAudit", "Bodies.olean")));
        var cachedBodies = Path.Combine(entry, "files", "BindingAudit", "Bodies.olean");
        var forged = Path.Combine(fixture.Root, "WrongBodies.olean");
        ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
            stage: stage =>
            {
                if (stage != "theorem audit" || File.Exists(forged)) return;
                var fresh = Directory.EnumerateDirectories(output, "proof-*").Single();
                WriteWrongBodies(fresh);
                File.Copy(Path.Combine(fresh, "BindingAudit", "Bodies.olean"), forged);
            }), "Compiled artifacts changed");
        File.Copy(forged, cachedBodies, true);
        var manifest = JsonSerializer.SerializeToUtf8Bytes(CacheFiles(Path.Combine(entry, "files")));
        File.WriteAllBytes(Path.Combine(entry, "receipt.json"), manifest);
        File.WriteAllBytes(Path.Combine(entry, "receipt.hmac"), HMACSHA256.HashData(verification.ReceiptKey,
            Encoding.UTF8.GetBytes(Path.GetFileName(entry)).Concat(manifest).ToArray()));
        var deepHits = verification.deepCacheHits;
        var audited = new DeepCheckRun(inputs);
        ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
            deepRun: audited), "Theorem statement mismatch");
        Require(verification.deepCacheHits == deepHits + 1 && audited.Attempt!.Failure("theorem audit", "rejected")
            .facts.Single(fact => fact.id == "body-bytes").status == FailureReports.BindingFailureStatus.Failed,
            "The theorem audit did not reject a restored body module that states another fact");
        RequireNoReport();
        Console.WriteLine("PASS the theorem audit rejects an authenticated restored module that states another fact");

        SameLengthChange(cachedBodies);
        var changedBodies = File.ReadAllBytes(cachedBodies);
        var previousReplay = Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY");
        (Report Report, string[] AfterDeepChecks, string Output, int DeepHits, int ProofHits) rebuilt;
        try
        {
            // The cold run takes the separate replay that follows a rejected joint replay.
            Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", "true");
            rebuilt = DeepRun(image, selector, proof, output, inputs);
        }
        finally { Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", previousReplay); }
        Require(rebuilt.DeepHits == 0 && rebuilt.AfterDeepChecks.Contains("kernel replay") &&
            rebuilt.AfterDeepChecks.Contains("theorem audit") && SameFacts(rebuilt.Report),
            "A same-length change to a cached deep module with its timestamp restored was restored");
        Require(verification.AuthenticatedSuccess(Path.GetFileName(entry)) is not null &&
            !File.ReadAllBytes(cachedBodies).SequenceEqual(changedBodies),
            "A rebuilt deep result did not replace the changed entry");
        Console.WriteLine("PASS a changed cached deep module runs a complete cold deep audit and is replaced");

        var variant = fixture.Build("Variant", "DeepFixture", """
            public static class Input
            {
                public static ulong Value(ulong value) => value | 1;
                public static ulong Other(ulong value) => value + 1;
            }
            """);
        var variantDigests = Path.Combine(fixture.Root, "variant.sha256");
        File.WriteAllText(variantDigests, Sha(variant) + "  " + Path.GetRelativePath(fixture.Root, variant) + "\n");
        var variantInputs = DeepCheckInputs.Read(variantDigests);
        Require(DeepRun(variant, selector, proof, fixture.Artifact("Variant"), variantInputs).DeepHits == 0,
            "A changed instruction in the library reused a deep result");
        Require(DeepRun(variant, "Input::Other(System.UInt64)", proof, fixture.Artifact("VariantOther"),
            variantInputs).DeepHits == 0, "Another entry method of one image reused a deep result");
        Console.WriteLine("PASS a changed library instruction and another entry method of one image miss");
    }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", previousCache); }
}

// Runs one deep request with its stages from the deep checks on, its standard output and its cache hits.
(Report Report, string[] AfterDeepChecks, string Output, int DeepHits, int ProofHits) DeepRun(string assembly,
    string entry, string proofPath, string outputPath, DeepCheckInputs digests, bool check = false)
{
    List<string> stages = [];
    var deepHits = verification.deepCacheHits;
    var proofHits = verification.proofCacheHits;
    var previousOutput = Console.Out;
    using var captured = new StringWriter();
    Report result;
    try
    {
        Console.SetOut(captured);
        result = verification.Verify(assembly, "DeepFixture", entry, proofPath, outputPath, check: check,
            deepChecks: digests, stage: stages.Add);
    }
    finally
    {
        Console.SetOut(previousOutput);
        Console.Write(captured.ToString());
    }
    return (result, [.. stages.SkipWhile(stage => stage != "deep checks")], captured.ToString(),
        verification.deepCacheHits - deepHits, verification.proofCacheHits - proofHits);
}

bool SameFacts(Report checkedReport) => checkedReport.binding.facts
    .Select(fact => (fact.id, fact.status, fact.theorem))
    .SequenceEqual(report.binding.facts.Select(fact => (fact.id, fact.status, fact.theorem)));

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

// A run with a cold cache builds its deep modules; any other run restores those an earlier run published.
void Reject(string name, string marker, string callback, Action<string> mutate, string? coldCache = null)
{
    bool changed = false;
    var run = new DeepCheckRun(inputs);
    var deepHits = verification.deepCacheHits;
    var previousCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
    try
    {
        if (coldCache is not null) Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", coldCache);
        ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
            deepRun: run,
            stage: stage =>
            {
                if (changed || stage != callback) return;
                var fresh = Directory.EnumerateDirectories(output, "proof-*").SingleOrDefault();
                if (fresh is null || !File.Exists(Path.Combine(fresh, "BindingAudit", "Bodies.olean"))) return;
                mutate(fresh);
                changed = true;
            }), marker);
    }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", previousCache); }
    if (!changed) throw new InvalidOperationException("Mutation callback did not execute: " + name);
    if (verification.deepCacheHits != deepHits + (coldCache is null ? 1 : 0))
        throw new InvalidOperationException("Mutation ran on the wrong deep result path: " + name);
    RequireUnattributed(run, callback);
    RequireNoReport();
    Console.WriteLine("PASS " + name + " prevents deep report publication");
}

// Replaces the body theorem with one about no evidence and compiles it over the generated module.
void WriteWrongBodies(string fresh)
{
    var source = Path.Combine(fresh, "BindingAudit", "Bodies.lean");
    var text = File.ReadAllText(source);
    var start = text.IndexOf("theorem bodies :", StringComparison.Ordinal);
    if (start < 0) throw new InvalidOperationException("Missing body theorem");
    File.WriteAllText(source, text[..start] + """
        theorem bodies : StrictBinding.BodiesBound images [] := StrictBinding.claimsHold_nil Bodies.prepared
        #print axioms bodies
        end BindingAudit
        """);
    Run([verification.LeanExecutable, "--root=" + fresh, "-o", Path.ChangeExtension(source, ".olean"), source],
        leanPath: fresh + Path.PathSeparator + verification.SessionLeanPath(verification.session!));
}

void RequireUnattributed(DeepCheckRun run, string stage)
{
    var failed = run.Attempt?.Failure(stage, "rejected")
        ?? throw new InvalidOperationException("Missing begun deep attempt");
    if (failed.facts.Any(fact => fact.status != FailureReports.BindingFailureStatus.NotCovered) ||
        failed.images.Any(item => item.status != FailureReports.BindingFailureStatus.NotCovered))
        throw new InvalidOperationException("Unclassified failure attributed a binding rejection");
}

// Changing one byte preserves the size and every other input byte.
static void WriteInputByte(string path, int offset, byte value)
{
    using var file = new FileStream(path, FileMode.Open, FileAccess.Write, FileShare.ReadWrite | FileShare.Delete);
    file.Position = offset;
    file.WriteByte(value);
}

void CheckFailureDiagnostics()
{
    using Program privateChecker = new();
    if (args is not ["--diagnostic", var selectedCase] ||
        selectedCase is "original-library" or "originals" or "replay-library" or "replay-auditor" or
            "kernel" or "kernel-remaining")
    {
        privateChecker.Library(Inputs(proof), writes: true);
        if (!privateChecker.ownsLibrary || privateChecker.libraryStamps is not null)
            throw new InvalidOperationException("Expected an owned private library for the integrity regression");
    }
    var priorCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", Path.Combine(fixture.Root, "DiagnosticsCache"));
    try
    {
        if (args is not ["--diagnostic", _])
        {
            var selected = new DeepCheckRun(inputs);
            ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output,
                theorem: "bad theorem", deepChecks: inputs, deepRun: selected), "Invalid theorem name");
            if (selected.Attempt is not null)
                throw new InvalidOperationException("Selection failure began an attempt");
            foreach (var early in new[] { "Lean library build", "proof checking", "kernel replay" })
            {
                File.AppendAllText(proof, "\n-- diagnostics " + Guid.NewGuid().ToString("N") + "\n");
                var run = new DeepCheckRun(inputs);
                ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output,
                    deepChecks: inputs, deepRun: run, stage: stage =>
                {
                    if (stage == early)
                    {
                        if (run.Attempt is null) throw new InvalidOperationException("Missing early attempt");
                        throw new InvalidOperationException("diagnostic resource failure");
                    }
                }), "diagnostic resource failure");
                RequireUnattributed(run, early);
                RequireNoReport();
            }
            Console.WriteLine("PASS selection leaves no attempt and library/proof/replay failures stay not covered");
        }

        foreach (var target in new[] { "body-type", "body-axiom", "digest-type", "images-type",
            "body-kernel", "digest-kernel", "images-kernel", "rows-page-kernel",
            "replay-proof", "replay-identity", "replay-library", "replay-assembly", "replay-auditor",
            "original-proof", "original-identity", "original-library", "original-assembly" })
        {
            if (args is ["--diagnostic", var only] && target != only &&
                !((only == "kernel" || only == "kernel-remaining" && target != "body-kernel") &&
                    (target.EndsWith("-kernel", StringComparison.Ordinal) ||
                        target.StartsWith("replay-", StringComparison.Ordinal))) &&
                !(only == "originals" && target.StartsWith("original-", StringComparison.Ordinal))) continue;
            bool kernelForgery = target.EndsWith("-kernel", StringComparison.Ordinal) ||
                target.StartsWith("replay-", StringComparison.Ordinal);
            var checker = target is "original-library" or "replay-library" or "replay-auditor"
                ? privateChecker : verification;
            var originalPath = target switch
            {
                "original-proof" or "replay-proof" => proof,
                "original-identity" or "replay-identity" => Path.Combine(output, "identity.json"),
                "original-library" or "replay-library" => Path.Combine(checker.library!, "CIL.lean"),
                "original-assembly" or "replay-assembly" => image,
                "replay-auditor" => checker.CheckedAuditExecutable(),
                _ => null
            };
            var originalBytes = originalPath is null ? null : File.ReadAllBytes(originalPath);
            var originalTime = originalPath is null ? default : File.GetLastWriteTimeUtc(originalPath);
            const int dosStubOffset = 0x50;
            var byteOffset = target is "original-assembly" or "replay-assembly" ? dosStubOffset : 0;
            var run = new DeepCheckRun(inputs);
            bool changed = false;
            bool originalChanged = false;
            string? savedAuditor = null;
            string lastStage = "";
            string[]? before = null;
            var diagnostic = target switch
            {
                "body-kernel" or "digest-kernel" or "images-kernel" or "rows-page-kernel" => "while replaying",
                "body-axiom" => "Unapproved proof axioms",
                "original-proof" or "replay-proof" => "Proof inputs changed",
                "original-identity" or "replay-identity" => "extraction identity changed",
                "original-library" or "replay-library" or "replay-auditor" => "certified library contents changed",
                "original-assembly" or "replay-assembly" => "assembly has changed since extraction",
                _ => "Theorem statement mismatch"
            };
            try
            {
                ExpectFailure(() => checker.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
                    deepRun: run, stage: stage =>
                {
                    lastStage = stage;
                    if (stage == (kernelForgery ? "replay diagnostics" : "theorem audit") &&
                        originalPath is not null && !originalChanged)
                    {
                        if (byteOffset == dosStubOffset && (originalBytes!.Length <= dosStubOffset ||
                            BitConverter.ToInt32(originalBytes, 0x3c) <= dosStubOffset))
                            throw new InvalidOperationException("Fixture has no DOS stub byte before the PE header");
                        // Keep the original runnable image outside the private library. Windows can rename
                        // a mapped executable even while it denies write access to its contents.
                        if (target == "replay-auditor" && OperatingSystem.IsWindows())
                        {
                            var saved = Path.Combine(Path.GetTempPath(), "leancil-auditor-" + Guid.NewGuid().ToString("N"));
                            File.Move(originalPath, saved);
                            savedAuditor = saved;
                            File.Copy(saved, originalPath);
                        }
                        WriteInputByte(originalPath, byteOffset, (byte)(originalBytes![byteOffset] ^ 1));
                        originalChanged = true;
                        File.SetLastWriteTimeUtc(originalPath, originalTime);
                    }
                    if (stage != "deep-check sources") return;
                    var fresh = Directory.EnumerateDirectories(output, "proof-*").Single();
                    if (target == "rows-page-kernel")
                    {
                        var rows = ModuleSource(fresh, MetadataRowsModule);
                        File.WriteAllText(rows, ForgedRowPage(File.ReadAllText(rows)));
                        changed = true;
                        before = Receipts();
                        return;
                    }
                    var module = target is "digest-type" or "digest-kernel" ? "I" + Sha(image)
                        : target is "images-type" or "images-kernel" ? "Images" : "Bodies";
                    var path = Path.Combine(fresh, "BindingAudit", module + ".lean");
                    var source = File.ReadAllText(path);
                    var theorem = target is "digest-type" or "digest-kernel" ? "digest"
                        : target is "images-type" or "images-kernel" ? "images_eq" : "bodies";
                    var start = source.IndexOf("theorem " + theorem + " :", StringComparison.Ordinal);
                    if (start < 0) throw new InvalidOperationException("Missing generated theorem");
                    var ns = target is "digest-type" or "digest-kernel" ? "BindingAudit." + module : "BindingAudit";
                    string replacement = target == "body-axiom"
                        ? "axiom cheat : StrictBinding.BodiesBound images Extracted.methodEvidence\n" +
                            "theorem bodies : StrictBinding.BodiesBound images Extracted.methodEvidence := cheat\n"
                        : "theorem " + theorem + " : True := True.intro\n";
                    if (kernelForgery)
                    {
                        var documentation = source.LastIndexOf("/--", start, StringComparison.Ordinal);
                        if (documentation >= 0) start = documentation;
                        replacement = $$"""
                            set_option debug.skipKernelTC true in
                            run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
                              name := `{{ns}}.{{theorem}}
                              levelParams := []
                              type := Lean.mkConst ``False
                              value := Lean.mkConst ``True.intro
                            })

                            """;
                    }
                    File.WriteAllText(path, (kernelForgery ? "import Lean\n" : "") + source[..start] +
                        replacement + "#print axioms " + theorem +
                        "\nend " + ns + "\n");
                    changed = true;
                    before = Receipts();
                }), diagnostic);
            }
            finally
            {
                if (savedAuditor is not null)
                {
                    var changedAuditor = savedAuditor + ".changed";
                    if (File.Exists(originalPath)) File.Move(originalPath, changedAuditor);
                    File.Move(savedAuditor, originalPath!);
                    File.Delete(changedAuditor);
                }
                else if (originalChanged)
                {
                    WriteInputByte(originalPath!, byteOffset, originalBytes![byteOffset]);
                    File.SetLastWriteTimeUtc(originalPath!, originalTime);
                }
            }
            var failed = run.Attempt!.Failure("theorem audit", diagnostic);
            var failedFacts = failed.facts
                .Where(fact => fact.status == FailureReports.BindingFailureStatus.Failed)
                .Select(fact => fact.id).ToArray();
            var failedImages = failed.images.Where(item => item.status == FailureReports.BindingFailureStatus.Failed)
                .Select(item => item.sha256).ToArray();
            string[] expectedFacts = target.StartsWith("body-", StringComparison.Ordinal) ? ["body-bytes"]
                : target.StartsWith("rows-", StringComparison.Ordinal) ? ["metadata-rows"] : [];
            if (!changed || before is null || !before.SequenceEqual(Receipts()) ||
                !failedFacts.SequenceEqual(expectedFacts) ||
                !failedImages.SequenceEqual(target is "digest-type" or "digest-kernel" ? [Sha(image)] : []))
                throw new InvalidOperationException("Wrong named deep rejection attribution: " + target +
                    "; changed=" + changed + "; facts=" + string.Join(",", failedFacts) +
                    "; images=" + string.Join(",", failedImages) + "; receipts added=" +
                    string.Join(",", Receipts().Except(before ?? [])) + "; receipts removed=" +
                    string.Join(",", (before ?? []).Except(Receipts())));
            if (originalPath is not null)
            {
                if (!originalChanged) throw new InvalidOperationException("Original input mutation did not run");
                RequireUnattributed(run, lastStage);
            }
            else if (lastStage != (target.EndsWith("-kernel", StringComparison.Ordinal)
                ? "replay diagnostics" : "theorem audit"))
                throw new InvalidOperationException("Named rejection lost the theorem audit stage: " + lastStage);
            RequireNoReport();
            Console.WriteLine(originalPath is null
                ? "PASS named " + target + " rejection marks exactly its subject without publication"
                : "PASS " + target + " integrity failure leaves all subjects not covered without publication");
        }
    }
    finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", priorCache); }
}

// Row page 0 keeps its statement and takes a proof of True, which only kernel replay rejects.
static string ForgedRowPage(string source) => "import Lean\n" + source
    .Replace("theorem page0 :", "theorem page0_valid :", StringComparison.Ordinal)
    .Replace("end MetadataRows", """
        set_option debug.skipKernelTC true in
        run_cmd Lean.Elab.Command.liftCoreM do
          let valid <- Lean.getConstInfo `BindingAudit.MetadataRows.page0_valid
          Lean.addDecl (.thmDecl {
            name := `BindingAudit.MetadataRows.page0, levelParams := [], type := valid.type,
            value := Lean.mkConst ``True.intro })

        end MetadataRows
        """, StringComparison.Ordinal);

void RequireNoReport()
{
    if (File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Rejected deep verification left a successful report");
}

void ExpectFailure(Action action, string marker)
{
    try { action(); }
    catch (Exception error) when (error.Message.Contains(marker, StringComparison.Ordinal)) { return; }
    throw new InvalidOperationException("Expected rejection: " + marker);
}
