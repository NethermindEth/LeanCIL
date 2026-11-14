#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/BindingAudit.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include MultiAssemblyFixture.cs

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
    var elapsed = System.Diagnostics.Stopwatch.StartNew();
    for (var repetition = 0; repetition < 64; repetition++) RequireOnlyAdded(retained, built, modules);
    var milliseconds = elapsed.Elapsed.TotalMilliseconds;
    if (previousInventoryMilliseconds > 0 && milliseconds > previousInventoryMilliseconds * 20 + 20)
        throw new InvalidOperationException("Artifact addition checks grew faster than n log n");
    previousInventoryMilliseconds = milliseconds;
    Console.WriteLine($"PASS {count} added module families checked 64 times in {milliseconds:F1} ms");
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
if (report.binding.mode != BindingMode.Deep ||
    report.binding.facts.Single(fact => fact.id == BindingFact.BodyBytes).status != BindingStatus.Reconfirmed ||
    report.binding.facts.Where(fact => fact.id != BindingFact.BodyBytes)
        .Any(fact => fact.status != BindingStatus.NotCovered) ||
    report.binding.images.Length != 2 || report.binding.images[0].status != BindingStatus.Reconfirmed ||
    report.binding.images[1].role != ImageRole.Unused ||
    report.binding.images[1].status != BindingStatus.NotCovered ||
    CertificateProblem(File.ReadAllText(Path.Combine(output, "verified.json")), BindingMode.Deep) is not null)
    throw new InvalidOperationException("Deep verification reported facts beyond its joint audit");
Console.WriteLine("PASS standalone verification reports exactly the deep facts it audited");
CheckFailureDiagnostics();
if (focusedDiagnostics) return;
using (Program restoredSupport = new())
{
    bool audited = false;
    var restoredReport = restoredSupport.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
        stage: stage => audited |= stage == "theorem audit");
    var original = restoredSupport.bindingPreparation!;
    if (restoredSupport.supportCacheHits == 0 || !audited || restoredReport.binding.mode != BindingMode.Deep ||
        !Same(original.BaseArtifacts, ModuleArtifacts(restoredSupport.library!)) ||
        !ModuleArtifactsPreserved(original.SessionArtifacts, ModuleArtifacts(restoredSupport.session!)) ||
        !ModuleArtifactsPreserved(original.CertifiedArtifacts,
            restoredSupport.SessionModules(restoredSupport.session!)))
        throw new InvalidOperationException(
            "Authenticated support reuse changed the prepared library or skipped audit");
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

double previousMilliseconds = 0;
foreach (var count in new[] { 64, 512, 4096 })
{
    DeepCheckInputs.Pin[] pins = [.. Enumerable.Range(0, count)
        .Select(index => new DeepCheckInputs.Pin("Identity" + index, inputs.Images[0]))];
    var elapsed = System.Diagnostics.Stopwatch.StartNew();
    for (var repetition = 0; repetition < 64; repetition++)
    {
        var section = DeepBindingSection(inputs, pins, report.binding.sources!);
        if (section.images.Length != count + 1)
            throw new InvalidOperationException("Deep report lost an image association");
    }
    var milliseconds = elapsed.Elapsed.TotalMilliseconds;
    if (previousMilliseconds > 0 && milliseconds > previousMilliseconds * 20 + 20)
        throw new InvalidOperationException("Deep report construction grew faster than n log n");
    previousMilliseconds = milliseconds;
    Console.WriteLine($"PASS {count} image associations reported 64 times in {milliseconds:F1} ms");
}

bool auditedAgain = false;
var previousProofHits = verification.proofCacheHits;
var previousReplay = Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", "true");
    verification.Verify(image, "DeepFixture", selector, proof, output, check: true, deepChecks: inputs,
        stage: stage => auditedAgain |= stage == "theorem audit");
}
finally { Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", previousReplay); }
if (!auditedAgain) throw new InvalidOperationException("Deep check reused a report without a fresh audit");
if (verification.proofCacheHits <= previousProofHits)
    throw new InvalidOperationException("Deep verification did not exercise a cached proof");
Console.WriteLine("PASS cached proof and check requests run a complete fallback deep audit");
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
Reject("wrong body evidence", "Compiled artifacts changed", "kernel replay", fresh =>
{
    var source = Path.Combine(fresh, "BindingAudit", "Bodies.lean");
    var text = File.ReadAllText(source);
    var start = text.IndexOf("theorem bodies :", StringComparison.Ordinal);
    if (start < 0) throw new InvalidOperationException("Missing body theorem");
    File.WriteAllText(source, text[..start] + """
        theorem bodies : StrictBinding.BodiesBound images [] := StrictBinding.claimsHold_nil prepared
        #print axioms bodies
        end BindingAudit
        """);
    Run([verification.LeanExecutable, "--root=" + fresh, "-o", Path.ChangeExtension(source, ".olean"), source],
        leanPath: fresh + Path.PathSeparator + verification.SessionLeanPath(verification.session!));
});

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
        throw new InvalidOperationException("Rejected cold deep verification published a successful receipt");
    RequireNoReport();
}
finally { Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", previousCache); }
Console.WriteLine("PASS rejected cold deep verification publishes no proof or extraction receipt");

string[] Receipts() => Directory.Exists(SuccessCacheRoot)
    ? [.. Directory.EnumerateFiles(SuccessCacheRoot, "receipt.json", SearchOption.AllDirectories)
        .Select(path => path + "=" + Sha(path)).Order(StringComparer.Ordinal)] : [];

foreach (var name in new[] { "source", "toolchain" })
{
    var path = Path.Combine(verification.session!, name == "source" ? "StrictBinding.lean" : "lean-toolchain");
    var original = File.ReadAllBytes(path);
    try
    {
        Reject("prepared " + name + " mutation", "Deep-check sources, toolchain", "extraction integrity", _ =>
            File.AppendAllText(path, "\n"));
    }
    finally { File.WriteAllBytes(path, original); }
}

void Reject(string name, string marker, string callback, Action<string> mutate)
{
    bool changed = false;
    var run = new DeepCheckRun(inputs);
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
    if (!changed) throw new InvalidOperationException("Mutation callback did not execute: " + name);
    RequireUnattributed(run, callback);
    RequireNoReport();
    Console.WriteLine("PASS " + name + " prevents deep report publication");
}

void RequireUnattributed(DeepCheckRun run, string stage)
{
    var failed = run.Attempt?.Failure(stage, "rejected")
        ?? throw new InvalidOperationException("Missing begun deep attempt");
    if (failed.facts.Any(fact => fact.status != FailureReports.BindingFailureStatus.NotCovered) ||
        failed.images.Any(item => item.status != FailureReports.BindingFailureStatus.NotCovered))
        throw new InvalidOperationException("Unclassified failure attributed a binding rejection");
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
            "body-kernel", "digest-kernel", "images-kernel",
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
            var run = new DeepCheckRun(inputs);
            bool changed = false;
            bool originalChanged = false;
            string lastStage = "";
            string[]? before = null;
            var diagnostic = target switch
            {
                "body-kernel" or "digest-kernel" or "images-kernel" => "while replaying",
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
                        var bytes = (byte[])originalBytes!.Clone();
                        const int dosStubOffset = 0x50;
                        var offset = target is "original-assembly" or "replay-assembly" ? dosStubOffset : 0;
                        if (target is "original-assembly" or "replay-assembly" &&
                            (bytes.Length <= dosStubOffset || BitConverter.ToInt32(bytes, 0x3c) <= dosStubOffset))
                            throw new InvalidOperationException("Fixture has no DOS stub byte before the PE header");
                        bytes[offset] ^= 1;
                        File.WriteAllBytes(originalPath, bytes);
                        File.SetLastWriteTimeUtc(originalPath, originalTime);
                        originalChanged = true;
                    }
                    if (stage != "deep-check sources") return;
                    var fresh = Directory.EnumerateDirectories(output, "proof-*").Single();
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
                if (originalPath is not null)
                {
                    File.WriteAllBytes(originalPath, originalBytes!);
                    File.SetLastWriteTimeUtc(originalPath, originalTime);
                }
            }
            var failed = run.Attempt!.Failure("theorem audit", diagnostic);
            var failedFacts = failed.facts
                .Where(fact => fact.status == FailureReports.BindingFailureStatus.Failed)
                .Select(fact => fact.id).ToArray();
            var failedImages = failed.images.Where(item => item.status == FailureReports.BindingFailureStatus.Failed)
                .Select(item => item.sha256).ToArray();
            string[] expectedFacts = target.StartsWith("body-", StringComparison.Ordinal) ? ["body-bytes"] : [];
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
