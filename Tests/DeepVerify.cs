#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/BindingAudit.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include MultiAssemblyFixture.cs

using Program verification = new();
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
if (args is not ["--support-restore"])
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
if (args is not ["--support-restore"])
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
using (Program restoredSupport = new())
{
    bool audited = false;
    var restoredReport = restoredSupport.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
        stage: stage => audited |= stage == "theorem audit");
    var original = restoredSupport.bindingPreparation!;
    if (restoredSupport.supportCacheHits == 0 || !audited || restoredReport.binding.mode != BindingMode.Deep ||
        !Same(original.BaseArtifacts, ModuleArtifacts(restoredSupport.library!)) ||
        !BindingArtifactsPreserved(original.SessionArtifacts, ModuleArtifacts(restoredSupport.session!)) ||
        !BindingArtifactsPreserved(original.CertifiedArtifacts,
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
    ExpectFailure(() => verification.Verify(image, "DeepFixture", selector, proof, output, deepChecks: inputs,
        stage: stage =>
        {
            if (changed || stage != callback) return;
            var fresh = Directory.EnumerateDirectories(output, "proof-*").SingleOrDefault();
            if (fresh is null || !File.Exists(Path.Combine(fresh, "BindingAudit", "Bodies.olean"))) return;
            mutate(fresh);
            changed = true;
        }), marker);
    if (!changed) throw new InvalidOperationException("Mutation callback did not execute: " + name);
    RequireNoReport();
    Console.WriteLine("PASS " + name + " prevents deep report publication");
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
