#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/BindingAudit.cs
#:include ../scripts/DeepCheckInputs.cs
#:include MultiAssemblyFixture.cs

using System.Text.Json;
using System.Text.Json.Nodes;

if (args is ["--request-scaling"])
{
    foreach (var count in new[] { 16, 128, 1024 })
    {
        BindingImagePin[] pins = [.. Enumerable.Range(0, count).Select(index =>
            new BindingImagePin("Identity" + index, "", index.ToString("x64"), "stated", []))];
        BindingPlan plan = new("", "", "", "", pins, 0);
        var json = JsonSerializer.Serialize(BindingRequests(plan).Select(request => request.Audit), AuditJson);
        Console.WriteLine($"PASS {count} pins serialized in {json.Length} characters");
    }
    return;
}

using Program verification = new();
SortedDictionary<string, string> certifiedArtifacts = new(StringComparer.Ordinal)
{
    ["CIL.olean"] = "main",
    ["CIL.olean.private"] = "private"
};
SortedDictionary<string, string> builtArtifacts = new(certifiedArtifacts, StringComparer.Ordinal)
{
    ["StrictBinding.olean"] = "binding",
    ["StrictBinding.olean.private"] = "binding-private"
};
if (!BindingArtifactsPreserved(certifiedArtifacts, builtArtifacts))
    throw new InvalidOperationException("Binding preparation rejected an additional module family");
builtArtifacts["CIL.olean.private"] = "changed";
if (BindingArtifactsPreserved(certifiedArtifacts, builtArtifacts))
    throw new InvalidOperationException("Binding preparation accepted a changed certified companion");
builtArtifacts.Remove("CIL.olean.private");
if (BindingArtifactsPreserved(certifiedArtifacts, builtArtifacts))
    throw new InvalidOperationException("Binding preparation accepted a removed certified companion");
builtArtifacts["CIL.olean.private"] = "private";
builtArtifacts["CIL.olean.injected"] = "injected";
if (BindingArtifactsPreserved(certifiedArtifacts, builtArtifacts))
    throw new InvalidOperationException("Binding preparation accepted an added certified companion");
SortedDictionary<string, string> sessionArtifacts = new(StringComparer.Ordinal)
{
    ["CIL.olean.injected"] = "injected"
};
SortedDictionary<string, string> combinedArtifacts = new(certifiedArtifacts, StringComparer.Ordinal);
foreach (var (name, hash) in sessionArtifacts) combinedArtifacts[name] = hash;
if (!BindingArtifactsPreserved(new(StringComparer.Ordinal), sessionArtifacts) ||
    BindingArtifactsPreserved(certifiedArtifacts, combinedArtifacts))
    throw new InvalidOperationException("Binding preparation accepted a session companion for a base-only family");
Console.WriteLine("PASS binding builds preserve complete certified module families");
double previousInventoryMilliseconds = 0;
foreach (var count in new[] { 64, 512, 4096 })
{
    SortedDictionary<string, string> before = new(StringComparer.Ordinal);
    for (var index = 0; index < count; index++) before[$"M{index:D5}.olean"] = "bytes";
    SortedDictionary<string, string> after = new(before, StringComparer.Ordinal)
    {
        ["StrictBinding.olean"] = "binding"
    };
    const int repetitions = 64;
    var elapsed = System.Diagnostics.Stopwatch.StartNew();
    for (var repetition = 0; repetition < repetitions; repetition++)
    {
        after["StrictBinding.olean"] = repetition.ToString();
        if (!BindingArtifactsPreserved(before, after))
            throw new InvalidOperationException("Binding inventory scaling rejected an additional family");
    }
    var milliseconds = elapsed.Elapsed.TotalMilliseconds;
    if (previousInventoryMilliseconds > 0 && milliseconds > previousInventoryMilliseconds * 20 + 20)
        throw new InvalidOperationException("Binding inventory validation grew faster than n log n");
    previousInventoryMilliseconds = milliseconds;
    Console.WriteLine($"PASS {count} binding artifacts validated {repetitions} times in {milliseconds:F1} ms");
}
if (args is ["--artifact-inventory"]) return;
MultiAssemblyFixture fixture = new("DeepSession");
var artifactDirectory = Path.Combine(fixture.Root, "directory.olean.test");
Directory.CreateDirectory(artifactDirectory);
var testArtifact = Path.Combine(artifactDirectory, "Extracted.olean");
File.WriteAllBytes(testArtifact, [0]);
if (BindingArtifactHashes([testArtifact]).Count != 1)
    throw new InvalidOperationException("An artifact directory name hid its module");
File.Delete(testArtifact);
ExpectFailure(() => BindingArtifactHashes([testArtifact]), "missing");
Console.WriteLine("PASS artifact inventories include modules below .olean directories and reject missing modules");
var image = fixture.Build("Input", "DeepFixture", """
    public static class Input { public static int Value(int value) => value + 1; }
    """);
var extraction = fixture.Artifact("Input");
Run([.. fixture.Cli, "extract", image, "Input::Value(System.Int32)", extraction]);
var identity = ExtractionIdentity.Read(extraction);
var digest = Sha(image);
var digestFile = Path.Combine(fixture.Root, "inputs.sha256");
File.WriteAllText(digestFile, digest + "  " + Path.GetRelativePath(fixture.Root, image) + "\n");
var inputs = DeepCheckInputs.Read(digestFile);
var package = verification.Library(Inputs(At("CIL.lean")), writes: true);
var session = Path.Combine(fixture.Root, "session");
Directory.CreateDirectory(session);
var search = session + Path.PathSeparator + verification.SessionLeanPath(package);
var extractedSource = Path.Combine(session, "Extracted.lean");
var extractedOlean = Path.ChangeExtension(extractedSource, ".olean");
File.Copy(Path.Combine(extraction, "Extracted.lean"), extractedSource);
Compile(extractedSource);
File.Delete(extractedSource);
var retainedExtraction = BindingArtifactHashes([extractedOlean]);
var baseArtifact = Path.Combine(verification.library!, ".lake/build/lib/lean/CIL.olean");
var baseBytes = File.ReadAllBytes(baseArtifact);
File.WriteAllBytes(baseArtifact, [0]);
ExpectFailure(() => verification.PrepareBindingLibrary(package), "certified library changed");
File.WriteAllBytes(baseArtifact, baseBytes);
verification.PrepareBindingLibrary(package);
var preparedArtifacts = verification.SessionModules(package);
verification.PrepareBindingLibrary(package);
verification.bindingPreparation = null;
verification.PrepareBindingLibrary(package);
if (!Same(preparedArtifacts, verification.SessionModules(package)) ||
    !Same(retainedExtraction, BindingArtifactHashes([extractedOlean])))
    throw new InvalidOperationException("Repeated binding preparation changed compiled artifacts");
ExpectFailure(() => verification.PrepareBindingLibrary(session), "selected certified library session");
var bindingArtifact = Path.Combine(package, ".lake/build/lib/lean/StrictBinding.olean");
var bindingBytes = File.ReadAllBytes(bindingArtifact);
File.WriteAllBytes(bindingArtifact, [0]);
ExpectFailure(() => verification.PrepareBindingLibrary(package), "certified library changed");
File.WriteAllBytes(bindingArtifact, bindingBytes);
var addedCompanion = bindingArtifact + ".unexpected";
File.WriteAllBytes(addedCompanion, [0]);
ExpectFailure(() => verification.PrepareBindingLibrary(package), "certified library changed");
File.Delete(addedCompanion);
File.Delete(bindingArtifact);
ExpectFailure(() => verification.PrepareBindingLibrary(package), "certified library changed");
File.WriteAllBytes(bindingArtifact, bindingBytes);
var bindingSource = Path.Combine(package, "StrictBinding.lean");
var bindingSourceText = File.ReadAllText(bindingSource);
File.AppendAllText(bindingSource, "\n");
ExpectFailure(() => verification.PrepareBindingLibrary(package), "prepared StrictBinding library changed");
File.WriteAllText(bindingSource, bindingSourceText);
verification.PrepareBindingLibrary(package);
Console.WriteLine("PASS binding preparation reuses the selected library and rejects artifact and source mutations");
var proofSource = Path.Combine(session, "Proof.lean");
File.WriteAllText(proofSource, """
    import Extracted
    /-- The extracted program has the certificate checked in this same environment. -/
    theorem certificate : CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
        Extracted.methodEvidence Extracted.imports Extracted.program := Extracted.translation_valid
    #print axioms certificate
    """);
Compile(proofSource);
File.WriteAllBytes(image, [0]);
var contribution = verification.BuildDeepSession(session, search, extractedOlean, identity, inputs);
if (File.Exists(extractedSource)) throw new InvalidOperationException("Deep checks copied extraction source");
if (!contribution.Modules.Contains("BindingAudit.I" + digest))
    throw new InvalidOperationException("Image module does not use the complete digest");
var requests = contribution.Requests.Select(request => request.Audit).Append(ProofTheorem("certificate")).ToArray();
string[] jointModules = [.. contribution.Modules, "Proof"];
var audited = verification.AuditOleans(search, jointModules, requests, replayTargets: jointModules);
contribution.RequireAudited(audited);
RequireAuditedModule(audited, "Proof", Path.ChangeExtension(proofSource, ".olean"));
foreach (var theorem in audited.theorems) AuditedAxioms(theorem);
Console.WriteLine("PASS deep modules and proof share the existing extraction with retained image bytes");

var digestRequest = contribution.Requests.Single(request => request.Module == "BindingAudit.I" + digest).Audit;
var wrongDigest = JsonSerializer.SerializeToNode(digestRequest.type)!;
wrongDigest["app"]![2]!["nat"] = 0;
var wrongConstant = JsonSerializer.SerializeToNode(digestRequest.type)!;
wrongConstant["app"]![1]!["const"] = "BindingAudit.images";
var bodiesRequest = contribution.Requests.Single(request => request.Module == BodiesModule).Audit;
var wrongEvidence = JsonSerializer.SerializeToNode(bodiesRequest.type)!;
wrongEvidence["app"]![2]!["const"] = "Extracted.program";
AuditRequest[] rejected =
[
    digestRequest with { type = wrongDigest },
    digestRequest with { type = wrongConstant },
    bodiesRequest with { type = wrongEvidence }
];
var negative = verification.AuditOleans(search, [.. contribution.Modules, "Proof"],
    [.. rejected, ProofTheorem("certificate"), ExtractionCertificate("Extracted.translation_valid")]);
contribution.RequireAudited(negative);
if (negative.theorems.Take(3).Any(theorem => theorem.error is null) ||
    negative.theorems.Skip(3).Any(theorem => theorem.error is not null))
    throw new InvalidOperationException("Joint audit accepted a wrong digest, image constant or evidence constant");
Console.WriteLine("PASS joint audit rejects wrong digests, image constants and body evidence");

var originalOlean = File.ReadAllBytes(extractedOlean);
File.WriteAllBytes(extractedOlean, [0]);
ExpectFailure(contribution.RequireStable, "Deep-check artifact changed");
File.WriteAllBytes(extractedOlean, originalOlean);
foreach (var companion in Directory.EnumerateFiles(session, "Extracted.olean.*")
             .Where(path => path != extractedOlean))
{
    var original = File.ReadAllBytes(companion);
    File.WriteAllBytes(companion, [0]);
    ExpectFailure(contribution.RequireStable, "Deep-check artifact changed");
    File.WriteAllBytes(companion, original);
}
Console.WriteLine("PASS changed extraction artifact is detected");
foreach (var artifact in new[] { extractedOlean, contribution.Artifacts["BindingAudit.I" + digest] })
{
    var added = artifact + ".unexpected";
    File.WriteAllBytes(added, [0]);
    ExpectFailure(contribution.RequireStable, "Deep-check artifact changed");
    File.Delete(added);
    var unrelated = artifact + "Other";
    File.WriteAllBytes(unrelated, [0]);
    contribution.RequireStable();
    File.Delete(unrelated);
}
Console.WriteLine("PASS added module companions are rejected and unrelated prefix names are excluded");

var manifest = JsonNode.Parse(identity.Root.GetRawText())!;
manifest["references"] = new JsonArray(new JsonObject
{
    ["assemblyIdentity"] = "Missing",
    ["sha256"] = new string('0', 64)
});
using var missing = JsonDocument.Parse(manifest.ToJsonString());
ExpectFailure(() => inputs.MatchPins(missing.RootElement), "No line of");
Console.WriteLine("PASS every reference requires a consumer-stated digest");

var same = new BindingImagePin("First", "", digest, "stated", inputs.Images[0].Bytes.ToArray());
BindingPlan shared = new("", "", "", "", [same, same with { Identity = "Second" }], 0);
var sharedSource = ImagesModuleSource(shared);
if (sharedSource.Split("import " + same.Module).Length != 2 ||
    !sharedSource.Contains("identity := \"First\"", StringComparison.Ordinal) ||
    !sharedSource.Contains("identity := \"Second\"", StringComparison.Ordinal) ||
    BindingRequests(shared).Count(request => request.Module == same.Module) != 1)
    throw new InvalidOperationException("Equal digests lost an association or duplicated their image module");
Console.WriteLine("PASS equal digests share an image module and retain both identity associations");

var imageModule = "BindingAudit.I" + digest;
var imageSource = ModuleSource(session, imageModule);
var sourceText = File.ReadAllText(imageSource);
var digit = sourceText.IndexOf("  0x", StringComparison.Ordinal) + 4;
if (digit < 4) throw new InvalidOperationException("Missing image byte literal");
File.WriteAllText(imageSource, sourceText[..digit] + (sourceText[digit] == '0' ? '1' : '0') +
    sourceText[(digit + 1)..]);
Compile(imageSource);
ExpectFailure(() => verification.ReplayCheckedModules([imageModule], search, "Replay changed image"),
    imageModule + ".hash");
Console.WriteLine("PASS kernel replay rejects changed bytes in a deep-session image module");

void Compile(string source)
{
    var result = Execute([verification.LeanExecutable, "--root=" + session, "-o",
        Path.ChangeExtension(source, ".olean"), source], leanPath: search, environment: verification.LeanEnvironment);
    if (result.Code != 0) throw new InvalidOperationException(result.Output);
}

void ExpectFailure(Action action, string marker)
{
    try { action(); }
    catch (Exception error) when (error.Message.Contains(marker, StringComparison.Ordinal)) { return; }
    throw new InvalidOperationException("Expected failure: " + marker);
}
