#!/usr/bin/env dotnet
#:property PublishAot=false
#:property EnforceCodeStyleInBuild=true
#:property GenerateDocumentationFile=true
#:include Verification.cs
#:include BatchVerification.cs
#:include CoreExamples.cs
#:include ExportVerificationSuites.cs
#:include VerificationSuites.cs

using System.Text.Json;

// A relocated shared runner must not execute an older suite plan after its source changes.
var fixtureManifest = Environment.GetEnvironmentVariable(FixtureManifestEnvironment);
if (!string.IsNullOrEmpty(fixtureManifest) &&
    typeof(Program).Assembly.Location.StartsWith(Path.GetDirectoryName(Path.GetFullPath(fixtureManifest))! +
        Path.DirectorySeparatorChar, StringComparison.OrdinalIgnoreCase) &&
    PreparedFixtureCommand("scripts/Test.cs", []) is null)
{
    Run(["dotnet", "run", "--file", At("scripts/Test.cs"), "--", .. args], streamOutput: true,
        environment: new Dictionary<string, string> { [FixtureManifestEnvironment] = "" });
    return;
}

string suite = args switch
{
    [] => "all",
    ["--build-tools"] => "tools",
    ["--suite", string name] when name == "all" || VerificationSuites.Names().Contains(name) => name,
    _ => throw new ArgumentException(
        $"Usage: dotnet run --file scripts/Test.cs -- [--suite all|{string.Join('|', VerificationSuites.Names())}]")
};

using var verification = new Program();
var results = new List<string>();
var preparedFixtures = new HashSet<string>(StringComparer.Ordinal);

void RunFixture(string script, string[] arguments, bool streamOutput = false, string? progress = null)
{
    Run(FixtureCommand(script, arguments, preparedFixtures.Contains(script)),
        streamOutput: streamOutput, progress: progress);
}

var independentSuites = VerificationSuites.Independent.ToDictionary(entry => entry.Name,
    entry => (entry.Script, entry.Description, Arguments: entry.Arguments ?? []), StringComparer.Ordinal);
foreach (ExportSuite entry in ExportVerificationSuites.Plan())
    independentSuites.Add(entry.Name, (entry.Script, entry.Description, entry.Arguments));

void Passed(string name)
{
    results.Add(name);
    Console.WriteLine("PASS " + name);
}

void RunSuite(string name)
{
    (string script, string description, string[] arguments) = independentSuites[name];
    RunFixture(script, arguments, streamOutput: true, progress: "Suite " + name);
    Passed(description);
}

void SaveResults()
{
    File.WriteAllText(ResultsPath(), JsonSerializer.Serialize(new { suite, passed = results, count = results.Count }, Json) + "\n");
    Console.WriteLine($"All {results.Count} checks passed ({suite}).");
}

string ResultsPath() => At(suite == "all" ? "artifacts/test-results.json" : $"artifacts/test-results-{suite}.json");

// A failed run must never leave an earlier successful summary behind; a fresh checkout has no artifacts/ yet.
Directory.CreateDirectory(At("artifacts"));
if (suite != "tools") File.Delete(ResultsPath());

void Rejected(string[] command, string marker)
{
    var result = Execute(command);

    if (result.Code == 0 || !result.Output.Contains(marker))
        throw new InvalidOperationException($"Expected rejection ({marker}): {result.Code}\n{result.Output}");
}

var assembly = At("Examples/Assembly/bin/Examples.dll");
const string identity = "Examples";

var signatures = CoreExampleSignatures;

// Each suite can run in its own checkout, with only the projects it needs.
string[] tools = ["Extractor", "Examples/Assembly"];
var projects = new List<string>(tools) { "scripts/Test.cs" };
if (suite == "tools") projects = [.. tools];
// CI builds the shared tools once per run and ships their outputs to every suite job.
else if (Environment.GetEnvironmentVariable(PrebuiltToolsEnvironment) == "true")
{
    if (!File.Exists(ExtractorPath) || !File.Exists(assembly))
        throw new InvalidOperationException(
            PrebuiltToolsEnvironment + " is set, but the extractor or example assembly is missing.");
    projects.RemoveAll(project => tools.Contains(project));
}
if (suite is "all" or "core")
    projects.AddRange(["Examples/Hardware/Hardware.cs", "Examples/Verify.cs", "Tests/MetadataMutator.cs",
        "Tests/MethodSelectors.cs", "Tests/LibraryCache.cs", "Tests/BuildReuse.cs", "Tests/VerificationCache.cs",
        "Tests/VerificationReuse.cs", "Tests/ExtractionBatch.cs", "Tests/InstructionIndexes.cs", "Tests/TemplateIndexes.cs", "Tests/ImportIndexes.cs", "Tests/StaticValueIndexes.cs",
        "Tests/BatchVerification.cs", "Tests/JointReplay.cs", "Tests/AllocationImports.cs", "scripts/Verify.cs",
        "Tests/EnvironmentLimit.cs", "Tests/ConsumerSupportCandidates.cs"]);
if (suite is "all" or "evidence")
    projects.AddRange(["Tests/MemorySpans.cs", "Tests/ReferenceInstructions.cs", "Tests/PointerOperations.cs",
        "Tests/PrimitiveArrays.cs", "Tests/ArrayElementReferences.cs", "Tests/ReadOnlyArrayReferences.cs",
        "Tests/Objects.cs", "Tests/Strings.cs", "Tests/Guards.cs"]);
if (suite is "all" or "dispatch")
    projects.AddRange(["Tests/ConstrainedResolution.cs", "Tests/ConstrainedCalls.cs", "Tests/ManagedDispatch.cs",
        "Tests/NativeManagedDispatch.cs", "Tests/StackAllocation.cs", "Tests/CompilerCoverage.cs",
        "Tests/RuntimeModelInventory.cs", "Tests/NativeProbe"]);
if (suite is "all" or "evidence")
    projects.AddRange([
        "Tests/PreparedLeanFixturesTests.cs", "Tests/RejectedEvidenceTests.cs", "Tests/LayoutEvidence.cs",
        "Tests/ParameterEvidence.cs", "Tests/GenericEvidence.cs", "Tests/FeatureEvidence.cs", "Tests/TypeTests.cs",
        "Tests/Throws.cs", "Tests/SpanTables.cs", "Tests/StaticValues.cs", "Tests/StaticScalarValues.cs",
        "Tests/TranslationAudit.cs"]);
if (suite is "all" or "blockers") projects.Add("Tests/SelfAdmission.cs");
if (suite is "all" or "fsharp" or "generics") projects.Add("Examples/FSharp");
if (suite is "all" or "generics") projects.AddRange(["Tests/GenericOwners.cs", "Tests/GenericLayouts.cs"]);
if (suite is "all" or "unsafe")
    projects.AddRange(["Tests/SkipInitialization.cs", "Tests/NullReferences.cs", "Tests/UnalignedMemory.cs",
        "Tests/MarshaledMemory.cs", "Tests/ReinterpretedSpans.cs", "Tests/SpanCopies.cs", "Tests/ViewAccessors.cs",
        "Tests/BinarySpans.cs", "Tests/AggregateSpans.cs", "Tests/SpanConstructors.cs",
        "Tests/AggregateSpanFill.cs", "Tests/AggregateArrays.cs", "Tests/SpanReferences.cs"]);
foreach (var (name, entry) in independentSuites)
    if (suite == "all" || suite == name)
        projects.Add(entry.Script);
foreach (ExportSuite entry in ExportVerificationSuites.Plan())
    if (suite == "all" || suite == entry.Name)
        projects.AddRange(entry.Inputs.Where(path => path.EndsWith(".cs", StringComparison.Ordinal)));

foreach (string project in projects.Distinct(StringComparer.Ordinal))
{
    if (project.EndsWith(".cs", StringComparison.Ordinal) && PreparedFixtureCommand(project, []) is not null)
        continue;
    var command = new List<string>
    {
        "dotnet", "build", project, "-c", "Release",
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"
    };

    if (project == "Examples/Hardware/Hardware.cs")
        command.AddRange(["--output", "Examples/Hardware/bin"]);

    var log = Run(command, streamOutput: true, progress: "Building " + project);

    if (log.Contains("IDE0005"))
        throw new InvalidOperationException("Unused imports: " + log);

    if (project.EndsWith(".cs", StringComparison.Ordinal) && project != "Examples/Hardware/Hardware.cs")
        preparedFixtures.Add(project);
}

if (suite == "tools") return;
Environment.SetEnvironmentVariable(ExtractorBuildEnvironment, ExtractorBuildIdentity());

if (suite is not ("all" or "core"))
{
    RunSuite(suite);
    SaveResults();
    return;
}

// Check method selection before starting the longer Lean verification run.
RunFixture("Tests/LibraryCache.cs", [], streamOutput: true, progress: "Library cache checks");
Passed("library cache integrity and source keys");

RunFixture("Tests/EnvironmentLimit.cs", [], streamOutput: true, progress: "Lean environment limit checks");
Passed("Lean environment blocks counted as Lean builds them and rejected before Lake drops LEAN_PATH");

RunFixture("Tests/BuildReuse.cs", [], streamOutput: true, progress: "Prepared build reuse checks");
Passed("prepared extractor source and output identity");

RunFixture("Tests/VerificationCache.cs", [], streamOutput: true, progress: "Certified verification cache checks");
Passed("certified artifact receipts and cache tampering rejection");

RunFixture("Tests/VerificationReuse.cs", [], streamOutput: true, progress: "Certified verification reuse checks");
Passed("cold and warm verification, proof-edit invalidation and unchecked helper rejection");

RunFixture("Tests/InstructionIndexes.cs", [], streamOutput: true, progress: "Instruction index checks");
RunFixture("Tests/TemplateIndexes.cs", [], streamOutput: true, progress: "Template index checks");
RunFixture("Tests/ImportIndexes.cs", [], streamOutput: true, progress: "Import index checks");
RunFixture("Tests/StaticValueIndexes.cs", [], streamOutput: true, progress: "Static value index checks");
Passed("instruction indexes and prefix target rejection");

RunFixture("Tests/ExtractionBatch.cs", [], streamOutput: true, progress: "Extraction batch checks");
Passed("batched extraction identities, input freshness and failure isolation");

RunFixture("Tests/BatchVerification.cs", [], streamOutput: true, progress: "Generated verification batch checks");
Passed("batched extraction and proof checking, independent identities and negative regressions");

RunFixture("Tests/JointReplay.cs", [], streamOutput: true, progress: "Joint kernel replay checks");
Passed("joint kernel replay, untargeted-import fallback and forged declaration attribution");

RunFixture("Tests/AllocationImports.cs", [], streamOutput: true, progress: "Selective allocation imports");
Passed("explicit allocation refinement imports, retained local initializers and complete kernel replay");

RunFixture("Tests/InitializedTypes.cs", [], streamOutput: true, progress: "Initialization assumptions");
Passed("explicit type initialization assumptions and identity");
RunFixture("Tests/ConsumerVerification.cs", [], streamOutput: true, progress: "Consumer proof packages");
Passed("external consumer proof package and transitive source identity");
RunFixture("Tests/ProofBindingCatalog.cs", [], streamOutput: true, progress: "Consumer binding catalogs");
Passed("binding catalogs as data, exact LF sources and check mode without writes");
RunFixture("Tests/GatePlans.cs", [], streamOutput: true, progress: "Gate plans and required results");
Passed("deterministic gate plans, plan groups and required results");
RunFixture("Tests/ProofCostFrontend.cs", [], streamOutput: true, progress: "Proof measurement imports");
Passed("proof measurements reject missing imports before diagnostic assertions");
RunFixture("Tests/ConsumerSupportCandidates.cs", ["--lake"], streamOutput: true,
    progress: "Coherent extraction restoration");
Passed("complete authenticated extraction generations remain stable during proof builds");
RunFixture("Tests/ProofBindingFamilies.cs", [], streamOutput: true, progress: "Generated integer binding families");
Passed("certified equality and bitwise binding families with rejected binding and body mutations");
RunFixture("Tests/MethodSelectors.cs", [], streamOutput: true, progress: "Method selector checks");
Passed("method selector aliases, overloads and actionable diagnostics");

Run(["lake", "build", "Tests.Semantics", "Tests.Automation", "Tests.MethodBinding", "Tests.MethodEmbedding",
    "Tests.OutcomeEmbedding", "Tests.InterpreterEquations", "Tests.MethodIdentity", "Tests.StructuralLabels",
    "Tests.DebugNames", "Tests.MethodContract", "Tests.ContractCalls", "Tests.ConstructContract", "Tests.OutcomeContract",
    "Tests.RuntimeExceptions", "Tests.Imports", "Tests.LoopOutcome", "Tests.ConfinedFootprints",
    "Tests.LocalSnapshots", "Tests.LocalSnapshotSteps", "Tests.AggregateFields", "Tests.LoopFrames",
    "Tests.WeakestPrecondition", "Tests.LocalCalls", "Tests.CallingFields", "Tests.OperationFacts",
    "Tests.VectorLocalCalls", "Tests.SimdCarryCalls", "Tests.OperationFactAdapters",
    "Tests.AggregateMemorySteps",
    "Tests.LoopDiagnostics", "Tests.ContractConsequence", "Tests.InvocationCertificates",
    "Tests.ValidCallTransport", "Tests.BufferContents", "Tests.Linking",
    "Tests.ModularStatics", "Tests.StepFlow", "Tests.RegionRun", "Tests.StoreFacts",
    "Tests.ProfileContract", "Tests.InstructionEquations", "Tests.CodeAt", "Tests.Segment", "Tests.SimdLanes",
    "Tests.LiteralDisplay", "Tests.PublicProofSurface", "Tests.BodyDecoding", "Tests.MetadataDecoding"],
    verification.CheckoutPackage(), streamOutput: true, progress: "Building semantics and automation tests");
Passed("library, semantic, method-body binding, embedding, shared equation, method identity, structural label, "
    + "debug name, method contract, constructor contract, outcome contract, contract import, loop outcome, footprint, "
    + "local snapshot, struct field view, loop frame, contract consequence, invocation certificate, call transport, "
    + "buffer contents, linking, "
    + "store fact, profile contract, instruction equation, code placement, SIMD lane and method body decoding tests");

verification.VerifyCoreExamples(At("artifacts"), Passed);

// Both selectors bind the same full identity; explicit mismatches must still fail.
const string fullIdentity = "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null";
Run(Extract("check", assembly, fullIdentity, signatures["Add"], At("artifacts/Add")));

var manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(At("artifacts/Add/identity.json")));

if (manifest.GetProperty("assemblyIdentity").GetString() != fullIdentity)
    throw new InvalidOperationException("Short selector did not retain the full assembly identity");

Passed("short and full assembly selectors retain exact identity");

foreach (var (field, wrongIdentity) in new[]
{
    ("version", fullIdentity.Replace("Version=1.0.0.0", "Version=2.0.0.0")),
    ("culture", fullIdentity.Replace("Culture=neutral", "Culture=en-US")),
    ("public key token", fullIdentity.Replace("PublicKeyToken=null", "PublicKeyToken=0000000000000000"))
})
{
    Rejected(Extract("check", assembly, wrongIdentity, signatures["Add"], At("artifacts/Add")), "assembly identity");
    Passed("explicit assembly identity mismatch rejected: " + field);
}

// Exercise feature selection with a separate assembly.
verification.Verify(At("Examples/Hardware/bin/Examples.Hardware.dll"),
    "Examples.Hardware", "System.Boolean Examples.Hardware::Available()",
    At("Examples/Proofs/Hardware.lean"), At("artifacts/Hardware"));
Passed("independent hardware assembly");

// The unchanged addition contract must reject the subtraction implementation.
var failed = false;

try
{
    verification.Verify(assembly, identity, signatures["WrongAdd"], At("Examples/Proofs/Add.lean"), At("artifacts/WrongContract"));
}
catch (InvalidOperationException error) when (error.Message.Contains("Tactic `rfl` failed"))
{
    failed = true;
}

if (!failed || File.Exists(At("artifacts/WrongContract/verified.json")))
    throw new InvalidOperationException("Incorrect arithmetic accepted or failed proof left a certificate");

Passed("incorrect addition rejected against unchanged universal contract");

// Unsupported instructions and malformed metadata must fail during extraction.
Rejected(Extract("extract", assembly, identity, "System.Int32 Examples.Arithmetic::Unsupported(System.Int32)", At("artifacts/Unsupported")), "Unsupported instruction");
Passed("unsupported array allocation rejected");

Directory.CreateDirectory(At("artifacts/mutations"));

var markers = new Dictionary<string, string>
{
    ["synchronized"] = "Unsupported method metadata",
    ["framework"] = "target framework",
    ["identity"] = "assembly identity",
    ["field"] = "Invalid field layout",
    ["local"] = "Unsupported type",
    ["initializer"] = "static initialisation",
    ["runtime-scope"] = "Unsupported type identity"
};

foreach (var (mutation, marker) in markers)
{
    var dll = At($"artifacts/mutations/{mutation}.dll");

    RunFixture("Tests/MetadataMutator.cs", [assembly, dll, mutation]);
    Rejected(Extract("extract", dll, identity, signatures[mutation == "field" ? "Struct" : "Add"], At($"artifacts/mutations/{mutation}")), marker);
    Passed("metadata rejection: " + mutation);
}

// A short selector must not allow a rebuilt assembly to reuse an old report.
var changedVersionDll = At("artifacts/mutations/version.dll");

RunFixture("Tests/MetadataMutator.cs", [assembly, changedVersionDll, "version"]);
Rejected(Extract("check", changedVersionDll, identity, signatures["Add"], At("artifacts/Add")), "Stale or mismatched");
Passed("changed assembly version rejected with short selector");

// Verify static data from an assembly with a generated RVA field.
var staticDll = At("artifacts/mutations/static.dll");

RunFixture("Tests/MetadataMutator.cs", [assembly, staticDll, "static-data"]);
verification.Verify(staticDll, identity, signatures["Add"], At("Examples/Proofs/StaticData.lean"), At("artifacts/StaticData"));
Passed("identity-bound static RVA data");

// Changing generated code, the assembly, the proof or the profile invalidates artifacts.
var addOutput = At("artifacts/Add");
var generated = Path.Combine(addOutput, "Extracted.lean");
var saved = File.ReadAllBytes(generated);

try
{
    File.AppendAllText(generated, "\n-- stale\n");
    Rejected(Extract("check", assembly, identity, signatures["Add"], addOutput), "Stale or mismatched");
}
finally
{
    File.WriteAllBytes(generated, saved);
}

Passed("tampered generated CIL rejected");

Rejected(Extract("check", staticDll, identity, signatures["Add"], addOutput), "Stale or mismatched");
Passed("different compiled assembly rejected");

failed = false;

try
{
    verification.Verify(assembly, identity, signatures["Add"], At("Examples/Proofs/Choose.lean"), addOutput, check: true);
}
catch (InvalidOperationException error) when (error.Message.Contains("Stale verification report"))
{
    failed = true;
}

if (!failed)
    throw new InvalidOperationException("Changed proof accepted");

Passed("changed proof identity rejected");

var reportPath = Path.Combine(addOutput, "verified.json");
var savedReport = File.ReadAllText(reportPath);
try
{
    var legacy = JsonSerializer.Deserialize<Report>(savedReport)! with { schema = 2 };
    File.WriteAllText(reportPath, JsonSerializer.Serialize(legacy, Json));
    failed = false;
    try
    {
        verification.Verify(assembly, identity, signatures["Add"], At("Examples/Proofs/Add.lean"), addOutput, check: true);
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Stale verification report"))
    {
        failed = true;
    }
    if (!failed)
        throw new InvalidOperationException("Legacy report without extraction certificate audit accepted");
}
finally
{
    File.WriteAllText(reportPath, savedReport);
}
Passed("legacy report without extraction certificate audit rejected");

Rejected(Extract("check", assembly, identity, signatures["Add"], addOutput, "x64-v3"), "Stale or mismatched");
Passed("different feature profile rejected");

// The default command still runs every suite locally.
if (suite == "all")
    foreach (var name in independentSuites.Keys)
        RunSuite(name);

// Write the summary only after every check succeeds.
SaveResults();
