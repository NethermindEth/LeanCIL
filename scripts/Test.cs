#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs
#:include ExportVerificationSuites.cs

using System.Text.Json;

string suite = args switch
{
    [] => "all",
    ["--suite", string name] when ExportVerificationSuites.Plan().Any(entry => entry.Name == name) => name,
    ["--suite", "all" or "core" or "contracts" or "cli" or "failures" or "integer" or "narrow" or "primitive" or "division" or "checked" or "conversions" or "native" or "arguments" or "layout" or "copy" or "bits" or "enums" or "nested" or "instance" or "constructors" or "fsharp" or "math" or "unsafe" or "blocks" or "generics" or "loops" or "evidence" or "identity" or "labels" or "names" or "symbols" or "callers" or "construction" or "outcomes" or "scaling" or "excluded" or "blockers" or "divrem" or "imports" or "exports" or "exceptionlint" or "intrinsics" or "audit"] => args[1],
    _ => throw new ArgumentException("Usage: dotnet run --file scripts/Test.cs -- [--suite all|core|contracts|cli|failures|integer|narrow|primitive|division|checked|conversions|native|arguments|layout|copy|bits|enums|nested|instance|constructors|fsharp|math|unsafe|blocks|generics|loops|evidence|identity|labels|names|symbols|callers|construction|outcomes|scaling|excluded|blockers|divrem|imports|exports|exceptionlint|intrinsics|audit]")
};

using var verification = new Program();
var results = new List<string>();
var preparedFixtures = new HashSet<string>(StringComparer.Ordinal);

void RunFixture(string script, string[] arguments, bool streamOutput = false, string? progress = null)
{
    Run(FixtureCommand(script, arguments, preparedFixtures.Contains(script)),
        streamOutput: streamOutput, progress: progress);
}

var independentSuites = new Dictionary<string, (string Script, string Description)>
{
    ["imports"] = ("Tests/ContractImports.cs", "implementation-bound contract imports and conditional caller verification"),
    ["exceptionlint"] = ("Tests/ExceptionLint.cs", "diagnostic XML exception drift without proof claims"),
    ["contracts"] = ("Tests/UniversalContracts.cs", "universal checked contracts, caller memory preservation and incorrect implementations"),
    ["evidence"] = ("Tests/ExtractionEvidence.cs", "independent extraction certificates and malformed evidence rejection"),
    ["loops"] = ("Tests/Loops.cs", "cyclic control-flow validation, universal termination and negative contracts"),
    ["generics"] = ("Tests/GenericMethods.cs", "C# and F# generic method specialization, provenance and rejection proofs"),
    ["blocks"] = ("Tests/Blocks.cs", "block memory, alignment prefixes, runtime comparisons and safety faults"),
    ["unsafe"] = ("Tests/UnsafeLayouts.cs", "layout-based Unsafe sizes, reference offsets and metadata validation"),
    ["math"] = ("Tests/IntegerMath.cs", "integer Math helpers, runtime faults and universal minimum"),
    ["intrinsics"] = ("Tests/DivisionIntrinsics.cs", "division SIMD signatures, unspecified lanes, opaque locals and profile rejection"),
    ["divrem"] = ("Tests/TupleDivision.cs", "X86Base.X64.DivRem through ValueTuple fields, divide-error faults and layout rejection"),
    ["fsharp"] = ("Tests/FSharp.cs", "F# arithmetic, branches, calls, references and struct construction"),
    ["constructors"] = ("Tests/Constructors.cs", "struct construction, initialized temporaries and constructor faults"),
    ["instance"] = ("Tests/StructMethods.cs", "struct instance calls, managed this and constructor calls"),
    ["nested"] = ("Tests/NestedStructs.cs", "nested struct layout, snapshots, copies and metadata validation"),
    ["enums"] = ("Tests/Enums.cs", "integer enum storage, flags, runtime comparisons and metadata validation"),
    ["cli"] = ("Tests/CliVerification.cs", "CLI proof verification and incorrect implementation rejection"),
    ["failures"] = ("Tests/FailureReporting.cs", "failure reports that classify and locate each failed obligation"),
    ["integer"] = ("Tests/IntegerOpcodes.cs", "integer opcode encodings, boundary cases and universal negation proofs"),
    ["narrow"] = ("Tests/NarrowIntegers.cs", "narrow integer conversions, storage, method boundaries and rejection proofs"),
    ["primitive"] = ("Tests/PrimitiveOperations.cs", "primitive memory, switch, sizeof and rejection proofs"),
    ["division"] = ("Tests/Division.cs", "integer division and remainder runtime comparisons and proofs"),
    ["checked"] = ("Tests/CheckedArithmetic.cs", "checked integer arithmetic runtime comparisons and proofs"),
    ["conversions"] = ("Tests/CheckedConversions.cs", "checked integer conversions runtime comparisons and proofs"),
    ["layout"] = ("Tests/SequentialLayout.cs", "sequential struct layout, runtime offsets and metadata validation"),
    ["bits"] = ("Tests/RuntimeBits.cs", "portable bit operations, endian reversal and runtime signature validation"),
    ["copy"] = ("Tests/TypedCopy.cs", "typed copies, aliases, byte snapshots and rejection proofs"),
    ["arguments"] = ("Tests/Arguments.cs", "argument assignment, addressing, aliases and lifetime proofs"),
    ["native"] = ("Tests/NativeIntegers.cs", "native integer storage, arithmetic and runtime comparisons"),
    ["identity"] = ("Tests/MethodIdentity.cs", "methods bound by signature or call shape that survive renumbering and renaming"),
    ["labels"] = ("Tests/StructuralLabels.cs", "loop-head and call-site labels that survive inserted statements"),
    ["names"] = ("Tests/DebugNames.cs", "PDB local names and source locations that never change extraction"),
    ["symbols"] = ("Tests/ConsumerSymbols.cs", "consumer proofs naming PDB locals through helper modules, bound only where imported"),
    ["callers"] = ("Tests/MethodContract.cs", "caller proofs that survive reimplemented helpers through their contracts"),
    ["construction"] = ("Tests/ConstructContract.cs", "caller proofs that survive reimplemented constructors through their contracts"),
    ["outcomes"] = ("Tests/OutcomeContract.cs", "outcome contracts that name exactly when each exception is thrown"),
    // Split from evidence: each fixture alone runs for minutes, so they take separate runners.
    ["scaling"] = ("Tests/TranslationScaling.cs", "compositional certificate for a six-method call graph and its consumer replay"),
    ["excluded"] = ("Tests/ExcludedBranchScaling.cs", "hundreds of excluded and live sites at the default heartbeat budget"),
    ["blockers"] = ("Tests/Blockers.cs", "admission reports with deduplicated blockers, call chains and profile-excluded branches"),
    ["audit"] = ("Tests/OleanAudit.cs", "theorem audits of replayed oleans that proof elaborators, initializers and substituted artifacts cannot forge")
};
foreach (ExportSuite entry in ExportVerificationSuites.Plan())
    independentSuites.Add(entry.Name, (entry.Script, entry.Description));

void Passed(string name)
{
    results.Add(name);
    Console.WriteLine("PASS " + name);
}

void RunSuite(string name)
{
    (string script, string description) = independentSuites[name];
    ExportSuite? export = ExportVerificationSuites.Plan().FirstOrDefault(entry => entry.Name == name);
    string[] arguments = export?.Arguments ?? [];
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
File.Delete(ResultsPath());

void Rejected(string[] command, string marker)
{
    var result = Execute(command);

    if (result.Code == 0 || !result.Output.Contains(marker))
        throw new InvalidOperationException($"Expected rejection ({marker}): {result.Code}\n{result.Output}");
}

var assembly = At("Examples/Assembly/bin/Examples.dll");
const string identity = "Examples";

var signatures = new Dictionary<string, string>
{
    ["Add"] = "System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)",
    ["Choose"] = "System.UInt64 Examples.Arithmetic::Choose(System.Boolean,System.UInt64,System.UInt64)",
    ["Calls"] = "System.UInt64 Examples.Arithmetic::Calls(System.UInt64)",
    ["Alias"] = "System.UInt64 Examples.Arithmetic::Alias(System.UInt64&,System.UInt64&)",
    ["Struct"] = "System.UInt64 Examples.Arithmetic::Struct(System.UInt64)",
    ["StructCopy"] = "System.UInt64 Examples.Arithmetic::StructCopy(System.UInt64)",
    ["LargeStruct"] = "System.UInt64 Examples.Arithmetic::LargeStruct(System.UInt64)",
    ["PastEnd"] = "System.UInt64 Examples.Arithmetic::PastEnd(System.UInt64&)",
    ["WrongAdd"] = "System.UInt64 Examples.Arithmetic::WrongAdd(System.UInt64,System.UInt64)",
    ["Escape"] = "System.UInt64& Examples.Arithmetic::Escape()"
};

// Each suite can run in its own checkout, with only the projects it needs.
var projects = new List<string> { "Extractor", "Examples/Assembly", "scripts/Test.cs" };
if (suite is "all" or "core")
    projects.AddRange(["Examples/Hardware/Hardware.cs", "Examples/Verify.cs", "Tests/MetadataMutator.cs", "Tests/MethodSelectors.cs", "Tests/LibraryCache.cs", "Tests/BuildReuse.cs", "Tests/VerificationCache.cs", "Tests/VerificationReuse.cs", "Tests/ExtractionBatch.cs", "Tests/BatchVerification.cs", "Tests/JointReplay.cs", "scripts/Verify.cs"]);
if (suite is "all" or "evidence")
    projects.AddRange(["Tests/LayoutEvidence.cs", "Tests/ParameterEvidence.cs", "Tests/GenericEvidence.cs", "Tests/FeatureEvidence.cs", "Tests/TypeTests.cs", "Tests/Throws.cs", "Tests/SpanTables.cs", "Tests/StaticValues.cs", "Tests/TranslationAudit.cs", "Tests/NativeProbe"]);
if (suite is "all" or "fsharp" or "generics") projects.Add("Examples/FSharp");
if (suite is "all" or "unsafe") projects.AddRange(["Tests/SkipInitialization.cs", "Tests/NullReferences.cs"]);
foreach (var (name, entry) in independentSuites)
    if (suite == "all" || suite == name)
        projects.Add(entry.Script);
foreach (ExportSuite entry in ExportVerificationSuites.Plan())
    if (suite == "all" || suite == entry.Name)
        projects.AddRange(entry.Inputs.Where(path => path.EndsWith(".cs", StringComparison.Ordinal)));

foreach (string project in projects.Distinct(StringComparer.Ordinal))
{
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

Environment.SetEnvironmentVariable(ExtractorBuildEnvironment, ExtractorBuildIdentity());

if (suite is "all" or "core" or "unsafe" or "evidence" or "scaling" or "excluded")
{
    // Direct semantic/evidence checks use the checkout's Lake build directory.
    // Seed it from the same validated private library instead of rebuilding CIL.
    var certified = verification.Library(Inputs(At("CIL.lean")));
    CopyTree(Path.Combine(certified, ".lake/build"), At(".lake/build"));
}

if (suite is not ("all" or "core"))
{
    RunSuite(suite);
    SaveResults();
    return;
}

// Check method selection before starting the longer Lean verification run.
RunFixture("Tests/LibraryCache.cs", [], streamOutput: true, progress: "Library cache checks");
Passed("library cache integrity and source keys");

RunFixture("Tests/BuildReuse.cs", [], streamOutput: true, progress: "Prepared build reuse checks");
Passed("prepared extractor source and output identity");

RunFixture("Tests/VerificationCache.cs", [], streamOutput: true, progress: "Certified verification cache checks");
Passed("certified artifact receipts and cache tampering rejection");

RunFixture("Tests/VerificationReuse.cs", [], streamOutput: true, progress: "Certified verification reuse checks");
Passed("cold and warm verification, proof-edit invalidation and unchecked helper rejection");

RunFixture("Tests/ExtractionBatch.cs", [], streamOutput: true, progress: "Extraction batch checks");
Passed("batched extraction identities, input freshness and failure isolation");

RunFixture("Tests/BatchVerification.cs", [], streamOutput: true, progress: "Generated verification batch checks");
Passed("batched extraction and proof checking, independent identities and negative regressions");

RunFixture("Tests/JointReplay.cs", [], streamOutput: true, progress: "Joint kernel replay checks");
Passed("joint kernel replay, untargeted-import fallback and forged declaration attribution");

RunFixture("Tests/InitializedTypes.cs", [], streamOutput: true, progress: "Initialization assumptions");
Passed("explicit type initialization assumptions and identity");
RunFixture("Tests/ConsumerVerification.cs", [], streamOutput: true, progress: "Consumer proof packages");
Passed("external consumer proof package and transitive source identity");
RunFixture("Tests/MethodSelectors.cs", [], streamOutput: true, progress: "Method selector checks");
Passed("method selector aliases, overloads and actionable diagnostics");

Run(["lake", "build", "CIL", "Tests.Semantics", "Tests.Automation", "Tests.MethodBinding", "Tests.MethodEmbedding", "Tests.OutcomeEmbedding", "Tests.InterpreterEquations", "Tests.MethodIdentity", "Tests.StructuralLabels", "Tests.DebugNames", "Tests.MethodContract", "Tests.ConstructContract", "Tests.OutcomeContract", "Tests.RuntimeExceptions", "Tests.Imports", "Tests.LoopOutcome", "Tests.ConfinedFootprints", "Tests.ContractConsequence", "Tests.BufferContents", "Tests.Linking", "Tests.ModularStatics", "Tests.StepFlow", "Tests.RegionRun", "Tests.StoreFacts"], streamOutput: true, progress: "Building Lean library, semantics and automation tests");
Passed("library, semantic, method-body binding, embedding, shared equation, method identity, structural label, debug name, method contract, constructor contract, outcome contract, contract import, loop outcome, footprint, contract consequence, buffer contents, linking and store fact tests");

// Verify each extracted method and immediately check its artifact identity.
foreach (var (name, signature) in signatures)
{
    var proof = At($"Examples/Proofs/{name}.lean");
    var output = At($"artifacts/{name}");

    verification.Verify(assembly, identity, name == "Add" ? "Arithmetic::Add(ulong,ulong)" : signature, proof, output);
    verification.Verify(assembly, identity, signature, proof, output, check: true);
    Passed(name + " kernel proof and artifact identity");
}

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
