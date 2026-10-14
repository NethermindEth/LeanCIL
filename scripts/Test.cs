#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs

using System.Text.Json;

var suite = args switch
{
    [] => "all",
    ["--suite", "all" or "core" or "cli" or "integer" or "narrow" or "primitive" or "division" or "checked" or "conversions" or "native" or "arguments" or "layout" or "copy" or "bits" or "enums" or "nested" or "instance" or "constructors" or "fsharp" or "math"] => args[1],
    _ => throw new ArgumentException("Usage: dotnet run --file scripts/Test.cs -- [--suite all|core|cli|integer|narrow|primitive|division|checked|conversions|native|arguments|layout|copy|bits|enums|nested|instance|constructors|fsharp|math]")
};

using var verification = new Program();
var results = new List<string>();

var independentSuites = new Dictionary<string, (string Script, string Description)>
{
    ["math"] = ("Tests/IntegerMath.cs", "integer Math helpers, runtime faults and universal minimum"),
    ["fsharp"] = ("Tests/FSharp.cs", "F# arithmetic, branches, calls, references and struct construction"),
    ["constructors"] = ("Tests/Constructors.cs", "struct construction, initialized temporaries and constructor faults"),
    ["instance"] = ("Tests/StructMethods.cs", "struct instance calls, managed this and constructor calls"),
    ["nested"] = ("Tests/NestedStructs.cs", "nested struct layout, snapshots, copies and metadata validation"),
    ["enums"] = ("Tests/Enums.cs", "integer enum storage, flags, runtime comparisons and metadata validation"),
    ["cli"] = ("Tests/CliVerification.cs", "CLI proof verification and incorrect implementation rejection"),
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
    ["native"] = ("Tests/NativeIntegers.cs", "native integer storage, arithmetic and runtime comparisons")
};

void Passed(string name)
{
    results.Add(name);
    Console.WriteLine("PASS " + name);
}

void RunSuite(string name)
{
    var (script, description) = independentSuites[name];
    Console.Write(Run(["dotnet", "run", "--file", script]));
    Passed(description);
}

void SaveResults()
{
    Directory.CreateDirectory(At("artifacts"));
    File.WriteAllText(ResultsPath(), JsonSerializer.Serialize(new { suite, passed = results, count = results.Count }, Json) + "\n");
    Console.WriteLine($"All {results.Count} checks passed ({suite}).");
}

string ResultsPath() => At(suite == "all" ? "artifacts/test-results.json" : $"artifacts/test-results-{suite}.json");

// A failed run must never leave an earlier successful summary behind.
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
    projects.AddRange(["Examples/Hardware/Hardware.cs", "Examples/Verify.cs", "Tests/MetadataMutator.cs", "Tests/MethodSelectors.cs", "scripts/Verify.cs"]);
if (suite is "all" or "fsharp") projects.Add("Examples/FSharp");
foreach (var (name, entry) in independentSuites)
    if (suite == "all" || suite == name)
        projects.Add(entry.Script);

foreach (var project in projects)
{
    var command = new List<string>
    {
        "dotnet", "build", project, "-c", "Release",
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"
    };

    if (project == "Examples/Hardware/Hardware.cs")
        command.AddRange(["--output", "Examples/Hardware/bin"]);

    var log = Run(command);

    if (log.Contains("IDE0005"))
        throw new InvalidOperationException("Unused imports: " + log);
}

if (suite is not ("all" or "core"))
{
    RunSuite(suite);
    SaveResults();
    return;
}

// Check method selection before starting the longer Lean verification run.
Console.Write(Run(["dotnet", "run", "--file", "Tests/MethodSelectors.cs"]));
Passed("method selector aliases, overloads and actionable diagnostics");

Run(["lake", "build", "CIL", "Tests.Semantics", "Tests.Automation"]);
Passed("library and semantic tests");

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
    ["cycle"] = "cyclic control flow",
    ["initializer"] = "static initialisation",
    ["runtime-scope"] = "Unsupported type identity"
};

foreach (var (mutation, marker) in markers)
{
    var dll = At($"artifacts/mutations/{mutation}.dll");

    Run(["dotnet", "run", "--file", "Tests/MetadataMutator.cs", "--", assembly, dll, mutation]);
    Rejected(Extract("extract", dll, identity, signatures[mutation == "field" ? "Struct" : "Add"], At($"artifacts/mutations/{mutation}")), marker);
    Passed("metadata rejection: " + mutation);
}

// A short selector must not allow a rebuilt assembly to reuse an old report.
var changedVersionDll = At("artifacts/mutations/version.dll");

Run(["dotnet", "run", "--file", "Tests/MetadataMutator.cs", "--", assembly, changedVersionDll, "version"]);
Rejected(Extract("check", changedVersionDll, identity, signatures["Add"], At("artifacts/Add")), "Stale or mismatched");
Passed("changed assembly version rejected with short selector");

// Verify static data from an assembly with a generated RVA field.
var staticDll = At("artifacts/mutations/static.dll");

Run(["dotnet", "run", "--file", "Tests/MetadataMutator.cs", "--", assembly, staticDll, "static-data"]);
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

Rejected(Extract("check", assembly, identity, signatures["Add"], addOutput, "x64-avx2"), "Stale or mismatched");
Passed("different feature profile rejected");

// The default command still runs every suite locally.
if (suite == "all")
    foreach (var name in independentSuites.Keys)
        RunSuite(name);

// Write the summary only after every check succeeds.
SaveResults();
