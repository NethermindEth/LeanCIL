#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

var cli = args.Length == 0
    ? new[] { "dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll") }
    : new[] { Path.GetFullPath(args[0]) };
var output = At("artifacts/CliVerification");
var assembly = At("Examples/Assembly/bin/Examples.dll");
var proof = At("Examples/Proofs/Add.lean");
var settingsPath = Path.Combine(output, "verification.json");

void Verified(params string[] options)
{
    var result = Execute([.. cli, "verify", output, .. options]);

    if (result.Code != 0 || result.Stderr.Length != 0 || !result.Stdout.StartsWith("Verified: ExampleProof.correctness") ||
        !result.Stdout.Contains("Statement:") || !result.Stdout.Contains("BitVec.toNat") ||
        !result.Stdout.Contains("(x y : CIL.W64)"))
        throw new InvalidOperationException("CLI proof failed: " + result.Output);

    // Authors read the statement in Lean notation, as Unicode, and the proof's own `#print` output.
    var entry = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")))
        .GetProperty("entry").GetString();
    var stdout = result.Stdout.ReplaceLineEndings("\n");
    if (!stdout.Contains("\u2203 result,") || stdout.Contains("Exists fun") || stdout.Contains("HMod.hMod") ||
        !stdout.Contains($"  Subject: {entry} (method 0) via CIL.Safety.invoke\n") ||
        !stdout.Contains($"  Extraction entry: {entry}\n") || stdout.Contains("  Entry:") ||
        !stdout.Contains("Add.lean:15:0: info: 'ExampleProof.correctness' depends on axioms"))
        throw new InvalidOperationException(
            "CLI verification did not print the readable statement, subject and messages: " + result.Output);

    var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (report.GetProperty("schema").GetInt32() != 4 ||
        !report.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid"))
        throw new InvalidOperationException("Missing mandatory extraction certificate audit in report.");

    if (report.GetProperty("theorem").GetString() != "ExampleProof.correctness")
        throw new InvalidOperationException("Wrong theorem in CLI verification report.");

    if (!report.GetProperty("inputs").TryGetProperty("settings:" + Path.GetFullPath(settingsPath), out _))
        throw new InvalidOperationException("Verification settings are not bound to the report.");
}

// Build a disposable copy so the demonstration tests an actual source edit and rebuild.
var fixture = At("artifacts/CliDemoSource");
Directory.CreateDirectory(fixture);
foreach (var path in Directory.EnumerateFiles(At("Examples/Assembly")))
    if (Path.GetExtension(path) is ".cs" or ".csproj")
        File.Copy(path, Path.Combine(fixture, Path.GetFileName(path)), true);
Run(["dotnet", "build", fixture, "-c", "Release"]);
var demoAssembly = Path.Combine(fixture, "bin", "Examples.dll");

// Explicit proof selection becomes portable settings, separate from the generated report.
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", output]);
Verified("--proof", proof);
Verified("--fresh");
var settings = File.ReadAllText(settingsPath);
if (Path.IsPathRooted(JsonSerializer.Deserialize<JsonElement>(settings).GetProperty("proof").GetString()!))
    throw new InvalidOperationException("Expected a relative proof path in verification settings.");
Console.WriteLine("PASS CLI proof selection, persistent settings and theorem statement");

// Elaborator acceptance and an empty axiom list do not establish kernel validity.
// Test both a forged selected theorem and a normally checked theorem using a forged helper.
var auditOutput = At("artifacts/CliKernelAudit");
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", auditOutput]);
foreach (var transitive in new[] { false, true })
{
    var maliciousProof = Path.Combine(auditOutput, "Unchecked.lean");
    var forgedName = transitive ? "ExampleProof.helper" : "ExampleProof.correctness";
    File.WriteAllText(maliciousProof, $$"""
        import Extracted
        import Lean
        set_option debug.skipKernelTC true
        run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
          name := `{{forgedName}}
          levelParams := []
          type := Lean.mkConst ``False
          value := Lean.mkConst ``True.intro
        })
        set_option debug.skipKernelTC false
        {{(transitive ? "theorem ExampleProof.correctness : False := ExampleProof.helper" : "")}}
        """);
    // A failed attempt must also invalidate an earlier report.
    File.WriteAllText(Path.Combine(auditOutput, "verified.json"), "stale report");
    var invalid = Execute([.. cli, "verify", auditOutput, "--proof", maliciousProof]);
    if (invalid.Code != 1 || invalid.Stdout.Length != 0 ||
        !invalid.Stderr.Contains("Stage: kernel replay") ||
        !invalid.Stderr.Contains("while replaying declaration") ||
        File.Exists(Path.Combine(auditOutput, "verified.json")))
        throw new InvalidOperationException("Unchecked theorem bypassed kernel replay: " + invalid.Output);
}
Console.WriteLine("PASS CLI kernel replay rejects unchecked theorems and transitive helpers");

// The unchanged addition contract must fail after changing + to - and rebuilding.
var methodsPath = Path.Combine(fixture, "Methods.cs");
var methods = File.ReadAllText(methodsPath);
File.WriteAllText(methodsPath, methods.Replace("Add(ulong x, ulong y) => unchecked(x + y)", "Add(ulong x, ulong y) => unchecked(x - y)"));
Run(["dotnet", "build", fixture, "-c", "Release"]);
var stale = Execute([.. cli, "check", output]);
if (stale.Code != 1 || !stale.Stderr.Contains("assembly has changed") || !stale.Stderr.Contains("Next: Rerun leancil extract"))
    throw new InvalidOperationException("Missing actionable stale-assembly diagnostic: " + stale.Output);

Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", output]);
var rejected = Execute([.. cli, "verify", output]);

if (rejected.Code != 1 || rejected.Stdout.Length != 0 || !rejected.Stderr.StartsWith("Invalid:") ||
    !rejected.Stderr.Contains("error:") || !rejected.Stderr.Contains("Stage: proof checking") ||
    !rejected.Stderr.Contains("Next:") || File.Exists(Path.Combine(output, "verified.json")) ||
    File.ReadAllText(settingsPath) != settings)
    throw new InvalidOperationException("Incorrect implementation was not rejected by the proof: " + rejected.Output);

Console.WriteLine("PASS CLI incorrect implementation rejected without a successful report");

// Fixing the implementation needs no repeated proof arguments or previous success report.
File.WriteAllText(methodsPath, methods);
Run(["dotnet", "build", fixture, "-c", "Release"]);
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", output]);
Verified();
Console.WriteLine("PASS CLI verification settings survive failure and support recovery");

// This theorem proves invalid memory access cannot produce a successful execution.
var memoryOutput = At("artifacts/CliMemory");
Run([.. cli, "extract", assembly, "Arithmetic::PastEnd(ulong&)", memoryOutput]);
var memory = Execute([.. cli, "verify", memoryOutput, "--proof", At("Examples/Proofs/PastEnd.lean")]);
if (memory.Code != 0 || memory.Stderr.Length != 0 || !memory.Stdout.Contains("Statement:") ||
    !memory.Stdout.Contains("fuel") || !memory.Stdout.Contains("Except.ok"))
    throw new InvalidOperationException("Missing checked invalid-access theorem: " + memory.Output);
Console.WriteLine("PASS CLI invalid memory-access theorem");

// The tool ships only CIL; a proof importing a repository fixture must name it, not fail inside Lake.
foreach (var module in new[] { "Tests.Support", "Examples.Support" })
{
    var fixtureProof = Path.Combine(auditOutput, "Fixture.lean");
    File.WriteAllText(fixtureProof, $"import Extracted\nimport {module}\n");
    var fixtureImport = Execute([.. cli, "verify", auditOutput, "--proof", fixtureProof]);
    var failure = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(auditOutput, "failed.json")));
    if (fixtureImport.Code != 1 || !fixtureImport.Stderr.Contains("Stage: proof selection") ||
        !fixtureImport.Stderr.Contains($"imports {module}, a LeanCIL repository module") ||
        failure.GetProperty("kind").GetString() != "invalid-request")
        throw new InvalidOperationException("Repository fixture import was not rejected by name: " + fixtureImport.Output);
}
Console.WriteLine("PASS CLI rejects proofs importing repository fixtures the tool does not ship");

// Query commands are how authors explore the API: their output must survive a failed audit, located
// in the author's file, and long output must say where the rest is rather than vanish.
var queryProof = Path.Combine(auditOutput, "Query.lean");
File.WriteAllText(queryProof, "import Extracted\n#check CIL.Safety.invoke\n" +
    string.Concat(Enumerable.Range(0, 70).Select(i => $"#eval {i} + 1000\n")));
var query = Execute([.. cli, "verify", auditOutput, "--proof", queryProof]);
var queryErrors = query.Stderr.ReplaceLineEndings("\n");
var fullMessages = Path.Combine(auditOutput, "proof-messages.txt");
if (query.Code != 1 || !queryErrors.Contains("Stage: theorem audit") ||
    !queryErrors.Contains("Query.lean:2:0: info: CIL.Safety.invoke (program : CIL.Program) (fuel method : Nat)") ||
    !queryErrors.Contains("Except CIL.Safety.LocatedFault (CIL.Safety.Memory \u00d7 List CIL.Safety.Value)\n") ||
    !queryErrors.Contains("Query.lean:3:0: info: 1000\n") || queryErrors.Contains("info: 1069\n") ||
    !queryErrors.Contains(" more lines in artifacts/CliKernelAudit/proof-messages.txt\n") ||
!File.ReadAllText(fullMessages).Contains("info: 1069\n"))
    throw new InvalidOperationException("Proof query output was not shown with its location: " + query.Output);
Console.WriteLine("PASS CLI shows located #check and #eval output and keeps long output in proof-messages.txt");

// The report names the method a theorem is about, not the extraction entry, and claims nothing for an open index.
var subjectOutput = At("artifacts/CliSubjects");
Run([.. cli, "extract", demoAssembly, "Examples.Loops::TallyTwice(uint)", subjectOutput]);
var subjectProof = Path.Combine(subjectOutput, "Subjects.lean");
File.WriteAllText(subjectProof, """
    import Extracted
    import CIL.MethodIdentity
    import CIL.Safety.MethodContract
    namespace ExampleProof
    bind_method tally tallyBody := "System.UInt32 Examples.Loops::TallyTwice(System.UInt32)"
    bind_callee addTwo addTwoBody := "System.UInt32 Examples.Loops::AddTwo(System.UInt32)" from tallyBody
    theorem helper (contract : CIL.Safety.MethodContract CIL.W32 CIL.W32)
        (holds : contract.Holds Extracted.program addTwo) : contract.Holds Extracted.program addTwo := holds
    theorem unfixed (contract : CIL.Safety.MethodContract CIL.W32 CIL.W32) (method : Nat)
        (holds : contract.Holds Extracted.program method) : contract.Holds Extracted.program method := holds
    end ExampleProof
    """);
const string addTwo =
    "System.UInt32 Examples.Loops::AddTwo(System.UInt32) (method 1) via CIL.Safety.MethodContract.Holds";
var helper = Execute([.. cli, "verify", subjectOutput, "--proof", subjectProof, "--theorem", "ExampleProof.helper"])
    .Stdout.ReplaceLineEndings("\n");
if (!helper.Contains($"  Subject: {addTwo}\n") || !helper.Contains($"  Premise: {addTwo}\n") ||
    helper.Contains("Subject: System.UInt32 Examples.Loops::TallyTwice") ||
    !helper.Contains("  Extraction entry: System.UInt32 Examples.Loops::TallyTwice(System.UInt32)\n"))
    throw new InvalidOperationException("Helper theorem was not labelled by its subject: " + helper);
var unfixed = Execute([.. cli, "verify", subjectOutput, "--theorem", "ExampleProof.unfixed"])
    .Stdout.ReplaceLineEndings("\n");
if (!unfixed.Contains("  Subject: a method index the statement does not fix via CIL.Safety.MethodContract.Holds\n") ||
    unfixed.Contains("Examples.Loops::AddTwo") || unfixed.Contains("Subject: System.UInt32"))
    throw new InvalidOperationException("An unfixed method index was labelled as a specific method: " + unfixed);
Console.WriteLine("PASS CLI labels a theorem by the methods its statement names");

// A proof checked inside a consumer package is read by its author exactly like a standalone one, fresh or cached.
var consumerRoot = At("artifacts/CliConsumer");
if (Directory.Exists(consumerRoot)) Directory.Delete(consumerRoot, true);
var consumerPackage = Path.Combine(consumerRoot, "Package");
Directory.CreateDirectory(Path.Combine(consumerPackage, "Proofs"));
var revision = Execute(["git", "-C", Root, "rev-parse", "HEAD"]).Stdout.Trim();
File.WriteAllText(Path.Combine(consumerPackage, "lakefile.toml"), $$"""
    name = "consumer"
    [[require]]
    name = "leancil"
    git = {{JsonSerializer.Serialize(Root.Replace('\\', '/'))}}
    rev = "{{revision}}"
    [[lean_lib]]
    name = "Proofs"
    """);
File.Copy(At("lean-toolchain"), Path.Combine(consumerPackage, "lean-toolchain"));
var consumerProof = Path.Combine(consumerPackage, "Proofs", "Add.lean");
File.Copy(proof, consumerProof);
Run(["lake", "update"], consumerPackage);
var consumerOutput = Path.Combine(consumerRoot, "Extraction");
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", consumerOutput]);
var consumerEntry = JsonSerializer.Deserialize<JsonElement>(
    File.ReadAllText(Path.Combine(consumerOutput, "identity.json"))).GetProperty("entry").GetString();
// A fresh run publishes nothing; the first ordinary run may reuse an earlier test run's result, the second must.
foreach (var (options, cached) in new[]
    { (new[] { "--fresh" }, (bool?)false), (Array.Empty<string>(), null), (Array.Empty<string>(), true) })
{
    var consumer = Execute([.. cli, "verify", consumerOutput, "--proof", consumerProof,
        "--proof-root", consumerPackage, .. options]);
    var consumerText = consumer.Stdout.ReplaceLineEndings("\n");
    var libraryBuild = JsonSerializer.Deserialize<JsonElement>(
        File.ReadAllText(Path.Combine(consumerOutput, "verified.json"))).GetProperty("libraryBuild").GetString();
    if (consumer.Code != 0 || (cached is { } reused && (libraryBuild == "consumer-proof-cache") != reused) ||
        !consumerText.Contains("∃ result,") || consumerText.Contains("Exists fun") ||
        consumerText.Contains("Subject: not identified") ||
        !consumerText.Contains($"  Subject: {consumerEntry} (method 0) via CIL.Safety.invoke\n") ||
        !consumerText.Contains("  Lean messages (1):\n") ||
        !consumerText.Contains("Add.lean:15:0: info: 'ExampleProof.correctness' depends on axioms"))
        throw new InvalidOperationException(
            "Consumer verification did not print the readable statement, subject and messages: " + consumer.Output);
}
Console.WriteLine("PASS CLI prints the readable statement, subject and Lean messages for --proof-root proofs");

// Consumers pin the framework from this report, so it must name the commit the tool was built from.
var version = Execute([.. cli, "--version"]);
var head = Execute(["git", "-C", Root, "rev-parse", "HEAD"]).Stdout.Trim();
if (version.Code != 0 || !version.Stdout.Contains($"LeanCIL revision: {head}") ||
    !version.Stdout.Contains($"rev = \"{head}\"") ||
    !version.Stdout.Contains("Lean toolchain: " + File.ReadAllText(At("lean-toolchain")).Trim()))
    throw new InvalidOperationException("Version report does not name the built revision: " + version.Output);
Console.WriteLine("PASS CLI version names the framework revision and toolchain");

if (args.Length == 0)
    Run(["dotnet", "run", "--file", At("Tests/CliImportedKernelAudit.cs")],
        streamOutput: true, progress: "CLI imported helper kernel audit");
