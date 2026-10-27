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

    var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (report.GetProperty("schema").GetInt32() != 4 ||
        !report.GetProperty("extractionAudit").GetString()!.Contains("ExtractionAudit.valid"))
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

if (args.Length == 0)
    Run(["dotnet", "run", "--file", At("Tests/CliImportedKernelAudit.cs")],
        streamOutput: true, progress: "CLI imported helper kernel audit");
