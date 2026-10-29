#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Text.Json;

var assembly = At("Examples/Assembly/bin/Examples.dll");
const string identity = "Examples";
const string canonical = "System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)";
var output = At("artifacts/Selectors");
var checks = 0;

void Accepted(string selector, string expected, string? input = null)
{
    Run(Extract("extract", input ?? assembly, identity, selector, output));
    var manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));

    if (manifest.GetProperty("entry").GetString() != expected)
        throw new InvalidOperationException("Selector resolved to the wrong method: " + selector);

    // Canonical and shorthand selectors must describe byte-identical artifacts.
    Run(Extract("check", input ?? assembly, identity, expected, output));
    checks++;
}

void Rejected(string selector, string marker, string[]? candidates = null, string? input = null)
{
    var result = Execute(Extract("extract", input ?? assembly, identity, selector, output));

    if (result.Code == 0 || !result.Output.Contains(marker) ||
        (candidates is not null && candidates.Any(candidate => !result.Output.Contains(candidate))))
        throw new InvalidOperationException($"Unexpected selector diagnostic for '{selector}':\n{result.Output}");

    checks++;
}

// Aliases, optional return types, qualification and whitespace preserve exact identity.
foreach (var selector in new[]
{
    canonical,
    "ulong Examples.Arithmetic::Add(ulong,ulong)",
    "Examples.Arithmetic::Add(ulong,ulong)",
    "Arithmetic::Add(ulong,ulong)",
    "  ulong Arithmetic :: Add( ulong , System.UInt64 )  "
})
{
    Accepted(selector, canonical);
}

Accepted("Arithmetic::Alias(ulong&,ulong&)", "System.UInt64 Examples.Arithmetic::Alias(System.UInt64&,System.UInt64&)");
Accepted("ulong& Arithmetic::Escape()", "System.UInt64& Examples.Arithmetic::Escape()");

// Namespace and parameter types disambiguate independently; never choose the first match.
const string first = "System.UInt64 SelectorExamples.One.Collision::Add(System.UInt64,System.UInt64)";
const string second = "System.UInt64 SelectorExamples.Two.Collision::Add(System.UInt64,System.UInt64)";
Rejected("Collision::Add(ulong,ulong)", "Ambiguous method selector", [first, second]);
Accepted("SelectorExamples.One.Collision::Add(ulong,ulong)", first);
Accepted("SelectorExamples.Two.Collision::Add(ulong,ulong)", second);
Accepted("Collision::Add(uint,uint)", "System.UInt32 SelectorExamples.One.Collision::Add(System.UInt32,System.UInt32)");

foreach (var selector in new[]
{
    "uint Arithmetic::Add(ulong,ulong)",
    "Arithmetic::Add(uint,uint)",
    "Arithmetic::Add(ulong)",
    "ithmetic::Add(ulong,ulong)",
    "Arithmetic::Missing()"
})
{
    Rejected(selector, "No method matches selector");
}

foreach (var selector in new[]
{
    "Arithmetic::Add", "Arithmetic::Add(ulong,)", "Arithmetic::Add(List<ulong,ulong)",
    "ManagedDispatch::Dispatch(method int *(int][],int,int)",
    "ManagedDispatch::Dispatch(method int *(int[],int,int)",
    "ManagedDispatch::Dispatch(method int *int)[],int,int)"
})
{
    Rejected(selector, "Malformed method selector");
}

// Balanced callable syntax still requires an exact metadata signature.
Rejected("ManagedDispatch::Dispatch(method int *(long)[],int,int)", "No method matches selector");

// Selection does not bypass validation of unsupported runtime types.
Rejected("string SelectorExamples.One.Collision::Unsupported(string)", "Unsupported type");

// CLR metadata can contain overloads distinguished only by return type.
var returnOverload = At("artifacts/Selectors/return-overload.dll");
Run(["dotnet", "run", "--file", "Tests/MetadataMutator.cs", "--", assembly, returnOverload, "return-overload"]);
Rejected("Arithmetic::Add(ulong,ulong)", "Ambiguous method selector",
    [canonical, "System.UInt32 Examples.Arithmetic::Add(System.UInt64,System.UInt64)"], returnOverload);
Accepted("ulong Arithmetic::Add(ulong,ulong)", canonical, returnOverload);
Accepted("uint Arithmetic::Add(ulong,ulong)", "System.UInt32 Examples.Arithmetic::Add(System.UInt64,System.UInt64)", returnOverload);

Console.WriteLine($"All {checks} method selector checks passed.");

// Inference uses metadata, including when the DLL filename differs from its identity.
var renamed = At("artifacts/Selectors/renamed.dll");
File.Copy(assembly, renamed, true);
Run(Extract("extract", renamed, null, canonical, output));
var inferredManifest = File.ReadAllText(Path.Combine(output, "identity.json"));
var fullIdentity = JsonSerializer.Deserialize<JsonElement>(inferredManifest).GetProperty("assemblyIdentity").GetString();
Run(Extract("check", renamed, null, canonical, output));
Run(Extract("check", renamed, identity, canonical, output));
Run(Extract("check", renamed, fullIdentity, canonical, output));
Run(Extract("extract", renamed, fullIdentity, canonical, output));

if (File.ReadAllText(Path.Combine(output, "identity.json")) != inferredManifest)
    throw new InvalidOperationException("Assembly inference changed artifact identity.");

void InvalidArguments(string[] command, string marker)
{
    var result = Execute(command);

    if (result.Code != 1 || result.Stdout.Length != 0 || !result.Stderr.StartsWith("Invalid:") || !result.Stderr.Contains(marker))
        throw new InvalidOperationException($"Expected '{marker}':\n{result.Output}");
}

var inferred = Extract("check", renamed, null, canonical, output);
InvalidArguments([.. inferred, "--assembly", "Wrong.Name"], "assembly identity");
InvalidArguments([.. inferred, "--assembly", "Examples, Version=9.0.0.0, Culture=neutral, PublicKeyToken=null"], "assembly identity");
InvalidArguments([.. inferred, "--assembly"], "--assembly requires");
InvalidArguments([.. inferred, "--assembly", ""], "--assembly requires");
InvalidArguments([.. inferred, "--assembly", identity, "--assembly", identity], "Duplicate --assembly");
InvalidArguments([.. inferred, "--unknown"], "Unknown option");
Run([inferred[0], inferred[1], "check", "--assembly", identity, .. inferred[3..]]);

// Omitting the expectation never disables stale-artifact checks.
var recordedCheck = new[] { inferred[0], inferred[1], "check", output };
var valid = Execute(recordedCheck);

if (valid.Code != 0 || valid.Stderr.Length != 0 || !valid.Stdout.StartsWith("Valid:") ||
    !valid.Stdout.Contains(canonical) || !valid.Stdout.Contains(fullIdentity!) ||
    !valid.Stdout.Contains("Profile: scalar") || !valid.Stdout.Contains("Reachable methods: 1") ||
    !valid.Stdout.Contains("CIL: artifacts/Selectors/Extracted.lean") ||
    !valid.Stdout.Contains("Manifest: artifacts/Selectors/identity.json"))
    throw new InvalidOperationException("Expected a detailed validity summary on stdout only.");

var outside = Execute(recordedCheck, cwd: At("Examples"));
if (outside.Code != 0 || !outside.Stdout.Contains("CIL: " + Path.GetFullPath(Path.Combine(output, "Extracted.lean"))))
    throw new InvalidOperationException("Expected an absolute path for artifacts outside the current directory.");

Run([.. recordedCheck, "--assembly-path", assembly]);
InvalidArguments([.. recordedCheck, "--assembly", "Wrong.Name"], "assembly identity");
InvalidArguments([.. recordedCheck, "--assembly-path"], "--assembly-path requires");
InvalidArguments([.. recordedCheck, "--assembly-path", returnOverload], "Stale or mismatched");
File.AppendAllText(Path.Combine(output, "Extracted.lean"), "\n-- changed\n");
InvalidArguments(inferred, "Stale or mismatched");
InvalidArguments(recordedCheck, "Stale or mismatched");

// Recover the recorded non-default capabilities and validate them again.
Run(Extract("extract", renamed, null, canonical, output, "x64-v3"));
Run(recordedCheck);
var profileManifest = File.ReadAllText(Path.Combine(output, "identity.json"));
File.WriteAllText(Path.Combine(output, "identity.json"), profileManifest.Replace("\"NativeWidth\": 64", "\"NativeWidth\": 32"));
InvalidArguments(recordedCheck, "Invalid execution profile");
File.WriteAllText(Path.Combine(output, "identity.json"), profileManifest);
File.Delete(renamed);
InvalidArguments(recordedCheck, "Could not find file");
Run([.. recordedCheck, "--assembly-path", assembly]);
Console.WriteLine("Assembly inference, explicit constraints, option diagnostics and stale-artifact checks passed.");

// Discovery returns copyable canonical selectors, including unsupported candidates.
var listing = Execute([inferred[0], inferred[1], "list", assembly]);
if (listing.Code != 0 || listing.Stderr.Length != 0 || !listing.Stdout.Contains(canonical) ||
    !listing.Stdout.Contains("System.Int32 Examples.Arithmetic::Unsupported(System.Int32)") ||
    !listing.Stdout.Contains("Discovery only:"))
    throw new InvalidOperationException("Incomplete or misleading method discovery: " + listing.Output);

var unsupported = Execute(Extract("extract", assembly, null, "Arithmetic::Unsupported(int)", output));
if (unsupported.Code != 1 || !unsupported.Stderr.Contains("Stage: metadata and CIL validation") ||
    !unsupported.Stderr.Contains("Next:") || !unsupported.Stderr.Contains("Unsupported instruction"))
    throw new InvalidOperationException("Missing actionable unsupported-CIL diagnostic: " + unsupported.Output);

// A call-site rejection must name the callee, caller and IL offset, and must not blame the selector.
string CallOffset(string input, string caller, string callee)
{
    using var module = Mono.Cecil.ModuleDefinition.ReadModule(input);
    var method = module.GetType("Examples.Arithmetic").Methods.Single(m => m.FullName == caller);
    var call = method.Body.Instructions.First(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Call &&
        ((Mono.Cecil.MethodReference)i.Operand).FullName == callee);
    return $"IL_{call.Offset:x4}";
}

void RejectedCall(string input, string selector, string caller, string callee, string[] markers)
{
    string[] generatedArtifacts = ["Extracted.lean", "identity.json", "verified.json"];
    foreach (string artifact in generatedArtifacts) File.Delete(Path.Combine(output, artifact));
    var result = Execute(Extract("extract", input, identity, selector, output));
    var site = $"{callee}\n  Caller: {caller} at {CallOffset(input, caller, callee)}";
    if (result.Code != 1 || !result.Stderr.Contains("Stage: metadata and CIL validation") ||
        !result.Stderr.Contains(site) || markers.Any(marker => !result.Stderr.Contains(marker)) ||
        result.Stderr.Contains("leancil list") || !result.Stderr.Contains("Next: Reachable calls must") ||
        generatedArtifacts.Any(artifact => File.Exists(Path.Combine(output, artifact))))
        throw new InvalidOperationException("Missing call-site diagnostic: " + result.Output);
    checks++;
}

var unfoldedTypeTest = At("artifacts/Selectors/unfolded-type-test.dll");
using (var module = Mono.Cecil.ModuleDefinition.ReadModule(assembly))
{
    var body = module.GetType("Examples.Arithmetic").Methods.Single(method => method.Name == "TypeCheck").Body;
    body.GetILProcessor().InsertBefore(body.Instructions[2],
        Mono.Cecil.Cil.Instruction.Create(Mono.Cecil.Cil.OpCodes.Nop));
    module.Write(unfoldedTypeTest);
}
RejectedCall(unfoldedTypeTest, "Arithmetic::TypeCheck(ulong)", "System.UInt64 Examples.Arithmetic::TypeCheck(System.UInt64)",
    "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)",
    ["Rejected external call: ", "External managed dependency: ", "Callee scope: System.Runtime"]);
var instanceCall = At("artifacts/Selectors/instance-call.dll");
Run(["dotnet", "run", "--file", "Tests/MetadataMutator.cs", "--", assembly, instanceCall, "instance-call"]);
RejectedCall(instanceCall, "Arithmetic::Add(ulong,ulong)", canonical,
    "System.UInt64 Examples.Arithmetic::Increment(System.UInt64)", ["Unresolved call: ", "Callee scope: Examples"]);

Run(Extract("extract", assembly, null, canonical, output));
var missingProof = Execute([inferred[0], inferred[1], "verify", output, "--proof", At("artifacts/missing-proof.lean")]);
if (missingProof.Code != 1 || missingProof.Stdout.Length != 0 || !missingProof.Stderr.Contains("Stage: proof selection") ||
    !missingProof.Stderr.Contains("Next: Supply --proof"))
    throw new InvalidOperationException("Missing actionable proof-selection diagnostic: " + missingProof.Output);

Console.WriteLine("Method discovery and actionable diagnostics passed.");

// Invalid settings must not silently fall back to a different proof selection.
var settingsPath = Path.Combine(output, "verification.json");
foreach (var settings in new[]
{
    "{\"schema\":2,\"proof\":\"Proof.lean\",\"theorem\":\"ExampleProof.correctness\"}",
    "{\"schema\":1,\"proof\":\"Proof.lean\",\"theorem\":\"ExampleProof.correctness\",\"unknown\":true}"
})
{
    File.WriteAllText(settingsPath, settings);
    var result = Execute([inferred[0], inferred[1], "verify", output]);
    if (result.Code != 1 || result.Stdout.Length != 0 || !result.Stderr.Contains("Stage: proof selection"))
        throw new InvalidOperationException("Invalid verification settings were accepted: " + result.Output);
}
File.Delete(settingsPath);
Console.WriteLine("Malformed verification settings rejected.");
