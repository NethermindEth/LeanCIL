#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// Consumer packages reach ExtractedSymbols through their own modules. PDB names bind only the
// proofs that import them, never Extracted, and a renamed local changes no theorem statement.
var cli = new[] { "dotnet", ExtractorPath };
var root = At("artifacts/ConsumerSymbols");
var package = Path.Combine(root, "Package");
Directory.CreateDirectory(Path.Combine(package, "Client"));
// Fresh receipts, so first runs really check; a valid base library may be copied and is still authenticated.
var existingCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
    Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries");
var isolatedCache = Path.Combine(root, "Cache-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(isolatedCache);
if (Directory.Exists(existingCache))
    foreach (var candidate in Directory.EnumerateDirectories(existingCache))
        if (File.Exists(Path.Combine(candidate, "cache-manifest.json")) &&
            File.Exists(Path.Combine(candidate, "lakefile.toml")) && Sha(Path.Combine(candidate, "lakefile.toml")) == Sha(At("lakefile.toml")))
            CopyTree(candidate, Path.Combine(isolatedCache, Path.GetFileName(candidate)));
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", isolatedCache);
var trace = Path.Combine(root, "Trace-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(trace);
Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);

const string Sum = "System.UInt32 Names.Calls::Sum(System.UInt32,System.UInt32)";
string Build(string name, string first, string debugType)
{
    var source = Path.Combine(root, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Names.csproj"), $"""
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize><DebugType>{debugType}</DebugType></PropertyGroup></Project>
    """);
    File.WriteAllText(Path.Combine(source, "Names.cs"), string.Join("\n",
        "namespace Names;",
        "public static class Calls",
        "{",
        "    public static uint Mix(uint x, uint y) => x & y;",
        "    public static ulong Wide(uint x, uint y) => (ulong)x * y;",
        "    public static uint Sum(uint x, uint y)",
        "    {",
        "        uint total = 0;",
        $"        {{ uint {first} = Mix(x, y); total += {first}; total += {first} >> 1; }}",
        "        { ulong carry = Wide(x, y); total ^= (uint)carry; total ^= (uint)(carry >> 32); }",
        "        return total;",
        "    }",
        "}"));
    Run(["dotnet", "build", Path.Combine(source, "Names.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Names.dll");
}
var original = Build("Original", "carry", "portable");
var renamed = Build("Renamed", "low", "portable");
var stripped = Build("Stripped", "carry", "none");
// The renamed build's PDB does not match the original assembly.
var mismatchedDirectory = Path.Combine(root, "Mismatched");
Directory.CreateDirectory(mismatchedDirectory);
var mismatched = Path.Combine(mismatchedDirectory, "Names.dll");
File.Copy(original, mismatched, true);
File.Copy(Path.ChangeExtension(renamed, ".pdb"), Path.ChangeExtension(mismatched, ".pdb"), true);

var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    $"name = \"symbols\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"), true);
// Only the helper imports ExtractedSymbols; the proof names a local through it.
File.WriteAllText(Path.Combine(package, "Client", "Named.lean"), $$"""
    import Extracted
    import ExtractedSymbols -- PDB names through a consumer helper
    import CIL.StructuralLabels

    namespace Client
    bind_method sum sumBody := "{{Sum}}"
    bind_callee wide wideBody := "System.UInt64 Names.Calls::Wide(System.UInt32,System.UInt32)" from sumBody
    bind_call atWide := wide from sumBody
    end Client
    """);
var proof = Path.Combine(package, "Proof.lean");
File.WriteAllText(proof, """
    import Client.Named

    namespace ExampleProof
    -- The second block stores the wide product in its own `carry`.
    theorem correctness :
        Client.sumBody.code[Client.atWide + 1]? = some (.setLocal (local_named Client.sum "carry" at (Client.atWide + 1))) := rfl
    end ExampleProof
    """);
var plain = Path.Combine(package, "Plain.lean");
File.WriteAllText(plain, $$"""
    import Extracted
    import CIL.StructuralLabels

    namespace ExampleProof
    bind_method sum sumBody := "{{Sum}}"
    bind_callee wide wideBody := "System.UInt64 Names.Calls::Wide(System.UInt32,System.UInt32)" from sumBody
    bind_call atWide := wide from sumBody
    theorem correctness : sumBody.code[atWide + 1]? = some (.setLocal 1) := rfl
    end ExampleProof
    """);
Run(["lake", "update"], package);

string Extraction(string name, string assembly)
{
    var output = Path.Combine(root, name + "-Extraction");
    Run([.. cli, "extract", assembly, "Calls::Sum(uint,uint)", output]);
    return output;
}
var named = Extraction("Named", original);
var plainOutput = Extraction("Plain", original);
var renamedOutput = Extraction("Renamed", renamed);
var strippedOutput = Extraction("Stripped", stripped);
var mismatchedOutput = Extraction("Mismatched", mismatched);
string Generated(string output) => Sha(Path.Combine(output, "Extracted.lean"));
string Names(string output) => Path.Combine(output, "Symbols.lean");
var generated = Generated(named);
if (new[] { plainOutput, renamedOutput, strippedOutput, mismatchedOutput }.Any(output => Generated(output) != generated))
    throw new InvalidOperationException("Extracted.lean depends on the PDB or on local names.");
if (!File.Exists(Names(named)) || !File.Exists(Names(renamedOutput)) || File.Exists(Names(strippedOutput)) ||
    File.Exists(Names(mismatchedOutput)) || Sha(Names(named)) == Sha(Names(renamedOutput)))
    throw new InvalidOperationException("Symbols.lean must exist exactly for matching PDBs and follow local names.");
Console.WriteLine("PASS Extracted.lean is identical across PDBs and local names; Symbols.lean follows the matching PDB");

string[] previous = [];
void Mark() => previous = Directory.GetFiles(trace, "*.jsonl");
string[][] Replays() => Directory.EnumerateFiles(trace, "*.jsonl").Where(path => !previous.Contains(path)).SelectMany(File.ReadLines)
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
    .Where(item => item.GetProperty("stage").GetString() is "Kernel replay of consumer proof and dependencies"
        or "Joint kernel replay of consumer proof and dependencies")
    .Select(item => File.ReadLines(Path.Combine(trace, item.GetProperty("transcript").GetString()!))
        .Where(line => line.StartsWith('{')).Select(line => JsonSerializer.Deserialize<JsonElement>(line)
            .GetProperty("module").GetString()!).ToArray()).ToArray();
bool Replayed(string module) => Replays().Any(command => command.Contains(module));
JsonElement Verify(string output, string proofPath)
{
    Mark();
    var text = Run([.. cli, "verify", output, "--proof", proofPath, "--proof-root", package]);
    if (!text.Contains("Verified: ")) throw new InvalidOperationException(text);
    return JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
}
string Reject(string output, string proofPath, params string[] markers)
{
    Mark();
    var result = Execute([.. cli, "verify", output, "--proof", proofPath, "--proof-root", package]);
    if (result.Code != 1 || markers.Any(marker => !result.Output.Contains(marker)) || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Expected consumer proof rejection: " + result.Output);
    return result.Output;
}
static bool Cached(JsonElement report) => report.GetProperty("libraryBuild").GetString() == "consumer-proof-cache";
static string Statement(JsonElement report) =>
    report.GetProperty("theoremAudit").GetString()!.Split("'" + report.GetProperty("theorem").GetString() + "'", 2)[0].Trim();

var first = Verify(named, proof);
var statement = Statement(first);
if (Cached(first) || !Replayed("ExtractedSymbols") || !Replayed("Client.Named"))
    throw new InvalidOperationException("ExtractedSymbols and its importer were not checked and replayed.");
// The statement holds the chosen slot, not a reference to the PDB names.
if (!statement.Contains("setLocal 1") || statement.Contains("local_named") || statement.Contains("ExtractedSymbols"))
    throw new InvalidOperationException("Unexpected elaborated statement: " + statement);
if (!Cached(Verify(named, proof))) throw new InvalidOperationException("An unchanged proof importing ExtractedSymbols was not reused.");
if (Cached(Verify(plainOutput, plain)) || Replayed("ExtractedSymbols"))
    throw new InvalidOperationException("A symbol-free proof checked or replayed ExtractedSymbols.");
if (!Cached(Verify(plainOutput, plain))) throw new InvalidOperationException("An unchanged symbol-free proof was not reused.");
Console.WriteLine("PASS a consumer proof names a local through a helper importing ExtractedSymbols; both replay and reuse");

// A rebuilt PDB also changes the assembly's debug directory, so change only Symbols.lean: with
// the PDB aside, `leancil check` cannot compare it and the PDB names are the only changed input.
var pdb = Path.ChangeExtension(original, ".pdb");
try
{
    File.Move(pdb, pdb + ".aside");
    foreach (var output in new[] { named, plainOutput }) File.Copy(Names(renamedOutput), Names(output), true);
    var changed = Verify(named, proof);
    if (Cached(changed) || !Replayed("ExtractedSymbols") || Generated(named) != generated || Statement(changed) != statement)
        throw new InvalidOperationException("Changed PDB names reused a proof, changed Extracted or changed the statement.");
    if (!Cached(Verify(plainOutput, plain))) throw new InvalidOperationException("Changed PDB names invalidated a symbol-free proof.");
}
finally
{
    if (File.Exists(pdb + ".aside")) File.Move(pdb + ".aside", pdb, true);
    Extraction("Named", original);
    Extraction("Plain", original);
}
Console.WriteLine("PASS changed PDB names recheck proofs importing them, reuse symbol-free proofs and keep Extracted and the statement");

if (Statement(Verify(renamedOutput, proof)) != statement)
    throw new InvalidOperationException("Renaming an unrelated local changed the theorem statement.");
Console.WriteLine("PASS a build with a renamed local verifies the unedited proof with the same statement");

foreach (var (output, assembly) in new[] { (strippedOutput, stripped), (mismatchedOutput, mismatched) })
    Reject(output, proof, "no matching portable PDB", "Assembly: " + Path.GetFullPath(assembly), "Method: " + Sum);
Verify(strippedOutput, plain);
Console.WriteLine("PASS a missing or mismatched PDB names the assembly and method; symbol-free proofs need none");

var saved = File.ReadAllText(Names(named));
try
{
    File.AppendAllText(Names(named), "\n-- stale\n");
    Reject(named, proof, "Stale or mismatched", "Method: " + Sum);
}
finally { File.WriteAllText(Names(named), saved); }
var reserved = Path.Combine(package, "ExtractedSymbols.lean");
try
{
    File.WriteAllText(reserved, "-- not the extraction's names\n");
    Reject(named, proof, "reserved");
}
finally { File.Delete(reserved); }
Console.WriteLine("PASS stale Symbols.lean and a consumer module named ExtractedSymbols are rejected");

// Equal Extracted with different PDB names takes separate workspaces; only the request without a PDB fails.
var manifest = Path.Combine(root, "Batch.json");
var results = Path.Combine(root, "BatchResults.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    schema = 1, proofRoot = package, requests = new object[]
    {
        new { output = named, proof, theorem = "ExampleProof.correctness" },
        new { output = renamedOutput, proof, theorem = "ExampleProof.correctness" },
        new { output = plainOutput, proof = plain, theorem = "ExampleProof.correctness" },
        new { output = strippedOutput, proof, theorem = "ExampleProof.correctness" }
    }
}));
var previousCache = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
    Mark();
    var batch = Execute([.. cli, "verify-batch", manifest, "--results", results]);
    var statuses = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(results))!
        .Select(item => item.GetProperty("status").GetString()).ToArray();
    if (batch.Code != 1 || !statuses.SequenceEqual(["verified", "verified", "verified", "failed"]) ||
        !batch.Output.Contains("no matching portable PDB") || Replays().Count(command => command.Contains("ExtractedSymbols")) != 2)
        throw new InvalidOperationException("Unexpected batch outcomes: " + string.Join(", ", statuses) + "\n" + batch.Output);
    foreach (var output in new[] { named, renamedOutput })
        if (Statement(JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")))) != statement)
            throw new InvalidOperationException("A batch certificate changed the theorem statement.");
}
finally { Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", previousCache); }
Console.WriteLine("PASS batch verification checks each PDB's names in its own workspace and fails only the request without a PDB");
