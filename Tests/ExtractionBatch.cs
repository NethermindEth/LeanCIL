#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Text.Json;
using Mono.Cecil;

var root = At("artifacts/ExtractionBatch");
Directory.CreateDirectory(root);
var assembly = At("Examples/Assembly/bin/Examples.dll");
var modified = Path.Combine(root, "Modified.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var arithmetic = module.GetType("Examples.Arithmetic");
    arithmetic.Methods.Single(method => method.Name == "Add").Name = "OriginalAdd";
    arithmetic.Methods.Single(method => method.Name == "WrongAdd").Name = "Add";
    module.Write(modified);
}
var requests = new[]
{
    new Request(assembly, "Examples", "GenericMethods::Repeated(ulong)", Path.Combine(root, "Generic"), "scalar"),
    new Request(modified, "Examples", "Arithmetic::Add(ulong,ulong)", Path.Combine(root, "Modified"), "scalar"),
    new Request(assembly, "Examples", "GenericMethods::Repeated(ulong)", Path.Combine(root, "Arm"), "arm64-advsimd"),
    new Request(assembly, "Examples", "GenericMethods::Repeated(ulong)", Path.Combine(root, "Repeated"), "scalar"),
    new Request(assembly, "Examples", "Arithmetic::Add(ulong,ulong)", Path.Combine(root, "Original"), "x64-sse2"),
    new Request(assembly, "Examples", "Capabilities::Flags()", Path.Combine(root, "ScalarFlags"), "scalar"),
    new Request(assembly, "Examples", "Capabilities::Flags()", Path.Combine(root, "X64Flags"), "x64-v3"),
    new Request(assembly, "Examples", "Loops::Countdown(uint)", Path.Combine(root, "Loop"), "scalar")
};
var originals = new List<SortedDictionary<string, string>>();
foreach (var request in requests)
{
    Run(Extract("extract", request.Assembly, request.Identity, request.Entry, request.Output, request.Profile));
    originals.Add(CacheFiles(request.Output));
}
Batch("extract", requests);
for (var index = 0; index < requests.Length; index++)
    Require(Same(originals[index], CacheFiles(requests[index].Output)), "Batched extraction differs from direct output");
Batch("check", requests);
Require(File.Exists(Path.Combine(requests[0].Output, "Symbols.lean")), "Expected matching PDB symbols");
Require(!File.Exists(Path.Combine(requests[1].Output, "Symbols.lean")), "Symbols leaked into another DLL");
Console.WriteLine("PASS mixed DLLs, profiles, repeated generic specialization and symbol identities match direct extraction");

var generated = Path.Combine(requests[0].Output, "Extracted.lean");
var source = File.ReadAllText(generated);
File.AppendAllText(generated, "\n-- tampered\n");
Reject("check", requests, "differs from regenerated CIL");
File.WriteAllText(generated, source);
var originalAssembly = File.ReadAllBytes(modified);
File.Copy(assembly, modified, overwrite: true);
Reject("check", requests, "assembly has changed since extraction");
File.WriteAllBytes(modified, originalAssembly);
Batch("check", requests);
Console.WriteLine("PASS final check reloads DLLs and rejects changed source and assembly bytes");

var duplicates = requests.Select(request => request with { Output = Path.Combine(root, "Duplicate") }).ToArray();
Reject("extract", duplicates, "outputs must be distinct");
Reject("extract", [duplicates[0], duplicates[1] with { Output = duplicates[0].Output + Path.DirectorySeparatorChar }],
    "outputs must be distinct");
Require(!File.Exists(Path.Combine(duplicates[0].Output, "identity.json")), "Duplicate output wrote an artifact");
using (var verification = new Program())
{
    var rejected = false;
    try
    {
        verification.VerifyGeneratedBatch(assembly, "Examples",
            [new(requests[0].Entry, "unused.lean", duplicates[0].Output),
                new(requests[1].Entry, "unused.lean", duplicates[0].Output + Path.DirectorySeparatorChar)]);
    }
    catch (ArgumentException error) when (error.Message == "Batch outputs must be distinct")
    {
        rejected = true;
    }
    Require(rejected, "Generated verification accepted aliased output directories");
}
var invalid = requests[0] with { Entry = "Missing::Method()", Output = Path.Combine(root, "Invalid") };
var never = requests[0] with { Output = Path.Combine(root, "Never") };
Reject("extract", [requests[0], invalid, never], "Missing::Method()");
Require(!File.Exists(Path.Combine(never.Output, "identity.json")), "Batch continued after failed request");
var commands = Execute(["dotnet", ExtractorPath, "generated-extraction-batch", "verify", "missing.json"]);
Require(commands.Code != 0 && commands.Output.Contains("extract|check", StringComparison.Ordinal),
    "Batch accepted an unrelated command");
Console.WriteLine("PASS duplicate outputs, unsupported command and failing middle request reject the batch");

// An output deliberately overlaps its input: the final freshness check must reject cached bytes.
var collision = Path.Combine(root, "Collision");
Directory.CreateDirectory(collision);
var collidingAssembly = Path.Combine(collision, "identity.json");
File.Copy(assembly, collidingAssembly, overwrite: true);
Reject("extract", [requests[0] with { Assembly = collidingAssembly, Output = collision }],
    "Extraction batch input changed");
var profileDirectory = Path.Combine(root, "ProfileCollision");
Directory.CreateDirectory(profileDirectory);
var profilePath = Path.Combine(profileDirectory, "Extracted.lean");
var identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(requests[0].Output, "identity.json")));
File.WriteAllText(profilePath, JsonSerializer.Serialize(identity.GetProperty("profile").EnumerateObject()
    .ToDictionary(property => JsonNamingPolicy.CamelCase.ConvertName(property.Name), property => property.Value)));
Reject("extract", [requests[0] with { Profile = "@" + profilePath, Output = profileDirectory }],
    "Extraction batch input changed");
Console.WriteLine("PASS changed cached assembly and profile inputs reject batch completion");

void Batch(string mode, Request[] batch)
{
    var result = Invoke(mode, batch);
    Require(result.Code == 0, result.Output);
}

void Reject(string mode, Request[] batch, string expected)
{
    var result = Invoke(mode, batch);
    Require(result.Code != 0 && result.Output.Contains(expected, StringComparison.Ordinal),
        "Expected rejection containing " + expected + "\n" + result.Output);
}

(int Code, string Output, string Stdout, string Stderr) Invoke(string mode, Request[] batch)
{
    var path = Path.Combine(root, "requests.json");
    File.WriteAllText(path, JsonSerializer.Serialize(batch));
    return Execute(["dotnet", ExtractorPath, "generated-extraction-batch", mode, path]);
}

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

sealed record Request(string Assembly, string Identity, string Entry, string Output, string Profile);
