#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

var cli = new[] { "dotnet", ExtractorPath };
var assembly = At("Examples/Assembly/bin/Examples.dll");
var output = At("artifacts/InitializedTypes");
string[] Command(string method, params string[] types) =>
    [.. cli, "extract", assembly, method, output,
        .. types.SelectMany(type => new[] { "--assume-initialized", type })];

void Reject(string[] command, string marker)
{
    var result = Execute(command);
    if (result.Code != 1 || !result.Output.Contains(marker))
        throw new InvalidOperationException("Expected rejection: " + result.Output);
}

const string type = "Examples.InitializedTypes";
const string add = "InitializedTypes::Add(ulong,ulong)";
Reject(Command(add), "static initialisation");
Reject(Command(add, "Examples.Arithmetic"), "type with a static constructor");
Reject(Command(add, type, type), "Duplicate initialization assumption");
Reject(Command("InitializedTypes::.cctor()", type), "static initialisation");
Reject(Command("InitializedTypes::ReadConstant()"), "static initialisation");
Run(Command("InitializedTypes::ReadConstant()", type));
Run([.. cli, "check", output]);
Reject(Command("InitializedTypes::CallHelper(ulong)", type), "static initialisation");
Run(Command("InitializedTypes::CallHelper(ulong)", type, "Examples.InitializedHelper"));
Run([.. cli, "check", output]);
Run(Command(add, type));
Reject(Command("InitializedValue::Read(Examples.InitializedValue&)"), "static initialisation");
Run(Command("InitializedValue::Read(Examples.InitializedValue&)", "Examples.InitializedValue"));
Run([.. cli, "check", output]);
Run(Command(add, type));
Run([.. cli, "check", output]);
Reject([.. cli, "check", output, "--assume-initialized", "Examples.InitializedHelper"], "assumptions differ");
var manifestPath = Path.Combine(output, "identity.json");
var original = File.ReadAllText(manifestPath);
File.WriteAllText(manifestPath, original.Replace("\"Examples.InitializedTypes\"", "\"Examples.InitializedHelper\""));
Reject([.. cli, "check", output], "static initialisation");
File.WriteAllText(manifestPath, original);
var manifest = JsonSerializer.Deserialize<JsonElement>(original);
if (manifest.GetProperty("initializedTypes")[0].GetString() != type ||
    !File.ReadAllText(Path.Combine(output, "Extracted.lean")).Contains("def Extracted.initializedTypes"))
    throw new InvalidOperationException("Initialization assumption missing from generated artifacts.");
var verified = Run([.. cli, "verify", output, "--proof", At("Examples/Proofs/Add.lean")]);
if (!verified.Contains("Caller assumption: " + type))
    throw new InvalidOperationException("Verification omitted initialization precondition.");
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (report.GetProperty("initializedTypes")[0].GetString() != type)
    throw new InvalidOperationException("Verification report omitted initialization precondition.");
Console.WriteLine("PASS initialization opt-in, helper boundaries, readonly static reads, artifact identity and proof reporting");
