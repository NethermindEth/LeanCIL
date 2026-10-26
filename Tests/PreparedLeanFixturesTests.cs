#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs

using System.Text.Json;

using var verification = new Program();
var module = "Tests.PreparedFixture" + Guid.NewGuid().ToString("N");
var source = At(module.Replace('.', '/') + ".lean");
const string fixture = "import CIL\ntheorem fixture : (1 : Nat) = 1 := rfl\n#print axioms fixture\n";
File.WriteAllText(source, fixture);
try
{
    verification.PrepareLeanFixtures(module);
    RequireLeanFixtures("CIL.Extraction.Translation", module);
    CheckLeanFixture(module);
    File.AppendAllText(source, "-- changed source\n");
    Reject("source changed", () => RequireLeanFixtures(module));
    File.WriteAllText(source, fixture);
    var path = Environment.GetEnvironmentVariable(PreparedLeanFixturesPath)!;
    var manifest = JsonSerializer.Deserialize<PreparedLeanManifest>(File.ReadAllText(path))!;
    File.AppendAllText(manifest.Modules[module].Compiled, "changed output");
    Reject("compiled output changed", () => RequireLeanFixtures(module));
    Reject("missing library module", () => RequireLeanFixtures("CIL.DoesNotExist"));
    File.AppendAllText(path, " ");
    Reject("manifest changed", () => RequireLeanFixtures(module));
}
finally
{
    File.Delete(source);
}
Console.WriteLine("PASS fresh fixture compilation, source/output binding and missing-module rejection");

void Reject(string name, Action action)
{
    try { action(); }
    catch (InvalidOperationException) { return; }
    throw new InvalidOperationException("Prepared fixture accepted " + name);
}
