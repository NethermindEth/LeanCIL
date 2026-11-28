#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs

using System.Text.Json;

using var verification = new Program();
var module = "Tests.PreparedFixture" + Guid.NewGuid().ToString("N");
var source = At(module.Replace('.', '/') + ".lean");
const string fixture = "import CIL\ntheorem fixture : (1 : Nat) = 1 := rfl\n#print axioms fixture\n";
File.WriteAllText(source, fixture);
// A fixture that imports another test module, which the prepared list does not name.
var dependent = "Tests.PreparedDependent" + Guid.NewGuid().ToString("N");
var dependentSource = At(dependent.Replace('.', '/') + ".lean");
File.WriteAllText(dependentSource,
    $"import CIL\nimport {module}\ntheorem dependent : (1 : Nat) = 1 := fixture\n#print axioms dependent\n");
try
{
    verification.PrepareLeanFixtures(dependent);
    // The import is compiled before its importer and bound to its source like a listed fixture.
    RequireLeanFixtures(dependent, module);
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
    File.WriteAllText(source, $"import {dependent}\n" + fixture);
    Reject("import cycle", () => verification.PrepareLeanFixtures(dependent));
}
finally
{
    File.Delete(source);
    File.Delete(dependentSource);
}
Console.WriteLine("PASS fresh fixture compilation, imported fixtures, source/output binding and " +
    "missing-module rejection");

void Reject(string name, Action action)
{
    try { action(); }
    catch (InvalidOperationException) { return; }
    throw new InvalidOperationException("Prepared fixture accepted " + name);
}
