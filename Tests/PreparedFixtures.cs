#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Runtime.InteropServices;
using System.Text.Json;

var directory = At("artifacts/PreparedFixtures-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(directory);
var source = Path.Combine(directory, "Example.cs");
var include = Path.Combine(directory, "Included.cs");
File.WriteAllText(source, "#!/usr/bin/env dotnet\n#:property PublishAot=false\n#:include Included.cs\n" +
    "Console.WriteLine(Example.Message + string.Join(\",\", args));\n");
File.WriteAllText(include, "static class Example { public const string Message = \"prepared:\"; }\n");
var output = Path.Combine(directory, "bin");
Run(["dotnet", "build", source, "-c", "Release", "--output", output,
    "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
var relative = Path.GetRelativePath(Root, source).Replace('\\', '/');
var files = HashFiles(Directory.EnumerateFiles(output, "*", SearchOption.AllDirectories)
    .Select(path => (Path.GetRelativePath(directory, path).Replace('\\', '/'), path)));
var record = new PreparedFixture("bin/Example.dll", FixtureInputs(relative), files);
var prepared = new PreparedFixtures(Run(["dotnet", "--version"]).Trim(), RuntimeInformation.RuntimeIdentifier,
    new() { [relative] = record });
var manifest = Path.Combine(directory, "manifest.json");
var savedPath = Environment.GetEnvironmentVariable(FixtureManifestEnvironment);
var savedDigest = Environment.GetEnvironmentVariable(FixtureDigestEnvironment);
void Set(PreparedFixtures value)
{
    File.WriteAllText(manifest, JsonSerializer.Serialize(value));
    Environment.SetEnvironmentVariable(FixtureManifestEnvironment, manifest);
    Environment.SetEnvironmentVariable(FixtureDigestEnvironment, Sha(manifest));
}
void Rejected(Action action)
{
    try { action(); }
    catch (InvalidOperationException) { return; }
    throw new Exception("Changed prepared fixture was accepted");
}
try
{
    Set(prepared);
    var command = PreparedFixtureCommand(relative, ["one", "two"])!;
    if (Run(command).Trim() != "prepared:one,two" ||
        Run(["dotnet", "run", "--file", source, "--", "nested"]).Trim() != "prepared:nested")
        throw new Exception("Prepared fixture arguments changed");
    File.AppendAllText(include, "// changed\n");
    if (PreparedFixtureCommand(relative, []) is not null) throw new Exception("Changed include reused output");
    File.WriteAllText(include, "static class Example { public const string Message = \"prepared:\"; }\n");
    Set(prepared with { Sdk = "incompatible" });
    if (PreparedFixtureCommand(relative, []) is not null) throw new Exception("Changed SDK reused output");
    Set(prepared with { Runtime = "incompatible" });
    if (PreparedFixtureCommand(relative, []) is not null) throw new Exception("Changed RID reused output");
    Set(prepared);
    File.AppendAllText(manifest, " ");
    Rejected(() => PreparedFixtureCommand(relative, []));
    Set(prepared);
    var unexpected = Path.Combine(output, "unexpected.dll");
    File.WriteAllText(unexpected, "extra");
    Rejected(() => PreparedFixtureCommand(relative, []));
    File.Delete(unexpected);
    File.AppendAllText(Path.Combine(output, "Example.dll"), "changed");
    Rejected(() => PreparedFixtureCommand(relative, []));
    Console.WriteLine("PASS prepared fixture execution, includes, SDK/RID binding, manifest and output tampering");
}
finally
{
    Environment.SetEnvironmentVariable(FixtureManifestEnvironment, savedPath);
    Environment.SetEnvironmentVariable(FixtureDigestEnvironment, savedDigest);
}
