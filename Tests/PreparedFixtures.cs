#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Runtime.InteropServices;
using System.Text.Json;

var directory = At("artifacts/PreparedFixtures-" + Guid.NewGuid().ToString("N"));
var sourceDirectory = Path.Combine(directory, "sources");
Directory.CreateDirectory(sourceDirectory);
var source = Path.Combine(sourceDirectory, "Example.cs");
var include = Path.Combine(sourceDirectory, "Included.cs");
File.WriteAllText(source, "#!/usr/bin/env dotnet\n#:property PublishAot=false\n \t#:include Included.cs\n" +
    "Console.WriteLine(Example.Message + string.Join(\",\", args));\n");
File.WriteAllText(include, "static class Example { public const string Message = \"prepared:\"; }\n");
File.WriteAllText(Path.Combine(directory, ".editorconfig"), "# fixture analyzer configuration\n");
var output = Path.Combine(directory, "bin");
Run(["dotnet", "build", source, "-c", "Release", "--output", output,
    "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
var relative = Path.GetRelativePath(Root, source).Replace('\\', '/');
var files = HashFiles(Directory.EnumerateFiles(output, "*", SearchOption.AllDirectories)
    .Select(path => (Path.GetRelativePath(directory, path).Replace('\\', '/'), path)));
var record = new PreparedFixture("bin/Example.dll", FixtureInputs(relative)!, files);
var prepared = new PreparedFixtures(Run(["dotnet", "--version"]).Trim(), RuntimeInformation.RuntimeIdentifier,
    new() { [relative] = record });
var manifest = Path.Combine(directory, "manifest.json");
var savedPath = Environment.GetEnvironmentVariable(FixtureManifestEnvironment);
var savedDigest = Environment.GetEnvironmentVariable(FixtureDigestEnvironment);
var savedRoot = Environment.GetEnvironmentVariable("LEANCIL_FIXTURE_ROOT");
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
    var corpus = Path.Combine(directory, "isolated");
    Directory.CreateDirectory(Path.Combine(corpus, "scripts"));
    File.Copy(At("scripts/Verification.cs"), Path.Combine(corpus, "scripts", "Verification.cs"));
    var probe = Path.Combine(corpus, "Probe.cs");
    File.WriteAllText(probe, "#!/usr/bin/env dotnet\n#:property PublishAot=false\n" +
        "#:include scripts/Verification.cs\nConsole.WriteLine(Root);\n");
    Environment.SetEnvironmentVariable("LEANCIL_FIXTURE_ROOT", Root);
    var probeOutput = Path.Combine(directory, "probe-bin");
    Run(["dotnet", "build", probe, "-c", "Release", "--output", probeOutput,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
    if (Run(["dotnet", Path.Combine(probeOutput, "Probe.dll")]).Trim() != Root)
        throw new Exception("Relocated prepared fixture lost the checkout root");
    var isolated = Run(["dotnet", "run", "--file", probe, "-c", "Release",
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
    if (!isolated.TrimEnd().EndsWith(Path.GetFullPath(corpus), StringComparison.Ordinal))
        throw new Exception("Source-built child inherited the prepared fixture's checkout root: " + isolated);
    File.AppendAllText(include, "// changed\n");
    if (PreparedFixtureCommand(relative, []) is not null) throw new Exception("Changed include reused output");
    File.WriteAllText(include, "static class Example { public const string Message = \"prepared:\"; }\n");
    foreach (var name in new[] { "Directory.Build.props", "Directory.Build.targets", "Directory.Packages.props",
                 "Directory.Packages.targets", ".editorconfig", "NuGet.Config", "global.json",
                 "Directory.Build.Props", "Nuget.Config" })
    {
        var configuration = Path.Combine(directory, name);
        var original = File.Exists(configuration) ? File.ReadAllText(configuration) : null;
        File.WriteAllText(configuration, "changed build configuration");
        if (PreparedFixtureCommand(relative, []) is not null)
            throw new Exception("New nested configuration reused output: " + name);
        if (original is null) File.Delete(configuration);
        else File.WriteAllText(configuration, original);
    }
    var originalSource = File.ReadAllText(source);
    var projectSource = originalSource.Replace("#:property PublishAot=false\n",
        "#:property PublishAot=false\n#:project Missing.csproj\n", StringComparison.Ordinal);
    File.WriteAllText(source, projectSource);
    if (FixtureInputs(relative) is not null || PreparedFixtureCommand(relative, []) is not null)
        throw new Exception("Project-reference fixture reused an incomplete source closure");
    File.WriteAllText(source, originalSource);
    File.AppendAllText(include, "\n#:project Missing.csproj\n");
    if (FixtureInputs(relative) is not null)
        throw new Exception("Included project reference was omitted from the source closure");
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
    Environment.SetEnvironmentVariable("LEANCIL_FIXTURE_ROOT", savedRoot);
}
