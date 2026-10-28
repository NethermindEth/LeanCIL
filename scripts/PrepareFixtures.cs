#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs

using System.Runtime.InteropServices;
using System.Text.Json;

if (args.Length != 1) throw new ArgumentException("Usage: PrepareFixtures.cs <output-directory>");
var output = Path.GetFullPath(args[0]);
Directory.CreateDirectory(output);
var fixtures = new Dictionary<string, PreparedFixture>(StringComparer.Ordinal);
foreach (var script in new[] { "scripts/Test.cs", "Tests/ContractExport.cs", "Tests/FullImportVerification.cs",
    "Tests/ModularStaticExports.cs", "scripts/LibraryArchive.cs", "scripts/RunVerificationGroup.cs" })
{
    var inputs = FixtureInputs(script);
    var name = Path.GetFileNameWithoutExtension(script);
    var directory = Path.Combine(output, name);
    if (Directory.Exists(directory))
        throw new InvalidOperationException("Fixture output must be fresh: " + directory);
    var log = Run(["dotnet", "build", script, "-c", "Release", "--output", directory,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"],
        progress: "Building shared fixture " + script);
    var current = FixtureInputs(script);
    if (log.Contains("IDE0005", StringComparison.Ordinal) ||
        inputs is not null && (current is null || !Same(inputs, current)))
        throw new InvalidOperationException("Fixture inputs changed or have unused imports: " + script);
    var files = HashFiles(Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
        .Select(path => (Path.GetRelativePath(output, path).Replace('\\', '/'), path)));
    var assembly = name + "/" + name + ".dll";
    if (!files.ContainsKey(assembly)) throw new InvalidOperationException("Missing fixture assembly: " + assembly);
    // Unsupported project graphs still build, but consumers run them from source.
    if (inputs is not null) fixtures.Add(script, new(assembly, inputs, files));
}
var manifest = Path.Combine(output, "manifest.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new PreparedFixtures(
    Run(["dotnet", "--version"]).Trim(), RuntimeInformation.RuntimeIdentifier, fixtures), Json));
// Check the executable bytes before starting the shared runner, including its manifest.
var checksums = Path.Combine(output, "checksums.sha256");
var lines = Directory.EnumerateFiles(output, "*", SearchOption.AllDirectories)
    .Select(path => Sha(path) + "  " + Path.GetRelativePath(Root, path).Replace('\\', '/')).Order().ToArray();
File.WriteAllLines(checksums, lines);
Console.WriteLine("Fixture manifest SHA256: " + Sha(manifest));
if (Environment.GetEnvironmentVariable("GITHUB_OUTPUT") is { Length: > 0 } githubOutput)
    File.AppendAllText(githubOutput, "manifest-sha256=" + Sha(manifest) + "\nchecksums-sha256=" + Sha(checksums) + "\n");
