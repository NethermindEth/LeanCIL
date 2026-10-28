#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// Reusing a parent's build requires matching source and output bytes, not an environment flag.
var buildElapsed = System.Diagnostics.Stopwatch.StartNew();
Run(["dotnet", "build", "Extractor", "-c", "Release",
    "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
buildElapsed.Stop();
var prior = Environment.GetEnvironmentVariable(ExtractorBuildEnvironment);
var source = At("Extractor/BuildReuseProbe-" + Guid.NewGuid().ToString("N") + ".cs");
var output = Path.Combine(Path.GetDirectoryName(ExtractorPath)!, "BuildReuseProbe-" + Guid.NewGuid().ToString("N"));
var fixture = Path.Combine(Path.GetTempPath(), "leancil-build-reuse-" + Guid.NewGuid().ToString("N") + ".cs");
try
{
    File.WriteAllText(fixture, """
        #if DEBUG
        Console.WriteLine("Debug " + args[0]);
        #else
        Console.WriteLine("Release " + args[0]);
        #endif
        """);
    Run(["dotnet", "build", fixture, "-c", "Release",
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
    if (Run(FixtureCommand(fixture, ["prepared"], prepared: true)).Trim() != "Release prepared")
        throw new Exception("Prepared fixture did not use its Release build or forward arguments");
    if (Run(FixtureCommand(fixture, ["unprepared"], prepared: false)).Trim() != "Release unprepared")
        throw new Exception("Unprepared fixture did not build normally or forward arguments");
    if (Run(["dotnet", "run", "--file", fixture, "--", "nested"]).Trim() != "Release nested")
        throw new Exception("Nested fixture did not use Release or forward arguments");
    File.AppendAllText(fixture, "\nConsole.WriteLine(\"changed\");\n");
    if (!Run(["dotnet", "run", "--file", fixture, "--", "nested"]).TrimEnd().EndsWith("changed"))
        throw new Exception("Nested fixture did not rebuild changed source");
    if (!Run(["dotnet", "run", "--file", fixture, "-c", "Debug", "--", "explicit"]).Contains("Debug explicit"))
        throw new Exception("Explicit fixture configuration was overridden");
    Environment.SetEnvironmentVariable(ExtractorBuildEnvironment, "true");
    if (PreparedExtractorMatches()) throw new Exception("Boolean bypass accepted");
    var identity = ExtractorBuildIdentity();
    Environment.SetEnvironmentVariable(ExtractorBuildEnvironment, identity);
    if (!PreparedExtractorMatches()) throw new Exception("Prepared build rejected");
    using var verification = new Program();
    var reuseElapsed = System.Diagnostics.Stopwatch.StartNew();
    verification.EnsureExtractorBuilt();
    reuseElapsed.Stop();
    if (!verification.extractorBuilt) throw new Exception("Prepared build not reused");
    File.WriteAllText(source, "// Changed source\n");
    if (PreparedExtractorMatches()) throw new Exception("Changed source accepted");
    File.Delete(source);
    if (!PreparedExtractorMatches()) throw new Exception("Restored source rejected");
    File.WriteAllText(output, "changed output");
    if (PreparedExtractorMatches()) throw new Exception("Changed output accepted");
    File.Delete(output);
    if (!PreparedExtractorMatches()) throw new Exception("Restored output rejected");
    Console.WriteLine("PASS prepared extractor source and output identity");
    Console.WriteLine($"Extractor build {buildElapsed.ElapsedMilliseconds}ms; " +
        $"validated reuse {reuseElapsed.ElapsedMilliseconds}ms");
}
finally
{
    File.Delete(source);
    File.Delete(output);
    File.Delete(fixture);
    Environment.SetEnvironmentVariable(ExtractorBuildEnvironment, prior);
}
