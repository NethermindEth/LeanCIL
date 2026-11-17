#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include MultiAssemblyFixture.cs
#:include DeepBinding.cs

using System.Text.Json;

using Program preparation = new();
preparation.EnsureExtractorBuilt();
MultiAssemblyFixture fixture = new("DeepCli");
var cli = args is [var executable] && !executable.StartsWith("--", StringComparison.Ordinal)
    ? new[] { Path.GetFullPath(executable) } : fixture.Cli;
const string libName = "DeepCli.Library";
var lib = fixture.Build("Library", libName,
    "namespace MultiFixture; public static class Mix { public static ulong Step(ulong x) => x * 3 + 1; }");
var app = fixture.Build("Application", "DeepCli.Application",
    "namespace MultiFixture; public static class Application { " +
        "public static ulong Direct(ulong x) => Mix.Step(x) + 1; }",
    references: $"<Reference Include=\"{libName}\"><HintPath>{lib}</HintPath></Reference>");
var output = fixture.Artifact("Direct");
Run([.. cli, "extract", app, "MultiFixture.Application::Direct(System.UInt64)", output, "--reference", lib]);
var proof = At("Tests/MultiAssembly/Direct.lean");
string[] verify = [.. cli, "verify", output, "--proof", proof, "--theorem", "MultiAssemblyProof.correctness"];
var digestFile = Path.Combine(fixture.Root, "inputs.sha256");
var digests = Sha(app) + "  " + Path.GetRelativePath(fixture.Root, app) + "\n" +
    Sha(lib) + "  " + Path.GetRelativePath(fixture.Root, lib) + "\n";
File.WriteAllText(digestFile, digests);

void Refused(string name, string[] command, string? expectedStage = null)
{
    var result = Execute(command);
    if (result.Code == 0) throw new InvalidOperationException(name + " was accepted");
    if (expectedStage is not null)
    {
        var report = JsonSerializer.Deserialize<JsonElement>(result.Stdout);
        if (report.GetProperty("stage").GetString() != expectedStage ||
            report.GetProperty("binding").ValueKind != JsonValueKind.Null)
            throw new InvalidOperationException(name + " has the wrong failure boundary: " + result.Output);
    }
    Console.WriteLine("PASS " + name);
}

// The deep checks run only as an option of verify, so a command name that is not one of the listed commands
// is a usage error that runs nothing, whatever it is called.
void RefusedAsUnknownCommand(string[] cli, string output, string digestFile)
{
    foreach (var name in new[] { "audit" + "-binding", "audit", "binding-audit", "strict-binding", "deep-checks",
                 "deep", "verify-deep", "audit-deep" })
    {
        var result = Execute([.. cli, name, output, "--deep-checks", digestFile]);
        if (result.Code == 0 || !result.Output.Contains("Stage: arguments", StringComparison.Ordinal) ||
            !result.Output.Contains("Usage: leancil", StringComparison.Ordinal) ||
            result.Output.Contains("Binding:", StringComparison.Ordinal) ||
            result.Output.Contains("BindingAudit", StringComparison.Ordinal) ||
            result.Output.Contains("StrictBinding", StringComparison.Ordinal))
            throw new InvalidOperationException(name + " was not refused as an unknown command: " + result.Output);
    }
    Console.WriteLine("PASS unknown audit command names");
}

// The help text lists the deep checks only as an option of verify. The one audit command, audit-library, checks
// the theorems of a Lean library and runs no binding check.
void RequireNoSeparateAudit(string[] cli)
{
    var help = Execute([.. cli, "--help"]);
    var commands = help.Stdout.ReplaceLineEndings("\n").Split('\n')
        .Select(line => line.Trim().StartsWith("Usage: ", StringComparison.Ordinal) ? line.Trim()["Usage: ".Length..]
            : line.Trim())
        .Where(line => line.StartsWith("leancil ", StringComparison.Ordinal)).ToArray();
    var names = commands.Select(line => line.Split(' ')[1])
        .Where(name => !name.StartsWith("--", StringComparison.Ordinal)).ToArray();
    var audits = names.Where(name => name.Contains("audit", StringComparison.OrdinalIgnoreCase)).ToArray();
    var deepLines = commands.Where(line => line.Contains("--deep-checks", StringComparison.Ordinal)).ToArray();
    if (help.Code != 0 || !names.Contains("verify") || !audits.SequenceEqual(["audit-library"]) ||
        deepLines.Length != 1 || !deepLines[0].StartsWith("leancil verify ", StringComparison.Ordinal) ||
        help.Stdout.Contains("binding audit", StringComparison.OrdinalIgnoreCase))
        throw new InvalidOperationException("The help text names a separate audit entry: " + help.Output);
    Console.WriteLine("PASS help names no separate audit command");
}

if (args is not (["--consumer"] or ["--mutations"] or ["--controls"] or ["--final-mutations"]))
{
    Refused("missing digest option value", [.. verify, "--format", "json", "--deep-checks"], "arguments");
    Refused("duplicate digest option", [.. verify, "--format", "json", "--deep-checks", digestFile,
        "--deep-checks", digestFile], "arguments");
    Refused("missing digest file", [.. verify, "--deep-checks", digestFile + ".missing", "--format", "json"],
        "arguments");
    foreach (var content in new[] { "malformed\n", new string('0', 64) + "  " + app + "\n",
        Sha(app) + "  " + app + "\n" })
    {
        File.WriteAllText(digestFile, content);
        Refused("invalid or missing image digest", [.. verify, "--deep-checks", digestFile, "--format", "json"],
            "arguments");
    }
    File.WriteAllBytes(digestFile, [0xff]);
    Refused("invalid UTF-8 digest file", [.. verify, "--deep-checks", digestFile, "--format", "json"], "arguments");
    File.WriteAllText(digestFile, digests);
    foreach (var command in new[] { "verify-batch", "gates", "watch", "workspace", "check", "audit-library" })
        Refused(command + " rejects deep option", [.. cli, command, output, "--deep-checks", digestFile]);
    RefusedAsUnknownCommand(cli, output, digestFile);
    RequireNoSeparateAudit(cli);
    Refused("invalid proof root", [.. verify, "--proof-root", fixture.Root + ".missing", "--deep-checks",
        digestFile, "--format", "json"], "extraction integrity");
    File.Delete(Path.Combine(output, "verification.json"));
    if (args is ["--arguments"]) return;

    var ordinary = Execute(verify);
    if (ordinary.Code != 0 || !ordinary.Stdout.Contains("Binding: default", StringComparison.Ordinal) ||
        ordinary.Stdout.Split(": trusted", StringSplitOptions.None).Length != 13 ||
        ordinary.Output.Contains("BindingAudit", StringComparison.Ordinal))
        throw new InvalidOperationException("Default binding output or work changed: " + ordinary.Output);
    var deep = Execute([.. verify, "--deep-checks", digestFile]);
    string[] reconfirmed = ["body-bytes", "metadata-rows"];
    if (deep.Code != 0 || !deep.Stdout.Contains("StrictBinding sources:", StringComparison.Ordinal) ||
        deep.Stdout.Split(": not covered", StringSplitOptions.None).Length != 11)
        throw new InvalidOperationException("Deep binding text is incomplete: " + deep.Output);
    string[] factNames =
    [
        "body-bytes", "metadata-rows", "platform-type-kinds", "enum-underlying-types", "value-tuple-field-order",
        "object-fields", "layout-content", "dispatch-catalogs", "static-data", "generic-constraints",
        "public-key-tokens", "import-identities"
    ];
    foreach (var fact in factNames)
        if (!ordinary.Stdout.Contains(fact + ": trusted", StringComparison.Ordinal) ||
            !deep.Stdout.Contains(fact + (reconfirmed.Contains(fact) ? ": reconfirmed" : ": not covered"),
                StringComparison.Ordinal))
            throw new InvalidOperationException("Binding text omitted wire name " + fact);
    Console.WriteLine("PASS default and deep binding text");
}
if (args is ["--text"]) return;
if (args is ["--mutations"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify);
if (args is ["--controls"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify, controlsOnly: true);
if (args is ["--final-mutations"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify, finalOnly: true);
if (args is not (["--mutations"] or ["--controls"] or ["--final-mutations"]))
{
    var package = Path.Combine(fixture.Root, "Consumer");
    Directory.CreateDirectory(package);
    var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
    File.WriteAllText(Path.Combine(package, "lakefile.toml"), $"""
        name = "deep_cli_consumer"
        [[require]]
        name = "leancil"
        git = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}
        rev = "{revision}"
        """);
    File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
    var consumerProof = Path.Combine(package, "Proof.lean");
    File.Copy(proof, consumerProof);
    Run(["lake", "update"], package);
    string[] consumer = [.. cli, "verify", output, "--proof", consumerProof, "--theorem",
        "MultiAssemblyProof.correctness", "--proof-root", package, "--deep-checks", digestFile, "--format", "json"];
    var checkedConsumer = Execute(consumer);
    if (checkedConsumer.Code != 0) throw new InvalidOperationException(checkedConsumer.Output);
    var consumerReport = JsonSerializer.Deserialize<JsonElement>(checkedConsumer.Stdout);
    var binding = consumerReport.GetProperty("binding");
    if (binding.GetProperty("mode").GetString() != "deep" ||
        binding.GetProperty("facts").GetArrayLength() != 12 ||
        binding.GetProperty("facts")[0].GetProperty("status").GetString() != "reconfirmed")
        throw new InvalidOperationException("Consumer CLI did not retain deep binding");
    Console.WriteLine("PASS proof-root CLI deep verification");
    File.WriteAllText(consumerProof,
        "import Extracted\nnamespace MultiAssemblyProof\ntheorem correctness : False := by exact True.intro\n" +
        "end MultiAssemblyProof\n");
    var rejected = Execute(consumer);
    if (rejected.Code == 0 || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Rejected consumer proof published a certificate");
    var failed = JsonSerializer.Deserialize<JsonElement>(rejected.Stdout);
    var failedFile = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "failed.json")));
    var failureBinding = failed.GetProperty("binding");
    if (!JsonElement.DeepEquals(failureBinding, failedFile.GetProperty("binding")) ||
        failureBinding.GetProperty("facts").GetArrayLength() != 12 ||
        failureBinding.GetProperty("facts").EnumerateArray().Any(fact =>
            fact.GetProperty("status").GetString() != "not covered"))
        throw new InvalidOperationException("Failed consumer binding payload is inconsistent: " + rejected.Output);
    Console.WriteLine("PASS failed.json and JSON retain the same incomplete deep attempt");
}
