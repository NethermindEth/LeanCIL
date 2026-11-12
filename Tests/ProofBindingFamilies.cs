#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Diagnostics;
using System.Text.Json;

var framework = args switch
{
    [] => Root,
    ["--framework", var path] => Path.GetFullPath(path),
    _ => throw new ArgumentException("Usage: ProofBindingFamilies.cs [--framework <compiled checkout>]")
};
var cli = new[] { "dotnet", Path.Combine(framework, "Extractor/bin/Nethermind.LeanCIL.dll") };
var directory = At("artifacts/ProofBindingFamilies");
var package = Path.Combine(directory, "Package");
var negativePackage = Path.Combine(directory, "NegativePackage");
// Sources left by an earlier run must not stand in for the ones the catalogs generate.
foreach (var generated in new[] { Path.Combine(package, "Bindings"), Path.Combine(negativePackage, "Negative") })
    if (Directory.Exists(generated)) Directory.Delete(generated, recursive: true);
Directory.CreateDirectory(package);
Directory.CreateDirectory(negativePackage);
var revision = Run(["git", "rev-parse", "HEAD"], framework).Trim();
File.Copy(Path.Combine(framework, "lean-toolchain"), Path.Combine(package, "lean-toolchain"), overwrite: true);
foreach (var file in new[] { "Support.lean", "Binding.lean.in", "Bindings.json" })
    File.Copy(At("Tests/BindingFamilies/" + file), Path.Combine(package, file), overwrite: true);
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"binding-families\"\n[[require]]\nname = \"leancil\"\ngit = " +
    JsonSerializer.Serialize(framework.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) +
    "\n[[lean_lib]]\nname = \"Support\"\n");
Run(["lake", "update"], package);

string Build(string name, bool changed)
{
    var source = Path.Combine(directory, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Methods.csproj"), """
        <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>
          <TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize>
        </PropertyGroup></Project>
        """);
    var methods = File.ReadAllText(At("Tests/BindingFamilies/Methods.cs"));
    File.WriteAllText(Path.Combine(source, "Methods.cs"), changed
        ? methods.Replace("left ^ right", "left | right", StringComparison.Ordinal) : methods);
    Run(["dotnet", "build", source, "-c", "Release", "-o", Path.Combine(source, "output"),
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
    return Path.Combine(source, "output/Methods.dll");
}
var assembly = Build("Production", changed: false);
var changedAssembly = Build("Changed", changed: true);

// The manifest lists no gate itself: every gate comes from the catalog, generated before any source is read.
var manifest = Path.Combine(directory, "gates.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    schema = 1, proofRoot = "Package", outputRoot = "Outputs", gates = Array.Empty<object>(),
    defaults = new { assembly = Path.GetRelativePath(directory, assembly).Replace('\\', '/') },
    catalogs = new[] { "Package/Bindings.json" }
}));
var resultsPath = Path.Combine(directory, "results.json");
var timer = Stopwatch.StartNew();
Run([.. cli, "gates", manifest, "--results", resultsPath]);
var verificationSeconds = timer.Elapsed.TotalSeconds;
var results = JsonDocument.Parse(File.ReadAllText(resultsPath)).RootElement.GetProperty("rows").EnumerateArray()
    .ToArray();
if (results.Length != 8 || results.Any(result => result.GetProperty("status").GetString() != "verified"))
    throw new InvalidOperationException("Every generated family/profile gate must certify.");
foreach (var result in results)
{
    var certificate = Path.Combine(result.GetProperty("output").GetString()!, "verified.json");
    if (!File.Exists(certificate)) throw new InvalidOperationException("Missing certificate: " + certificate);
    using var report = JsonDocument.Parse(File.ReadAllText(certificate));
    var root = report.RootElement;
    var proof = Path.GetFullPath(result.GetProperty("proof").GetString()!);
    if (!root.GetProperty("inputs").TryGetProperty("consumer:" + proof, out _) ||
        !root.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid",
            StringComparison.Ordinal) || root.GetProperty("axioms").EnumerateArray()
            .Any(axiom => axiom.GetString() == "sorryAx"))
        throw new InvalidOperationException("Generated binding lost source identity or ordinary audit.");
}

// Each mutation binds a family's proof with one wrong field, or the right proof to a changed body.
foreach (var file in new[] { "lean-toolchain", "lakefile.toml", "Support.lean", "Binding.lean.in" })
    File.Copy(Path.Combine(package, file), Path.Combine(negativePackage, file), overwrite: true);
File.Copy(At("Tests/BindingFamilies/Negative.json"), Path.Combine(negativePackage, "Negative.json"), overwrite: true);
Run(["lake", "update"], negativePackage);
Run([.. cli, "bindings", Path.Combine(negativePackage, "Negative.json")]);
var mutations = new[]
{
    (Name: "WrongWidth", Method: "Equal(uint,uint)", Assembly: assembly),
    (Name: "WrongSignedness", Method: "Equal(uint,uint)", Assembly: assembly),
    (Name: "WrongPolarity", Method: "Equal(uint,uint)", Assembly: assembly),
    (Name: "ChangedBody", Method: "Xor(ulong,ulong)", Assembly: changedAssembly)
};
var negativeRequests = mutations.Select(mutation =>
{
    var output = Path.Combine(directory, mutation.Name);
    ExtractBatch("extract", null, [new(mutation.Assembly, "BindingMethods::" + mutation.Method, output, "scalar")],
        cli[1]);
    return new
    {
        output, proof = Path.Combine(negativePackage, "Negative", mutation.Name + ".lean"),
        theorem = "Generated.correctness", expect = "rejected"
    };
}).ToArray();
var requests = Path.Combine(directory, "requests.json");
File.WriteAllText(requests, JsonSerializer.Serialize(new
{
    schema = 1, proofRoot = negativePackage, requests = negativeRequests
}));
Run([.. cli, "verify-batch", requests, "--results", Path.Combine(directory, "negative-results.json")]);
if (negativeRequests.Any(request => File.Exists(Path.Combine(request.output, "verified.json"))))
    throw new InvalidOperationException("A rejected catalog binding retained a certificate.");

int Lines(string path) => File.ReadLines(path).Count();
var generatedFiles = Directory.GetFiles(Path.Combine(package, "Bindings"), "*.lean");
var sizes = new
{
    Schema = 1, FrameworkRevision = revision, RegisteredGates = results.Length,
    MaintainedCatalogLines = Lines(At("Tests/BindingFamilies/Bindings.json")) +
        Lines(At("Tests/BindingFamilies/Binding.lean.in")),
    SharedProofLines = Lines(At("Tests/BindingFamilies/Support.lean")),
    FixtureMethodLines = Lines(At("Tests/BindingFamilies/Methods.cs")),
    HarnessLines = Lines(At("Tests/ProofBindingFamilies.cs")),
    GeneratedBindingFiles = generatedFiles.Length,
    GeneratedBindingLines = generatedFiles.Sum(Lines),
    GeneratedBindingBytes = generatedFiles.Sum(path => new FileInfo(path).Length),
    VerificationSeconds = verificationSeconds,
    Measurement = "Synthetic fixture counts, not consumer savings. Shared proofs and harness are separate. " +
        "Every generated binding is certified; source generation removes no proof obligations. " +
        "Wall time is an observation with uncontrolled external load."
};
File.WriteAllText(Path.Combine(directory, "sizes.json"),
    JsonSerializer.Serialize(sizes, new JsonSerializerOptions { WriteIndented = true }) + "\n");
Console.WriteLine(JsonSerializer.Serialize(sizes));
Console.WriteLine("PASS equality/bitwise bindings, exact signed widths, polarity and changed-body rejection");
