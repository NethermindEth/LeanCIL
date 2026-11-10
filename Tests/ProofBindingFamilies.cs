#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ProofBindingCatalog.cs
#:include BindingFamilies/Recipes.cs

using System.Diagnostics;
using System.Text.Json;
using BindingFixtures;
using LeanCIL;

var framework = args switch
{
    [] => Root,
    ["--framework", var path] => Path.GetFullPath(path),
    _ => throw new ArgumentException("Usage: ProofBindingFamilies.cs [--framework <compiled checkout>]")
};
var cli = new[] { "dotnet", Path.Combine(framework, "Extractor/bin/Nethermind.LeanCIL.dll") };
var directory = At("artifacts/ProofBindingFamilies");
var package = Path.Combine(directory, "Package");
Directory.CreateDirectory(package);
var revision = Run(["git", "rev-parse", "HEAD"], framework).Trim();
File.Copy(Path.Combine(framework, "lean-toolchain"), Path.Combine(package, "lean-toolchain"), overwrite: true);
File.Copy(At("Tests/BindingFamilies/Support.lean"), Path.Combine(package, "Support.lean"), overwrite: true);
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
var families = FamilyRecipes.Reviewed;
var catalog = families.SelectMany(family => new[] { "scalar", "x64-v3" }
    .Select(profile => FamilyRecipes.Gate(family, profile))).ToArray();
var bindings = families.SelectMany(family => catalog.Where(gate =>
    gate.Method == FamilyRecipes.Gate(family, "scalar").Method).Select(gate => FamilyRecipes.Bind(family, gate)))
    .ToArray();
ProofBindingCatalog.Materialize(package, catalog, bindings);
ProofBindingCatalog.Materialize(package, catalog.Reverse(), bindings.Reverse(), check: true);
var extractions = catalog.Select(gate => new GeneratedExtraction(assembly, gate.Method,
    Path.Combine(directory, Path.GetFileNameWithoutExtension(gate.Proof)), gate.Profile)).ToArray();
ExtractBatch("extract", null, extractions, cli[1]);
var requests = catalog.Select((gate, index) => new
{
    output = extractions[index].Output, proof = Path.Combine(package, gate.Proof), theorem = gate.Theorem
}).ToArray();
var manifest = Path.Combine(directory, "requests.json");
var resultsPath = Path.Combine(directory, "results.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new { schema = 1, proofRoot = package, requests }));
var timer = Stopwatch.StartNew();
Run([.. cli, "verify-batch", manifest, "--results", resultsPath]);
var verificationSeconds = timer.Elapsed.TotalSeconds;
var results = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(resultsPath))!;
if (results.Length != 8 || results.Any(result => result.GetProperty("status").GetString() != "verified"))
    throw new InvalidOperationException("Every registered family/profile gate must certify.");
foreach (var request in requests)
{
    var certificate = Path.Combine(request.output, "verified.json");
    if (!File.Exists(certificate)) throw new InvalidOperationException("Missing certificate: " + certificate);
    using var report = JsonDocument.Parse(File.ReadAllText(certificate));
    var root = report.RootElement;
    if (!root.GetProperty("inputs").TryGetProperty("consumer:" + Path.GetFullPath(request.proof), out _) ||
        !root.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid",
            StringComparison.Ordinal) || root.GetProperty("axioms").EnumerateArray()
            .Any(axiom => axiom.GetString() == "sorryAx"))
        throw new InvalidOperationException("Generated binding lost source identity or ordinary audit.");
}

var equal = families[0];
var negativePackage = Path.Combine(directory, "NegativePackage");
Directory.CreateDirectory(negativePackage);
foreach (var file in new[] { "lean-toolchain", "lakefile.toml", "Support.lean" })
    File.Copy(Path.Combine(package, file), Path.Combine(negativePackage, file), overwrite: true);
Run(["lake", "update"], negativePackage);
var mutations = new[]
{
    (Name: "WrongWidth", Recipe: equal with { Width = 64 }, Original: equal, Assembly: assembly),
    (Name: "WrongSignedness", Recipe: equal with { Signed = true }, Original: equal, Assembly: assembly),
    (Name: "WrongPolarity", Recipe: equal with { Positive = false }, Original: equal, Assembly: assembly),
    (Name: "ChangedBody", Recipe: families[3], Original: families[3], Assembly: changedAssembly)
};
var negativeRequests = mutations.Select(mutation =>
{
    var gate = FamilyRecipes.Gate(mutation.Original, "scalar") with { Proof = mutation.Name + ".lean" };
    ProofBindingCatalog.Materialize(negativePackage, [gate], [FamilyRecipes.Bind(mutation.Recipe, gate)]);
    var output = Path.Combine(directory, mutation.Name);
    ExtractBatch("extract", null, [new(mutation.Assembly, gate.Method, output, gate.Profile)], cli[1]);
    return new
    {
        output, proof = Path.Combine(negativePackage, gate.Proof), theorem = gate.Theorem, expect = "rejected"
    };
}).ToArray();
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    schema = 1, proofRoot = negativePackage, requests = negativeRequests
}));
Run([.. cli, "verify-batch", manifest, "--results", Path.Combine(directory, "negative-results.json")]);
if (negativeRequests.Any(request => File.Exists(Path.Combine(request.output, "verified.json"))))
    throw new InvalidOperationException("A rejected recipe retained a certificate.");

int Lines(string path) => File.ReadLines(path).Count();
var sizes = new
{
    Schema = 1, FrameworkRevision = revision, RegisteredGates = catalog.Length,
    MaintainedRecipeLines = Lines(At("Tests/BindingFamilies/Recipes.cs")),
    SharedProofLines = Lines(At("Tests/BindingFamilies/Support.lean")),
    FixtureMethodLines = Lines(At("Tests/BindingFamilies/Methods.cs")),
    HarnessLines = Lines(At("Tests/ProofBindingFamilies.cs")),
    GeneratedBindingFiles = bindings.Length,
    GeneratedBindingLines = bindings.Sum(binding => Lines(Path.Combine(package, binding.Gate.Proof))),
    GeneratedBindingBytes = bindings.Sum(binding => new FileInfo(Path.Combine(package, binding.Gate.Proof)).Length),
    VerificationSeconds = verificationSeconds,
    Measurement = "Synthetic fixture counts, not consumer savings. Shared proofs and harness are separate. " +
        "Every generated binding is certified; source generation removes no proof obligations. " +
        "Wall time is an observation with uncontrolled external load."
};
File.WriteAllText(Path.Combine(directory, "sizes.json"),
    JsonSerializer.Serialize(sizes, new JsonSerializerOptions { WriteIndented = true }) + "\n");
Console.WriteLine(JsonSerializer.Serialize(sizes));
Console.WriteLine("PASS equality/bitwise bindings, exact signed widths, polarity and changed-body rejection");
