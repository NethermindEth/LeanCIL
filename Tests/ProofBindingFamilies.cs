#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs

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
          <TargetFramework>net11.0</TargetFramework><Optimize>true</Optimize>
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

// The negative catalog binds a family's proof with a wrong width or signedness to the production method.
foreach (var file in new[] { "lean-toolchain", "lakefile.toml", "Support.lean", "Binding.lean.in" })
    File.Copy(Path.Combine(package, file), Path.Combine(negativePackage, file), overwrite: true);
File.Copy(At("Tests/BindingFamilies/Negative.json"), Path.Combine(negativePackage, "Negative.json"), overwrite: true);
Run(["lake", "update"], negativePackage);
Run([.. cli, "bindings", Path.Combine(negativePackage, "Negative.json")]);
// A wrong width or signedness is a claim about the managed signature, which the binding's `signature` theorem
// decides; a wrong polarity or a changed body is a wrong result, which a verified refutation shows at an input.
var mutations = new[]
{
    (Name: "WrongWidth", Method: "Equal(uint,uint)", Assembly: assembly, Refutation: (string?)null),
    (Name: "WrongSignedness", Method: "Equal(uint,uint)", Assembly: assembly, Refutation: null),
    (Name: "WrongPolarity", Method: "Equal(uint,uint)", Assembly: assembly,
        Refutation: Refutation("32", ".i32 (if input.1 ≠ input.2 then 1 else 0)", 0, 0)),
    (Name: "ChangedBody", Method: "Xor(ulong,ulong)", Assembly: changedAssembly,
        Refutation: Refutation("64", ".i64 (input.1 ^^^ input.2)", 1, 1))
};
Directory.CreateDirectory(Path.Combine(negativePackage, "Refutation"));
var negativeRequests = mutations.Select(mutation =>
{
    var output = Path.Combine(directory, mutation.Name);
    ExtractBatch("extract", null, [new(mutation.Assembly, "BindingMethods::" + mutation.Method, output, "scalar")],
        cli[1]);
    if (mutation.Refutation is null)
        return new { output, proof = Path.Combine(negativePackage, "Negative", mutation.Name + ".lean"),
            theorem = "Generated.correctness" };
    var refutation = Path.Combine(negativePackage, "Refutation", mutation.Name + ".lean");
    File.WriteAllText(refutation, mutation.Refutation);
    return new { output, proof = refutation, theorem = "Refutation.refuted" };
}).ToArray();
var requests = Path.Combine(directory, "requests.json");
File.WriteAllText(requests, JsonSerializer.Serialize(new
{
    schema = 1, proofRoot = negativePackage, requests = negativeRequests
}));
var negativeResults = Path.Combine(directory, "negative-results.json");
var negative = Execute([.. cli, "verify-batch", requests, "--results", negativeResults]);
var outcomes = JsonDocument.Parse(File.ReadAllText(negativeResults)).RootElement.EnumerateArray().ToArray();
foreach (var ((name, _, _, refuting), outcome) in mutations.Zip(outcomes))
{
    var output = outcome.GetProperty("output").GetString()!;
    var failure = outcome.GetProperty("failure");
    var entry = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "identity.json"))).RootElement
        .GetProperty("entry").GetString();
    var met = refuting is not null
        ? outcome.GetProperty("status").GetString() == "verified" &&
            failure.GetProperty("kind").GetString() == "refutation" &&
            failure.GetProperty("method").GetProperty("entry").GetString() == entry
        : outcome.GetProperty("status").GetString() == "failed" &&
            outcome.GetProperty("stage").GetString() == "proof checking" &&
            failure.GetProperty("diagnostics")[0].GetProperty("message").GetString()!
                .Contains("Extracted.method0Signature\nis not definitionally equal", StringComparison.Ordinal) &&
            !File.Exists(Path.Combine(output, "verified.json"));
    if (!met)
        throw new InvalidOperationException($"{name} was not refuted or rejected at its signature: {outcome}\n{
            negative.Output}");
}
if (negative.Code != 1)
    throw new InvalidOperationException("The batch of wrong bindings did not fail its signature checks: " +
        negative.Output);

// The claim a mutated binding makes about `width`-bit arguments, refuted where the method returns another value.
static string Refutation(string width, string value, int left, int right) => $$"""
    import Extracted
    import CIL.Safety.MethodContract
    open CIL.Safety
    namespace Refutation
    /-- The result the mutated binding claims for every pair of words. -/
    def contract : MethodContract (CIL.W{{width}} × CIL.W{{width}}) where
      args input := [.scalar (.i{{width}} input.1), .scalar (.i{{width}} input.2)]
      pre _ _ := True
      footprint _ := []
      post input initial final values := final = initial ∧ values = [.scalar ({{value}})]
    /-- The extracted method returns another value at `({{left}}, {{right}})`. -/
    theorem refuted : contract.Refuted Extracted.program 0 :=
      .of_return (input := ({{left}}, {{right}})) (initial := Memory.empty) trivial
        (rfl : invoke Extracted.program 16 0 [.scalar (.i{{width}} {{left}}), .scalar (.i{{width}} {{right}})]
          Memory.empty = .ok _)
        (by rintro ⟨-, out, rfl, -, wrong⟩; revert wrong; decide)
    #print axioms refuted
    end Refutation

    """;

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
Console.WriteLine("PASS equality/bitwise bindings, exact signed widths, refuted polarity and changed body");
