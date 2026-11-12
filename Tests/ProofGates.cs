#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// One fixture project builds every case of `First` from its FixtureCase property; `Second` is a prebuilt
// assembly from another project, so selection by project directory has something to leave out.
var cli = new[] { "dotnet", ExtractorPath };
var directory = At("artifacts/ProofGates-" + Guid.NewGuid().ToString("N"));
var package = Path.Combine(directory, "Package");
var fixture = Path.Combine(directory, "Fixture");
var second = Path.Combine(directory, "Second");
foreach (var path in new[] { package, fixture, second }) Directory.CreateDirectory(path);
File.WriteAllText(Path.Combine(fixture, "Gates.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk">
      <PropertyGroup>
        <TargetFramework>net10.0</TargetFramework>
        <Optimize>true</Optimize>
        <DefineConstants>$(DefineConstants);$(FixtureCase)</DefineConstants>
      </PropertyGroup>
    </Project>
    """);
File.WriteAllText(Path.Combine(fixture, "First.cs"), """
    public static class Methods
    {
    #if Baseline
        public static ulong First(ulong x, ulong y) => unchecked(x + y);
    #elif Reordered
        public static ulong First(ulong x, ulong y) => unchecked(y + x);
    #elif WrongXor
        public static ulong First(ulong x, ulong y) => x ^ y;
    #elif WrongSub
        public static ulong First(ulong x, ulong y) => unchecked(x - y);
    #elif Absent
        public static ulong Other(ulong x, ulong y) => x;
    #else
    #error FixtureCase names no fixture case.
    #endif
    }
    """);
File.WriteAllText(Path.Combine(second, "Second.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk">
      <PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
    </Project>
    """);
File.WriteAllText(Path.Combine(second, "Second.cs"),
    "public static class Methods { public static ulong Second(ulong x, ulong y) => unchecked(x - y); }");
// A method no gate reaches, in the same assembly: changing it selects nothing.
File.WriteAllText(Path.Combine(second, "Spare.cs"),
    "public static class Spare { public static ulong Unused(ulong x) => x; }");
Run(["dotnet", "build", second, "-c", "Release", "-o", Path.Combine(second, "output")]);

File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"gates-fixture\"\n[[require]]\nname = \"leancil\"\ngit = " +
    JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " +
    JsonSerializer.Serialize(Run(["git", "rev-parse", "HEAD"]).Trim()) +
    "\n[[lean_lib]]\nname = \"FirstSupport\"\n[[lean_lib]]\nname = \"SecondSupport\"\n");
Run(["lake", "update"], package);
// A tactic that reads past the end of an array: Lean prints a panic and the proof continues.
const string PastEnd = """
    open Lean Elab Tactic in
    /-- Reads the second entry of an empty array, as a tactic that assumed a longer term would. -/
    elab "read_past_end" : tactic => do
      let entries : Array Nat := #[]
      if entries[1]! == 7 then logInfo "seven"
    """;
string Correctness(string name, string support, string operation, string prefix = "", string tactic = "") => $$"""
    import Extracted
    import CIL.Safety.SymbolicExecution
    import {{support}}Support
    open CIL.Safety
    {{prefix}}
    /-- The extracted method computes wrapping arithmetic in arbitrary caller memory. -/
    theorem {{name}}.correctness (left right : CIL.W64) (memory : Memory) :
        ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 left), .scalar (.i64 right)]
          memory = .ok (memory, [.scalar (.i64 (left {{operation}} right))]) := by
      {{tactic}}cil_checked_steps []
      all_goals simp only [BitVec.add_comm]
    #print axioms {{name}}.correctness
    """ + "\n";
foreach (var name in new[] { "First", "Second" })
    File.WriteAllText(Path.Combine(package, name + "Support.lean"),
        $"theorem {name}.support : True := True.intro\n#print axioms {name}.support\n");
File.WriteAllText(Path.Combine(package, "First.lean"), Correctness("First", "First", "+"));
File.WriteAllText(Path.Combine(package, "Second.lean"), Correctness("Second", "Second", "-"));
File.WriteAllText(Path.Combine(package, "Reordered.lean"), Correctness("Reordered", "First", "+"));
File.WriteAllText(Path.Combine(package, "Panicking.lean"),
    Correctness("Panicking", "First", "+", PastEnd, "read_past_end\n  "));
File.WriteAllText(Path.Combine(package, "Trivial.lean"), """
    import Extracted
    /-- States nothing about the extracted program, so it verifies against any extraction. -/
    theorem Trivial.refuted : True := True.intro
    #print axioms Trivial.refuted

    """);
// A recorded witness gives inputs whose wrong result differs from the wrapping sum.
var template = Path.Combine(package, "Refutation.lean.in");
File.WriteAllText(template, """
    import Extracted
    import CIL.Safety.MethodContract
    open CIL.Safety
    /-- The witness inputs make the extracted method return other than their wrapping sum. -/
    theorem FixtureWitness.refuted : ¬ ∀ (left right : CIL.W64) (memory : Memory),
        ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 left), .scalar (.i64 right)]
          memory = .ok (memory, [.scalar (.i64 (left + right))]) := by
      intro holds
      obtain ⟨fuel, ran⟩ := holds @LEFT@ @RIGHT@ Memory.empty
      have returned := congrArg Prod.snd (invoke_ok_unique ran (rfl : invoke Extracted.program 16 0
        [.scalar (.i64 @LEFT@), .scalar (.i64 @RIGHT@)] Memory.empty = .ok _))
      revert returned
      decide
    #print axioms FixtureWitness.refuted

    """);
var witnesses = new Dictionary<string, (ulong Left, ulong Right)>
{
    ["WrongXor"] = (1, 1), ["WrongSub"] = (0, 1), ["Agreeing"] = (0, 0)
};
if ((1UL ^ 1UL) == 1UL + 1UL || unchecked(0UL - 1UL) == 0UL + 1UL || (0UL ^ 0UL) != 0UL + 0UL)
    throw new Exception("A recorded witness does not separate its wrong case from the wrapping sum.");

object Build(string fixtureCase) =>
    new { project = "fixture", properties = new Dictionary<string, string> { ["FixtureCase"] = fixtureCase } };
object Refute(string witness, string? extra = null)
{
    var values = new Dictionary<string, string>
    {
        ["LEFT"] = witnesses[witness].Left.ToString(), ["RIGHT"] = witnesses[witness].Right.ToString()
    };
    if (extra is not null) values[extra] = "0";
    return new { template = "Refutation.lean.in", theorem = "FixtureWitness.refuted", values };
}
var scalar = new[] { "scalar" };
var manifest = Path.Combine(directory, "gates.json");
var results = Path.Combine(directory, "results.json");
var outputs = Path.Combine(directory, "Outputs");
void Manifest(bool controls)
{
    var variants = new List<object>
    {
        new { name = "baseline", build = Build("Baseline"), expect = "certifies", program = "same" },
        new { name = "reordered", build = Build("Reordered"), expect = "certifies", program = "different",
            proof = "Reordered.lean", theorem = "Reordered.correctness" },
        new { name = "wrong-xor", build = Build("WrongXor"), expect = "rejected", program = "different",
            refutation = Refute("WrongXor") },
        new { name = "wrong-sub", build = Build("WrongSub"), profiles = scalar, expect = "rejected",
            program = "different", refutation = Refute("WrongSub") }
    };
    // Each control fails on one leg; none of these failures may count as a rejection.
    if (controls)
        variants.AddRange(
        [
            new { name = "refutation-fails", build = Build("WrongXor"), profiles = scalar, expect = "rejected",
                refutation = Refute("Agreeing") },
            new { name = "production-verifies", build = Build("Reordered"), profiles = scalar, expect = "rejected",
                refutation = new { proof = "Trivial.lean", theorem = "Trivial.refuted" } },
            new { name = "program-differs", build = Build("WrongXor"), profiles = scalar, expect = "certifies",
                program = "same" },
            new { name = "not-renamed", build = Build("Baseline"), profiles = scalar, expect = "certifies",
                program = "renamed" },
            new { name = "missing-proof", build = Build("WrongXor"), profiles = scalar, expect = "rejected",
                proof = "Missing.lean", theorem = "Missing.correctness", refutation = Refute("WrongXor") },
            new { name = "missing-template", build = Build("WrongXor"), profiles = scalar, expect = "rejected",
                refutation = new { template = "Missing.lean.in", theorem = "FixtureWitness.refuted",
                    values = new Dictionary<string, string> { ["LEFT"] = "1" } } },
            new { name = "unused-value", build = Build("WrongXor"), profiles = scalar, expect = "rejected",
                refutation = Refute("WrongXor", extra: "UNUSED") },
            new { name = "build-fails", build = Build("Unknown"), profiles = scalar, expect = "rejected",
                refutation = Refute("WrongXor") },
            new { name = "extraction-fails", build = Build("Absent"), profiles = scalar, expect = "rejected",
                refutation = Refute("WrongXor") },
            new { name = "internal-error", build = Build("WrongXor"), profiles = scalar, expect = "rejected",
                proof = "Panicking.lean", theorem = "Panicking.correctness", refutation = Refute("WrongXor") }
        ]);
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        schema = 1, proofRoot = "Package", outputRoot = "Outputs", generatedRoot = "Generated",
        projects = new Dictionary<string, object>
        {
            ["fixture"] = new { path = "Fixture/Gates.csproj", assembly = "Gates.dll",
                properties = new Dictionary<string, string>
                {
                    ["Configuration"] = "Release", ["FixtureCase"] = "Baseline"
                } }
        },
        gates = new object[]
        {
            new { name = "first", build = new { project = "fixture" }, method = "Methods::First(ulong,ulong)",
                profiles = new[] { "scalar", "x64-v3" }, proof = "First.lean", theorem = "First.correctness",
                variants },
            new { name = "second", assembly = "Second/output/Second.dll", method = "Methods::Second(ulong,ulong)",
                profiles = new[] { "scalar", "x64-v3" }, proof = "Second.lean", theorem = "Second.correctness" }
        }
    }));
}
JsonElement[] Gates(int expectedCode, params string[] options)
{
    var result = Execute([.. cli, "gates", manifest, "--results", results, .. options]);
    if (result.Code != expectedCode) throw new Exception("Unexpected gates exit:\n" + result.Output);
    return JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(results))!;
}
string? Text(JsonElement row, string name) =>
    row.GetProperty(name).ValueKind == JsonValueKind.Null ? null : row.GetProperty(name).GetString();
JsonElement Row(JsonElement[] rows, string variant, string profile = "scalar", string gate = "first") =>
    rows.Single(row => Text(row, "gate") == gate && Text(row, "variant") == variant &&
        Text(row, "profile") == profile);
void Expect(bool holds, string message, JsonElement? row = null)
{
    if (!holds) throw new Exception(message + (row is { } shown ? ":\n" + shown : ""));
}
void NoRejectedCertificates(IEnumerable<JsonElement> rows)
{
    foreach (var row in rows.Where(row => Text(row, "expect") == "rejected"))
        Expect(!File.Exists(Path.Combine(Text(row, "output")!, "verified.json")),
            "A rejection expectation retained a certificate", row);
}
string Assembly(JsonElement row)
{
    var output = Text(row, "output")!;
    var identity = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "identity.json"))).RootElement;
    return Path.GetFullPath(identity.GetProperty("assemblyPath").GetString()!, output);
}

Manifest(controls: false);
var all = Gates(0);
Expect(all.Length == 11 && all.Count(row => Text(row, "status") == "rejected") == 3,
    "Expected two methods, two profiles and every variant from one manifest");
foreach (var row in all)
{
    var variant = Text(row, "variant")!;
    var rejected = variant.StartsWith("wrong-", StringComparison.Ordinal);
    Expect(Text(row, "status") == (rejected ? "rejected" : "verified") &&
        Text(row, "build") == (Text(row, "gate") == "first" ? "built" : null) &&
        Text(row, "extraction") == "extracted" &&
        Text(row, "program") == (variant == "production" ? null : "passed") &&
        (rejected ? row.GetProperty("refutation").GetProperty("status").GetString() == "verified"
            : row.GetProperty("refutation").ValueKind == JsonValueKind.Null),
        "A variant did not report its build, extraction, program, refutation and proof outcomes", row);
}
Expect(!all.Any(row => Text(row, "variant") == "wrong-sub" && Text(row, "profile") == "x64-v3"),
    "A variant restricted to one profile ran under another");
NoRejectedCertificates(all);
Expect(Directory.GetDirectories(Path.Combine(outputs, "builds")).Length == 4 &&
    Assembly(Row(all, "production")) == Assembly(Row(all, "baseline", "x64-v3")),
    "Production and baseline, with the same project and properties, did not share one build");
foreach (var (variant, profile, witness) in
    new[] { ("wrong-xor", "x64-v3", "WrongXor"), ("wrong-sub", "scalar", "WrongSub") })
{
    var generated = File.ReadAllText(Path.Combine(package, "Generated", "first", profile, variant + ".lean"));
    Expect(!generated.Contains('@') && !generated.Contains('\r') &&
        generated.Contains($"holds {witnesses[witness].Left} {witnesses[witness].Right} Memory.empty"),
        "A template was not instantiated with its witness: " + variant);
}

var proofChanged = Gates(0, "--changed", Path.Combine(package, "FirstSupport.lean"), "--profile", "scalar");
Expect(proofChanged.Length == 5 && proofChanged.All(row => Text(row, "gate") == "first"),
    "Proof closure selection included the unrelated second method");
var sourceChanged = Gates(0, "--changed", Path.Combine(second, "Second.cs"));
Expect(sourceChanged.Length == 2 && sourceChanged.All(row => Text(row, "theorem") == "Second.correctness"),
    "Method source selection did not follow the extracted method metadata");
var spareChanged = Execute([.. cli, "gates", manifest, "--changed", Path.Combine(second, "Spare.cs")]);
Expect(spareChanged.Code != 0 &&
    spareChanged.Output.Contains("No gates depend on the changed paths.", StringComparison.Ordinal),
    "A source no extracted method reaches selected its assembly's gates");
var templateChanged = Gates(0, "--changed", template, "--profile", "scalar");
Expect(templateChanged.Select(row => Text(row, "variant")).Order().SequenceEqual(["wrong-sub", "wrong-xor"]),
    "A changed template did not select exactly the variants instantiated from it");
var fixtureChanged = Gates(0, "--changed", Path.Combine(fixture, "First.cs"), "--profile", "scalar");
Expect(fixtureChanged.Length == 5 && fixtureChanged.All(row => Text(row, "gate") == "first"),
    "A changed fixture source did not select exactly the variants built from its project");
var filtered = Gates(0, "--method", "Second", "--profile", "scalar", "--check");
Expect(filtered.Length == 1 && Text(filtered[0], "status") == "checked" &&
    !File.Exists(Path.Combine(Text(filtered[0], "output")!, "verified.json")),
    "Catalog filters or compile-only results were incorrect");
var json = Execute([.. cli, "gates", manifest, "--method", "Second", "--profile", "scalar", "--check",
    "--format", "json"]);
var document = JsonDocument.Parse(json.Stdout).RootElement;
Expect(json.Code == 0 && document.GetProperty("failed").GetInt32() == 0 &&
    document.GetProperty("variants").EnumerateArray().Single().GetProperty("status").GetString() == "checked",
    "The JSON report did not hold one document with the variant results:\n" + json.Output);
var checkRejected = Execute([.. cli, "gates", manifest, "--method", "First", "--profile", "scalar", "--check"]);
Expect(checkRejected.Code != 0 && checkRejected.Output.Contains("--check cannot evaluate", StringComparison.Ordinal),
    "--check accepted a rejection expectation");
Console.WriteLine("PASS project builds, per-variant proofs and profiles, witness refutations and selection");

Manifest(controls: true);
var controls = Gates(1, "--method", "First", "--profile", "scalar");
foreach (var variant in new[] { "production", "baseline", "reordered", "wrong-xor", "wrong-sub" })
    Expect(Text(Row(controls, variant), "status") != "failed", "A failing control failed another variant: " + variant,
        Row(controls, variant));
var requested = JsonDocument.Parse(File.ReadAllText(Path.Combine(outputs, "requests.json"))).RootElement
    .GetProperty("requests").EnumerateArray().Select(request => request.GetProperty("output").GetString()).ToHashSet();
void Failed(string variant, string message, Func<JsonElement, bool> leg)
{
    var row = Row(controls, variant);
    Expect(Text(row, "status") == "failed" && leg(row), message, row);
}
Failed("refutation-fails", "A refutation that does not verify passed or was misreported", row =>
    Text(row, "error") is null && row.GetProperty("refutation").GetProperty("status").GetString() == "failed");
Failed("production-verifies", "A proof that verifies counted as a rejection", row =>
    Text(row, "error")!.Contains("but the proof checked", StringComparison.Ordinal) &&
    row.GetProperty("refutation").GetProperty("status").GetString() == "verified");
foreach (var variant in new[] { "program-differs", "not-renamed" })
    Failed(variant, "A program comparison that does not hold passed or reached verification", row =>
        Text(row, "stage") == "program comparison" && Text(row, "program") == "failed" &&
        !requested.Contains(Text(row, "output")));
// The refutation is then the output's last checked request, so it must not leave its certificate.
Failed("missing-proof", "A missing proof counted as a rejection", row =>
    Text(row, "stage") == "proof selection" && Text(row, "error")!.Contains("not found", StringComparison.Ordinal) &&
    row.GetProperty("refutation").GetProperty("status").GetString() == "verified");
foreach (var variant in new[] { "missing-template", "unused-value" })
    Failed(variant, "A template that cannot be instantiated counted as a rejection", row =>
        Text(row, "stage") == "refutation template" && !requested.Contains(Text(row, "output")) &&
        !File.Exists(Path.Combine(package, "Generated", "first", "scalar", variant + ".lean")));
Failed("build-fails", "A failed build counted as a rejection", row =>
    Text(row, "stage") == "build" && Text(row, "build") == "failed");
Failed("extraction-fails", "A failed extraction counted as a rejection", row =>
    Text(row, "stage") == "extraction" && Text(row, "build") == "built" && Text(row, "extraction") == "failed");
Failed("internal-error", "A proof that panics counted as a rejection", row =>
    Text(row, "error")!.Contains("Lean reported an internal error", StringComparison.Ordinal));
NoRejectedCertificates(controls);

// A profile the gate does not list is a manifest error, before anything is built.
File.WriteAllText(manifest, File.ReadAllText(manifest)
    .Replace("\"profiles\":[\"scalar\"]", "\"profiles\":[\"arm64\"]"));
var invalid = Execute([.. cli, "gates", manifest]);
Expect(invalid.Code != 0 && invalid.Output.Contains("lists a profile its gate does not", StringComparison.Ordinal),
    "A variant profile outside its gate's was accepted");
Console.WriteLine("PASS build, extraction, program, template, proof and internal failures never count as rejections");
