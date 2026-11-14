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
        <TargetFramework>net11.0</TargetFramework>
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
      <PropertyGroup><TargetFramework>net11.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
    </Project>
    """);
File.WriteAllText(Path.Combine(second, "Second.cs"),
    "public static class Methods { public static ulong Second(ulong x, ulong y) => unchecked(x - y); }");
// Spare.cs holds a method of the same assembly that no gate reaches, so changing it selects nothing.
File.WriteAllText(Path.Combine(second, "Spare.cs"),
    "public static class Spare { public static ulong Unused(ulong x) => x; }");
// A binding catalog generates the gates of Third, one per profile.
File.WriteAllText(Path.Combine(second, "Third.cs"),
    "public static class Thirds { public static ulong Third(ulong x, ulong y) => unchecked(x * y); }");
Run(["dotnet", "build", second, "-c", "Release", "-o", Path.Combine(second, "output")]);

File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"gates-fixture\"\n[[require]]\nname = \"leancil\"\ngit = " +
    JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " +
    JsonSerializer.Serialize(Run(["git", "rev-parse", "HEAD"]).Trim()) +
    "\n[[lean_lib]]\nname = \"FirstSupport\"\n[[lean_lib]]\nname = \"SecondSupport\"\n");
Run(["lake", "update"], package);
// This tactic reads past the end of an array; Lean prints a panic and the proof continues.
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
File.WriteAllText(Path.Combine(package, "Third.lean.in"), Correctness("Third.@name@", "Second", "*"));
File.WriteAllText(Path.Combine(package, "Third.json"), """
    { "schema": 1, "generatedRoot": "Bindings", "families": [ {
      "template": "Third.lean.in",
      "dimensions": [ [ { "profile": "scalar", "name": "Scalar" }, { "profile": "x64-v3", "name": "Vector" } ] ],
      "gate": { "name": "third-@profile@", "method": "Thirds::Third(ulong,ulong)", "profiles": [ "@profile@" ],
                "proof": "Third@name@.lean", "theorem": "Third.@name@.correctness" } } ] }
    """);
File.WriteAllText(Path.Combine(package, "Reordered.lean"), Correctness("Reordered", "First", "+"));
File.WriteAllText(Path.Combine(package, "Panicking.lean"),
    Correctness("Panicking", "First", "+", PastEnd, "read_past_end\n  "));
File.WriteAllText(Path.Combine(package, "Trivial.lean"), """
    import Extracted
    /-- States nothing about the extracted program, so it verifies against any extraction. -/
    theorem Trivial.holds : True := True.intro
    #print axioms Trivial.holds

    """);
// Weaker.lean adds a premise to production's statement, so the kernel must not accept it as production's.
File.WriteAllText(Path.Combine(package, "Weaker.lean"), Correctness("Weaker", "First", "+")
    .Replace("(memory : Memory) :", "(memory : Memory) (_small : left = 0) :"));
// Definitional.lean names production's `0` through a definition, which the kernel unfolds.
File.WriteAllText(Path.Combine(package, "Definitional.lean"), """
    import Extracted
    import CIL.Safety.SymbolicExecution
    import FirstSupport
    open CIL.Safety
    /-- The entry method's index. -/
    def Definitional.entry : Nat := 0
    /-- Production's statement, proved directly. -/
    theorem Definitional.original (left right : CIL.W64) (memory : Memory) :
        ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 left), .scalar (.i64 right)]
          memory = .ok (memory, [.scalar (.i64 (left + right))]) := by
      cil_checked_steps []
      all_goals simp only [BitVec.add_comm]
    /-- Production's statement with the entry index named by `Definitional.entry`. -/
    theorem Definitional.correctness (left right : CIL.W64) (memory : Memory) :
        ∃ fuel, invoke Extracted.program fuel Definitional.entry
          [.scalar (.i64 left), .scalar (.i64 right)]
          memory = .ok (memory, [.scalar (.i64 (left + right))]) :=
      Definitional.original left right memory
    #print axioms Definitional.correctness

    """);
// The variant's values override the named template's; NOTE spans lines and PREFIX is empty.
File.WriteAllText(Path.Combine(package, "Correctness.lean.in"),
    Correctness("Templated", "First", "@OPERATION@", prefix: "-- @NOTE@@PREFIX@"));
File.WriteAllText(Path.Combine(directory, "plain.json"), """
    { "name": "plain-file", "architecture": "scalar", "nativeWidth": 64, "littleEndian": true,
      "advSimd": false, "sse2": false, "ssse3": false, "sse42": false, "avx": false, "avx2": false,
      "avx512F": false, "avx512FVL": false, "bmi1": false, "sse41": false, "avx512DQ": false,
      "avx512DQVL": false, "bmi2": false, "armBase64": false, "vector256Accelerated": false,
      "x86Base64": false, "vector128Accelerated": false, "avx512Vbmi": false, "aes": false, "armAes": false }
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
object Trivial = new { proof = "Trivial.lean", theorem = "Trivial.holds" };
void Manifest(bool controls, params object[] extra)
{
    var variants = new List<object>
    {
        new { name = "baseline", build = Build("Baseline"), expect = "certifies", program = "same" },
        new { name = "reordered", build = Build("Reordered"), expect = "certifies", program = "different",
            proof = "Reordered.lean", theorem = "Reordered.correctness" },
        new { name = "wrong-xor", build = Build("WrongXor"), expect = "rejected", program = "different",
            refutation = Refute("WrongXor") },
        new { name = "wrong-sub", build = Build("WrongSub"), profiles = scalar, expect = "rejected",
            program = "different", refutation = Refute("WrongSub") },
        new { name = "definitional", build = Build("Baseline"), profiles = scalar, expect = "certifies",
            proof = "Definitional.lean", theorem = "Definitional.correctness" },
        new { name = "templated", build = Build("Baseline"), profiles = scalar, expect = "certifies",
            proof = new { template = "correctness", values = new Dictionary<string, string>
                { ["OPERATION"] = "+", ["NOTE"] = "Generated from\n-- the correctness template." } },
            theorem = "Templated.correctness" },
        new { name = "witness-accepted", build = Build("Baseline"), profiles = scalar, expect = "certifies",
            proof = "Trivial.lean", theorem = "Trivial.holds", statement = "independent" },
        new { name = "unchanged-reordered", build = Build("Reordered"), profiles = scalar, expect = "unchanged",
            program = "same", programOf = "reordered" }
    };
    variants.AddRange(extra);
    // Each control fails on one leg; none of these failures may count as a rejection.
    if (controls)
        variants.AddRange(
        [
            new { name = "refutation-fails", build = Build("WrongXor"), profiles = scalar, expect = "rejected",
                refutation = Refute("Agreeing") },
            new { name = "production-verifies", build = Build("Reordered"), profiles = scalar, expect = "rejected",
                refutation = Trivial },
            new { name = "unrelated-refutation", build = Build("WrongXor"), profiles = scalar, expect = "rejected",
                refutation = Trivial },
            new { name = "weaker-statement", build = Build("Baseline"), profiles = scalar, expect = "certifies",
                proof = "Weaker.lean", theorem = "Weaker.correctness" },
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
        defaults = new { assembly = "Second/output/Second.dll" }, catalogs = new[] { "Package/Third.json" },
        templates = new Dictionary<string, object>
        {
            ["correctness"] = new { path = "Correctness.lean.in", values = new Dictionary<string, string>
                { ["OPERATION"] = "-", ["NOTE"] = "replaced", ["PREFIX"] = "" } }
        },
        profiles = new Dictionary<string, string> { ["plain"] = "@plain.json" },
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
                profiles = new[] { "scalar", "x64-v3", "plain" }, proof = "Second.lean",
                theorem = "Second.correctness" }
        }
    }));
}
JsonElement[] Gates(int expectedCode, params string[] options)
{
    var result = Execute([.. cli, "gates", manifest, "--results", results, .. options]);
    if (result.Code != expectedCode) throw new Exception("Unexpected gates exit:\n" + result.Output);
    return [.. JsonDocument.Parse(File.ReadAllText(results)).RootElement.GetProperty("rows").EnumerateArray()];
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

string? StatementStatus(JsonElement row) =>
    row.GetProperty("statement") is { ValueKind: JsonValueKind.Object } statement
    ? statement.GetProperty("status").GetString() : null;
Manifest(controls: false);
var bindings = Path.Combine(package, "Bindings");
Expect(!Directory.Exists(bindings), "A catalog's sources existed before the first run");
var all = Gates(0);
Expect(all.Length == 18 && all.Count(row => Text(row, "status") == "rejected") == 3,
    "Expected three methods, three profiles, every variant and the catalog's gates from one manifest");
Expect(all.Where(row => Text(row, "gate")!.StartsWith("third-", StringComparison.Ordinal))
    .Select(row => Text(row, "id")).Order().SequenceEqual(["third-scalar/scalar/production",
        "third-x64-v3/x64-v3/production"]) && File.Exists(Path.Combine(bindings, "ThirdVector.lean")),
    "The catalog's gates were not generated and verified with the manifest's");
string[] programmed = ["baseline", "reordered", "wrong-xor", "wrong-sub", "unchanged-reordered"];
foreach (var row in all)
{
    var variant = Text(row, "variant")!;
    var rejected = variant.StartsWith("wrong-", StringComparison.Ordinal);
    // The kernel accepts reordered structurally and definitional only by unfolding Definitional.entry.
    var statement = variant is "production" or "unchanged-reordered" ? null
        : variant == "witness-accepted" ? "independent" : "same";
    var status = rejected ? "rejected" : variant == "unchanged-reordered" ? "unchanged" : "verified";
    Expect(Text(row, "status") == status &&
        Text(row, "build") == (Text(row, "gate") == "first" ? "built" : null) &&
        Text(row, "extraction") == "extracted" &&
        Text(row, "program") == (programmed.Contains(variant) ? "passed" : null) &&
        (rejected ? row.GetProperty("refutation").GetProperty("status").GetString() == "verified"
            : row.GetProperty("refutation").ValueKind == JsonValueKind.Null) &&
        StatementStatus(row) == statement,
        "A variant did not report its build, extraction, program, refutation, proof and statement outcomes", row);
}
var requestedOutputs = File.ReadAllText(Path.Combine(outputs, "requests.json"));
Expect(!requestedOutputs.Contains(JsonSerializer.Serialize(Text(Row(all, "unchanged-reordered"), "output"))),
    "An unchanged variant requested a proof");
var templated = File.ReadAllText(Path.Combine(package, "Generated", "first", "scalar", "templated", "Proof.lean"));
Expect(templated.Contains("(left + right)") && templated.Contains("-- Generated from\n-- the correctness template.") &&
    !templated.Contains("replaced"), "A named template did not merge the variant's values over its own:\n" + templated);
Expect(!all.Any(row => Text(row, "variant") == "wrong-sub" && Text(row, "profile") == "x64-v3"),
    "A variant restricted to one profile ran under another");
NoRejectedCertificates(all);
Expect(Directory.GetDirectories(Path.Combine(outputs, "builds")).Length == 4 &&
    Assembly(Row(all, "production")) == Assembly(Row(all, "baseline", "x64-v3")),
    "Production and baseline, with the same project and properties, did not share one build");
foreach (var (variant, profile, witness) in
    new[] { ("wrong-xor", "x64-v3", "WrongXor"), ("wrong-sub", "scalar", "WrongSub") })
{
    var generated = File.ReadAllText(Path.Combine(package, "Generated", "first", profile, variant, "Refutation.lean"));
    Expect(!generated.Contains('@') && !generated.Contains('\r') &&
        generated.Contains($"holds {witnesses[witness].Left} {witnesses[witness].Right} Memory.empty"),
        "A template was not instantiated with its witness: " + variant);
}

var proofChanged = Gates(0, "--changed", Path.Combine(package, "FirstSupport.lean"), "--profile", "scalar");
Expect(proofChanged.Length == 7 && proofChanged.All(row => Text(row, "gate") == "first"),
    "Proof closure selection included the unrelated second method");
var sourceChanged = Gates(0, "--changed", Path.Combine(second, "Second.cs"));
Expect(sourceChanged.Length == 3 && sourceChanged.All(row => Text(row, "theorem") == "Second.correctness"),
    "Method source selection did not follow the extracted method metadata");
var spareChanged = Execute([.. cli, "gates", manifest, "--changed", Path.Combine(second, "Spare.cs")]);
Expect(spareChanged.Code != 0 &&
    spareChanged.Output.Contains("No gates depend on the changed paths.", StringComparison.Ordinal),
    "A source no extracted method reaches selected its assembly's gates");
var templateChanged = Gates(0, "--changed", template, "--profile", "scalar");
Expect(templateChanged.Select(row => Text(row, "variant")).Order().SequenceEqual(["wrong-sub", "wrong-xor"]),
    "A changed template did not select exactly the variants instantiated from it");
var fixtureChanged = Gates(0, "--changed", Path.Combine(fixture, "First.cs"), "--profile", "scalar");
Expect(fixtureChanged.Length == 9 && fixtureChanged.All(row => Text(row, "gate") == "first"),
    "A changed fixture source did not select exactly the variants built from its project");
var filtered = Gates(0, "--method", "Second", "--profile", "scalar", "--check");
Expect(filtered.Length == 1 && Text(filtered[0], "status") == "checked" &&
    !File.Exists(Path.Combine(Text(filtered[0], "output")!, "verified.json")),
    "Catalog filters or compile-only results were incorrect");
// Results and --profile use a named profile's name, and extraction reads its file.
var named = Gates(0, "--method", "Second", "--profile", "plain", "--check");
var namedIdentity = JsonDocument.Parse(File.ReadAllText(Path.Combine(Text(named.Single(), "output")!, "identity.json")))
    .RootElement.EnumerateObject().Single(property => property.Name == "profile").Value;
Expect(Text(named.Single(), "profile") == "plain" && namedIdentity.EnumerateObject().Any(property =>
        property.Name.Equals("name", StringComparison.OrdinalIgnoreCase) && property.Value.GetString() == "plain-file"),
    "A named profile did not extract with its file", named.Single());
var json = Execute([.. cli, "gates", manifest, "--method", "Second", "--profile", "scalar", "--check",
    "--format", "json"]);
var document = JsonDocument.Parse(json.Stdout).RootElement;
Expect(json.Code == 0 && document.GetProperty("failed").GetInt32() == 0 &&
    document.GetProperty("variants").EnumerateArray().Single().GetProperty("status").GetString() == "checked",
    "The JSON report did not hold one document with the variant results:\n" + json.Output);
var checkRejected = Execute([.. cli, "gates", manifest, "--method", "First", "--profile", "scalar", "--check"]);
Expect(checkRejected.Code != 0 && checkRejected.Output.Contains("--check cannot evaluate", StringComparison.Ordinal),
    "--check accepted a rejection expectation");
// A plan of the catalog's gates runs one group per job, and the required results then pass.
var plan = Execute([.. cli, "gates", manifest, "--plan", "2", "--method", "Third", "--format", "json"]);
Expect(plan.Code == 0, "Planning the catalog's gates failed:\n" + plan.Output);
var planPath = Path.Combine(directory, "plan.json");
File.WriteAllText(planPath, plan.Stdout);
var jobs = Path.Combine(directory, "Jobs");
foreach (var job in new[] { "job-1", "job-2" })
{
    var run = Execute([.. cli, "gates", manifest, "--plan-group", planPath, job, "--results",
        Path.Combine(jobs, job, "results.json")]);
    Expect(run.Code == 0, "A planned group failed:\n" + run.Output);
}
var required = Execute([.. cli, "gates", manifest, "--require-results", jobs, "--plan", planPath]);
Expect(required.Code == 0 && required.Output.Contains("all 2 planned rows passed"),
    "The results of every planned group did not satisfy the plan:\n" + required.Output);
Console.WriteLine("PASS project builds, per-variant proofs and profiles, witness refutations, catalogs and selection");

Manifest(controls: true);
var controls = Gates(1, "--method", "First", "--profile", "scalar");
foreach (var variant in new[] { "production", "baseline", "reordered", "wrong-xor", "wrong-sub", "definitional",
    "templated", "witness-accepted", "unchanged-reordered" })
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
    row.GetProperty("refutation").GetProperty("status").GetString() == "verified" &&
    StatementStatus(row) == "different");
// The refutation and the rejection both hold, so only the statement comparison fails these rows.
Failed("unrelated-refutation", "A refutation of an unrelated statement counted as a rejection", row =>
    Text(row, "stage") == "statement identity" && StatementStatus(row) == "different" &&
    Text(row, "error")!.Contains("does not state the negation", StringComparison.Ordinal) &&
    row.GetProperty("statement").GetProperty("variant").GetString()!.StartsWith("Trivial.holds : True"));
Failed("weaker-statement", "A weaker own statement certified the variant", row =>
    Text(row, "stage") == "statement identity" && StatementStatus(row) == "different" &&
    !File.Exists(Path.Combine(Text(row, "output")!, "verified.json")));
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
        !File.Exists(Path.Combine(package, "Generated", "first", "scalar", variant, "Refutation.lean")));
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
void Invalid(string message, string expected)
{
    var result = Execute([.. cli, "gates", manifest]);
    Expect(result.Code != 0 && result.Output.Contains(expected, StringComparison.Ordinal),
        message + ":\n" + result.Output);
}
Manifest(false, new { name = "loop-a", build = Build("Baseline"), expect = "unchanged", program = "same",
    programOf = "loop-b" }, new { name = "loop-b", build = Build("Baseline"), expect = "unchanged", program = "same",
    programOf = "loop-a" });
Invalid("A programOf cycle was accepted", "through a cycle: loop-a");
Manifest(false);
void Edit(string from, string to) => File.WriteAllText(manifest, File.ReadAllText(manifest).Replace(from, to));
Edit("\"programOf\":\"reordered\"", "\"programOf\":\"absent\"");
Invalid("An unknown programOf variant was accepted", "unknown variant or through a cycle: absent");
Manifest(false);
Edit("\"plain\":\"@plain.json\"", "\"scalar\":\"@plain.json\"");
Invalid("A named profile shadowed a built-in profile", "Profile scalar has the name of a built-in profile.");
Console.WriteLine("PASS build, extraction, program, template, proof and internal failures never count as rejections");
