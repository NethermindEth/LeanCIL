#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

var cli = new[] { "dotnet", ExtractorPath };
var directory = At("artifacts/ProofGates-" + Guid.NewGuid().ToString("N"));
var package = Path.Combine(directory, "Package");
Directory.CreateDirectory(package);
string Assembly(string variant, string first)
{
    var source = Path.Combine(directory, variant);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Gates.csproj"), """
        <Project Sdk="Microsoft.NET.Sdk">
          <PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
        </Project>
        """);
    File.WriteAllText(Path.Combine(source, "First.cs"),
        "public static partial class Methods { public static ulong First(ulong x, ulong y) => " + first + "; }");
    File.WriteAllText(Path.Combine(source, "Second.cs"),
        "public static partial class Methods { public static ulong Second(ulong x, ulong y) => unchecked(x - y); }");
    Run(["dotnet", "build", source, "-c", "Release", "-o", Path.Combine(source, "output")]);
    return Path.Combine(source, "output/Gates.dll");
}
var assembly = Assembly("Production", "unchecked(x + y)");
var equivalent = Assembly("Equivalent", "unchecked(y + x)");
var broken = Assembly("Broken", "x ^ y");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"gates-fixture\"\n[[require]]\nname = \"leancil\"\ngit = " +
    JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " +
    JsonSerializer.Serialize(Run(["git", "rev-parse", "HEAD"]).Trim()) +
    "\n[[lean_lib]]\nname = \"FirstSupport\"\n[[lean_lib]]\nname = \"SecondSupport\"\n");
Run(["lake", "update"], package);
foreach (var (name, operation) in new[] { ("First", "+"), ("Second", "-") })
{
    File.WriteAllText(Path.Combine(package, name + "Support.lean"),
        $"theorem {name}.support : True := True.intro\n#print axioms {name}.support\n");
    File.WriteAllText(Path.Combine(package, name + ".lean"), $$"""
        import Extracted
        import CIL.Safety.SymbolicExecution
        import {{name}}Support
        open CIL.Safety
        /-- The extracted method computes wrapping arithmetic in arbitrary caller memory. -/
        theorem {{name}}.correctness (left right : CIL.W64) (memory : Memory) :
            ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 left), .scalar (.i64 right)]
              memory = .ok (memory, [.scalar (.i64 (left {{operation}} right))]) := by
          cil_checked_steps []
          all_goals simp only [BitVec.add_comm]
        #print axioms {{name}}.correctness
        """ + "\n");
}
var manifest = Path.Combine(directory, "gates.json");
var results = Path.Combine(directory, "results.json");
void Manifest(bool falseRejection = false)
{
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        schema = 1, proofRoot = "Package", outputRoot = "Outputs", gates = new object[]
        {
            new { name = "first", assembly, method = "Methods::First(ulong,ulong)",
                profiles = new[] { "scalar", "x64-v3" }, proof = "First.lean", theorem = "First.correctness",
                variants = new[]
                {
                    new { name = "equivalent", assembly = equivalent,
                        expect = falseRejection ? "rejected" : "certifies" },
                    new { name = "broken", assembly = broken, expect = "rejected" }
                } },
            new { name = "second", assembly, method = "Methods::Second(ulong,ulong)",
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
void NoRejectedCertificates(IEnumerable<JsonElement> rows)
{
    foreach (var row in rows.Where(row => row.GetProperty("expect").GetString() == "rejected"))
        if (File.Exists(Path.Combine(row.GetProperty("output").GetString()!, "verified.json")))
            throw new Exception("A rejection expectation retained a certificate.");
}
Manifest();
var all = Gates(0);
if (all.Length != 8 || all.Count(row => row.GetProperty("status").GetString() == "rejected") != 2)
    throw new Exception("Expected two methods, two profiles and both variants from one manifest.");
NoRejectedCertificates(all);
var changed = Gates(0, "--changed", Path.Combine(package, "FirstSupport.lean"));
if (changed.Length != 6 || changed.Any(row => row.GetProperty("theorem").GetString() != "First.correctness"))
    throw new Exception("Proof closure selection included the unrelated second method.");
var sourceChanged = Gates(0, "--changed", Path.Combine(directory, "Production/Second.cs"));
if (sourceChanged.Length != 2 || sourceChanged.Any(row =>
    row.GetProperty("theorem").GetString() != "Second.correctness"))
    throw new Exception("Method source selection did not follow the extracted method metadata.");
var filtered = Gates(0, "--method", "Second", "--profile", "scalar", "--check");
if (filtered.Length != 1 || filtered[0].GetProperty("status").GetString() != "checked" ||
    File.Exists(Path.Combine(filtered[0].GetProperty("output").GetString()!, "verified.json")))
    throw new Exception("Catalog filters or compile-only results were incorrect.");
Manifest(falseRejection: true);
var unexpectedSuccess = Gates(1, "--method", "First", "--profile", "scalar");
if (unexpectedSuccess.Count(row => row.GetProperty("status").GetString() == "failed") != 1)
    throw new Exception("A certifying variant was accepted as a rejection.");
NoRejectedCertificates(unexpectedSuccess);
Console.WriteLine("PASS manifest extraction, profiles, proof/source selection and mutation expectations");
