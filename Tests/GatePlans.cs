#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;
using System.Text.Json.Nodes;

// Two listed gates and a catalog of four. Every method is absent from the assembly, so a run fails each row
// at extraction and no check here needs Lean.
var root = At("artifacts/GatePlans-" + Guid.NewGuid().ToString("N"));
var proofs = Path.Combine(root, "Proofs");
Directory.CreateDirectory(proofs);
File.WriteAllText(Path.Combine(proofs, "FirstSupport.lean"), "theorem First.support : True := trivial\n");
File.WriteAllText(Path.Combine(proofs, "First.lean"), "import FirstSupport\ntheorem First.correctness : True := " +
    "First.support\n");
File.WriteAllText(Path.Combine(proofs, "Second.lean"), "theorem Second.correctness : True := trivial\n");
File.WriteAllText(Path.Combine(proofs, "Binding.lean.in"),
    "import Extracted\ntheorem Binding.@op@@file@ : True := trivial\n");
File.WriteAllText(Path.Combine(proofs, "Catalog.json"), """
    { "schema": 1, "generatedRoot": "Bindings", "families": [ {
      "template": "Binding.lean.in",
      "dimensions": [ [ { "op": "Add" }, { "op": "Sub" } ],
        [ { "profile": "scalar", "file": "Scalar" }, { "profile": "x64-v3", "file": "Vector" } ] ],
      "gate": { "name": "@op@-@profile@", "method": "Missing::@op@(ulong,ulong)", "profiles": [ "@profile@" ],
                "proof": "@op@@file@.lean", "theorem": "Binding.@op@@file@" } } ] }
    """);
var manifest = Path.Combine(root, "gates.json");
var assembly = Path.GetRelativePath(root, At("Examples/Assembly/bin/Examples.dll")).Replace('\\', '/');
JsonObject Manifest() => JsonNode.Parse($$"""
    { "schema": 1, "proofRoot": "Proofs", "outputRoot": "Outputs",
      "defaults": { "assembly": {{JsonSerializer.Serialize(assembly)}} },
      "selection": { "all": [ "Shared" ], "ignore": [ "Notes" ] },
      "catalogs": [ "Proofs/Catalog.json" ],
      "gates": [
        { "name": "first", "method": "Missing::First(ulong,ulong)", "profiles": [ "scalar", "x64-v3" ],
          "proof": "First.lean", "theorem": "First.correctness",
          "variants": [ { "name": "again", "assembly": {{JsonSerializer.Serialize(assembly)}},
                          "profiles": [ "scalar" ], "expect": "certifies" } ] },
        { "name": "second", "method": "Missing::Second(ulong,ulong)", "profiles": [ "scalar" ],
          "proof": "Second.lean", "theorem": "Second.correctness" } ] }
    """)!.AsObject();
void Write(JsonObject document) => File.WriteAllText(manifest, document.ToJsonString());
(int Code, string Output, string Stdout) Gates(params string[] options)
{
    var result = Execute(["dotnet", ExtractorPath, "gates", manifest, .. options]);
    return (result.Code, result.Output, result.Stdout);
}
void Expect(bool holds, string message)
{
    if (!holds) throw new InvalidOperationException(message);
}
void Fails((int Code, string Output, string Stdout) result, string expected, string message) =>
    Expect(result.Code != 0 && result.Output.Contains(expected, StringComparison.Ordinal),
        message + ":\n" + result.Output);
JsonObject Plan(params string[] options)
{
    var result = Gates(["--format", "json", .. options]);
    Expect(result.Code == 0, "Planning failed:\n" + result.Output);
    return JsonNode.Parse(result.Stdout)!.AsObject();
}
string[] Strings(JsonNode? array) => [.. array!.AsArray().Select(node => node!.GetValue<string>())];
(string Id, string[] Rows, double Cost)[] Groups(JsonObject plan) => [.. plan["groups"]!.AsArray()
    .Select(group => (group!["id"]!.GetValue<string>(), Strings(group["rows"]), group["cost"]!.GetValue<double>()))];
string[] all = ["first/scalar/production", "first/x64-v3/production", "first/scalar/again",
    "second/scalar/production", "Add-scalar/scalar/production", "Add-x64-v3/x64-v3/production",
    "Sub-scalar/scalar/production", "Sub-x64-v3/x64-v3/production"];

Write(Manifest());
var bindings = Path.Combine(proofs, "Bindings");
Expect(!Directory.Exists(bindings), "Generated sources existed before the first run");
var counted = Plan("--plan", "3");
Expect(Directory.GetFiles(bindings, "*.lean").Length == 4, "Planning did not generate the catalog's sources first");
Expect(Strings(counted["selected"]).SequenceEqual(all), "The plan did not select every row in manifest order");
Expect(Groups(counted).Select(group => group.Cost).SequenceEqual([3.0, 2.0, 2.0]) &&
    Groups(counted).Select(group => group.Id).SequenceEqual(["job-1", "job-2", "job-3"]),
    "Without costs, each gate and profile did not count once: " + counted.ToJsonString());
Expect(Groups(counted).Any(group => group.Rows.Contains("first/scalar/production") &&
    group.Rows.Contains("first/scalar/again")), "A variant was planned apart from its production row");
Expect(Gates("--plan", "3", "--format", "json").Stdout == Gates("--plan", "3", "--format", "json").Stdout,
    "The same inputs gave a different plan");

// Recorded seconds: a gate without a record takes its method's median, then the median of all records.
var costs = Path.Combine(root, "costs.json");
File.WriteAllText(costs, """
    { "manifest": "earlier", "revision": null, "rows": [
      { "id": "first/scalar/production", "elapsedSeconds": 10 }, { "id": "first/scalar/again", "elapsedSeconds": 30 },
      { "id": "Add-scalar/scalar/production", "elapsedSeconds": 8 },
      { "id": "second/scalar/production", "elapsedSeconds": 4 } ] }
    """);
var priced = Groups(Plan("--plan", "3", "--costs", costs));
Expect(priced.Select(group => group.Cost).SequenceEqual([40.0, 40.0, 36.0]) &&
    priced[0].Rows.SequenceEqual(["first/scalar/production", "first/scalar/again"]) &&
    priced[1].Rows.SequenceEqual(["first/x64-v3/production"]),
    "Recorded costs were not balanced largest first: " + string.Join("; ", priced.Select(group =>
        $"{group.Id} {group.Cost} {string.Join(' ', group.Rows)}")));
var mean = priced.Average(group => group.Cost);
Expect(priced.Max(group => group.Cost) <= mean + 40, "The largest group exceeds the mean by more than one unit");
Expect(Groups(Plan("--plan", "1", "--costs", costs, "--only", "Add-x64-v3"))[0].Cost == 8 &&
    Groups(Plan("--plan", "1", "--costs", costs, "--only", "Sub-scalar"))[0].Cost == 8,
    "A gate without a record did not take its method's median, or the median of all records");
Expect(Groups(Plan("--plan", "8", "--costs", costs)).Length == 7, "A plan had an empty group");
Console.WriteLine("PASS deterministic plans balanced by recorded cost, with variants kept with production");

Expect(Strings(Plan("--plan", "2", "--only", "first/scalar")["selected"])
    .SequenceEqual(["first/scalar/production", "first/scalar/again"]), "--only did not select by id prefix");
Fails(Gates("--plan", "2", "--only", "fir"), "--only fir names no row", "An --only prefix of no id was accepted");
Expect(Strings(Plan("--plan", "2", "--changed", Path.Combine(proofs, "Binding.lean.in"))["selected"])
    .SequenceEqual(all[4..]), "A changed catalog template did not select exactly its gates");
Expect(Strings(Plan("--plan", "2", "--changed", Path.Combine(proofs, "Catalog.json"))["selected"])
    .SequenceEqual(all[4..]), "A changed catalog did not select exactly its gates");
Expect(Strings(Plan("--plan", "2", "--changed", Path.Combine(proofs, "FirstSupport.lean"))["selected"])
    .SequenceEqual(all[..3]), "A changed proof import did not select exactly the gates that import it");
var ignored = Plan("--plan", "2", "--changed", Path.Combine(root, "Notes", "Plan.md"));
Expect(Strings(ignored["selected"]).Length == 0 && Groups(ignored).Length == 0,
    "An ignored path selected rows, or an empty selection did not plan zero groups");
Fails(Gates("--changed", Path.Combine(root, "Notes", "Plan.md")), "No gates depend on the changed paths.",
    "A run with nothing selected passed");
Expect(Strings(Plan("--plan", "2", "--changed", Path.Combine(root, "Shared", "Source.cs"))["selected"])
    .SequenceEqual(all), "A path under an all prefix did not select every row");
Console.WriteLine("PASS --only, changed catalogs, proofs, ignored and all-selecting paths");

void Invalid(string expected, string message, Action<JsonObject> edit)
{
    var document = Manifest();
    edit(document);
    Write(document);
    Fails(Gates("--plan", "1"), expected, message);
}
JsonObject Gate(string name, string method) => JsonNode.Parse($$"""
    { "name": "{{name}}", "method": "{{method}}", "profiles": [ "scalar" ], "proof": "Second.lean",
      "theorem": "Second.correctness" }
    """)!.AsObject();
Invalid("overlaps between all and ignore", "Overlapping selection prefixes were accepted", document =>
    document["selection"]!["ignore"]!.AsArray().Add("Shared/Generated"));
Invalid("also generates", "A listed gate for a generated method was accepted", document =>
    document["gates"]!.AsArray().Add(Gate("extra", "Missing::Add(ulong,ulong)")));
Invalid("Invalid or duplicate gate entry Add-scalar", "A listed gate with a generated gate's name was accepted",
    document => document["gates"]!.AsArray().Add(Gate("Add-scalar", "Missing::Other(ulong,ulong)")));
Invalid("overlaps that of", "Overlapping generated roots were accepted", document =>
    document["generatedRoot"] = "Bindings/Variants");
Invalid("or takes it from defaults", "A gate without an assembly or defaults was accepted", document =>
    document.Remove("defaults"));
Write(Manifest());
Console.WriteLine("PASS manifest errors for selection prefixes, catalog collisions and defaults");

// Each group runs from the saved plan; its results carry the manifest digest and the revision.
var planPath = Path.Combine(root, "plan.json");
var saved = Plan("--plan", "2");
File.WriteAllText(planPath, saved.ToJsonString());
var stale = Path.Combine(root, "Outputs", "first", ContentKey("scalar")[..12], "production");
Directory.CreateDirectory(stale);
File.WriteAllText(Path.Combine(stale, "verified.json"), "{}");
File.WriteAllText(Path.Combine(stale, "failed.json"), "{}");
var results = Path.Combine(root, "Results");
foreach (var (id, _, _) in Groups(saved))
{
    var run = Gates("--plan-group", planPath, id, "--results", Path.Combine(results, id, "results.json"));
    Expect(run.Code == 1 && run.Output.Contains("(stage: extraction)"),
        "A group did not run its rows to their extraction failures:\n" + run.Output);
}
Expect(!File.Exists(Path.Combine(stale, "verified.json")) && !File.Exists(Path.Combine(stale, "failed.json")),
    "A row that failed extraction kept an earlier certificate or failure report");
var first = JsonNode.Parse(File.ReadAllText(Path.Combine(results, "job-1", "results.json")))!.AsObject();
Expect(first["manifest"]!.GetValue<string>() == saved["manifest"]!.GetValue<string>() &&
    first["revision"]?.GetValue<string>() == saved["revision"]?.GetValue<string>() &&
    first["rows"]!.AsArray().Select(row => row!["id"]!.GetValue<string>())
        .SequenceEqual(Strings(saved["groups"]![0]!["rows"])),
    "A group's results did not carry the plan's digest, revision and rows");

(int Code, string Output, string Stdout) Require() => Gates("--require-results", results, "--plan", planPath);
var failing = Require();
Expect(failing.Code == 1 && all.All(id => failing.Output.Contains($"FAILED {id} (status: failed, stage: extraction)")),
    "Failed rows were not reported by id:\n" + failing.Output);
foreach (var file in Directory.GetFiles(results, "*.json", SearchOption.AllDirectories))
{
    var document = JsonNode.Parse(File.ReadAllText(file))!.AsObject();
    foreach (var row in document["rows"]!.AsArray()) row!["status"] = "verified";
    File.WriteAllText(file, document.ToJsonString());
}
Expect(Require().Code == 0, "Every planned row passing did not satisfy the plan:\n" + Require().Output);
var second = Path.Combine(results, "job-2", "results.json");
var secondText = File.ReadAllText(second);
File.Delete(second);
var missing = Require();
Expect(missing.Code == 1 && Strings(saved["groups"]![1]!["rows"]).All(id => missing.Output.Contains("MISSING " + id)),
    "Missing results were not reported by id:\n" + missing.Output);
File.WriteAllText(second, secondText);
var copy = Path.Combine(results, "copy", "results.json");
Directory.CreateDirectory(Path.GetDirectoryName(copy)!);
File.WriteAllText(copy, secondText);
Fails(Require(), "DUPLICATE " + Strings(saved["groups"]![1]!["rows"])[0], "A duplicated result was accepted");
var foreign = JsonNode.Parse(secondText)!.AsObject();
foreign["revision"] = "another";
File.WriteAllText(copy, foreign.ToJsonString());
Fails(Require(), "FOREIGN " + Strings(saved["groups"]![1]!["rows"])[0], "A result of another revision was accepted");
File.WriteAllText(copy, "{ \"schema\": 1 }");
Fails(Require(), "Not a gates results file", "A file that is not a results file was accepted");
File.Delete(copy);
Expect(Require().Code == 0, "Restored results did not satisfy the plan");
var emptyPlan = Path.Combine(root, "empty.json");
File.WriteAllText(emptyPlan, ignored.ToJsonString());
Expect(Gates("--require-results", Path.Combine(root, "None"), "--plan", emptyPlan).Code == 0,
    "A plan with no rows did not pass");
Write(Manifest().Also(document => document["gates"]![1]!["theorem"] = "Second.other"));
Fails(Gates("--plan-group", planPath, "job-1"), "The plan was made for manifest",
    "A plan of another manifest ran");
Fails(Require(), "The plan was made for manifest", "Results were checked against a plan of another manifest");
Console.WriteLine("PASS plan groups, results headers, stale certificates and required results");
Directory.Delete(root, recursive: true);

static class JsonObjectExtensions
{
    /// <summary>`document` after `edit` changes it.</summary>
    internal static JsonObject Also(this JsonObject document, Action<JsonObject> edit)
    {
        edit(document);
        return document;
    }
}
