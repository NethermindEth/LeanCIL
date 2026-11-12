#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json.Nodes;

// A catalog of three dimensions with an exclude, an explicit row, assigns and a handwritten entry. The
// template has CRLF endings, which generated sources must not keep.
var root = At("artifacts/ProofBindingCatalog-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(Path.Combine(root, "templates"));
File.WriteAllText(Path.Combine(root, "templates", "Binding.lean.in"),
    "-- @op@ at width @width@ under @family@\r\nimport Extracted\r\n" +
    "theorem Binding.@op@@width@ : 1 @symbol@ 0 = 1 @symbol@ 0 := by\r\n@tactic@\r\n");
var catalog = Path.Combine(root, "catalog.json");
var generated = Path.Combine(root, "proofs", "Bindings");
const string Baseline = """
    { "schema": 1, "generatedRoot": "proofs/Bindings", "families": [ {
      "template": "templates/Binding.lean.in",
      "dimensions": [
        [ { "op": "Add", "symbol": "+" }, { "op": "Sub", "symbol": "-" } ],
        [ { "width": "32" }, { "width": "64" } ],
        [ { "family": "scalar", "profile": "scalar" }, { "family": "vector", "profile": "x64-v3" } ] ],
      "exclude": [ { "op": "Sub", "width": "32" } ],
      "rows": [ { "op": "Mul", "symbol": "*", "width": "8", "family": "scalar", "profile": "scalar" } ],
      "assign": [ { "match": { "family": "scalar" }, "set": { "tactic": "  decide" } },
                  { "match": { "family": "vector" }, "set": { "tactic": "  rfl" } } ],
      "gate": { "name": "@op@@width@-@family@", "method": "Ops::@op@@width@", "profiles": [ "@profile@" ],
                "proof": "@op@@width@@family@.lean", "theorem": "Binding.@op@@width@" },
      "handwritten": [ { "op": "Add", "width": "64", "family": "scalar", "proof": "proofs/AddScalar.lean",
                         "theorem": "Hand.add" } ] } ] }
    """;
(int Code, string Output) Bindings(params string[] options)
{
    var result = Execute(["dotnet", ExtractorPath, "bindings", catalog, .. options]);
    return (result.Code, result.Output);
}
void Expect(bool holds, string message)
{
    if (!holds) throw new InvalidOperationException(message);
}
void Fails((int Code, string Output) result, string expected, string message) =>
    Expect(result.Code != 0 && result.Output.Contains(expected, StringComparison.Ordinal),
        message + ":\n" + result.Output);
string[] Sources() => [.. Directory.EnumerateFiles(generated, "*.lean", SearchOption.AllDirectories)
    .Select(Path.GetFileName).Order(StringComparer.Ordinal)!];
try
{
    File.WriteAllText(catalog, Baseline);
    Fails(Bindings("--check"), "Generated source missing", "Check mode accepted missing sources");
    Expect(!Directory.Exists(generated), "Check mode created the generated root");
    var written = Bindings();
    Expect(written.Code == 0 && written.Output.Contains("wrote 6 of 6 generated sources for 7 gates"),
        "The catalog did not write six sources for seven gates:\n" + written.Output);
    Expect(Sources().SequenceEqual(["Add32scalar.lean", "Add32vector.lean", "Add64vector.lean",
        "Mul8scalar.lean", "Sub64scalar.lean", "Sub64vector.lean"]),
        "Excluded, handwritten or explicit rows generated the wrong sources: " + string.Join(", ", Sources()));
    var bytes = File.ReadAllBytes(Path.Combine(generated, "Sub64vector.lean"));
    Expect(bytes.AsSpan().SequenceEqual("-- Sub at width 64 under vector\nimport Extracted\n"u8.ToArray()
        .Concat("theorem Binding.Sub64 : 1 - 0 = 1 - 0 := by\n  rfl\n"u8.ToArray()).ToArray()),
        "A generated source is not the exact substituted text with LF endings and no BOM");
    Expect(Bindings("--check").Code == 0, "Check mode rejected the sources the catalog wrote");
    var before = Sources().ToDictionary(name => name, name => File.ReadAllBytes(Path.Combine(generated, name)));
    Expect(Bindings().Output.Contains("wrote 0 of 6"), "Writing unchanged sources rewrote them");

    var edited = Path.Combine(generated, "Add32scalar.lean");
    File.WriteAllText(edited, "-- edited\n");
    Fails(Bindings("--check"), "Generated source differs", "Check mode accepted an edited source");
    Expect(File.ReadAllText(edited) == "-- edited\n", "Check mode repaired an edited source");
    Bindings();
    Expect(File.ReadAllBytes(edited).AsSpan().SequenceEqual(before["Add32scalar.lean"]),
        "Writing did not restore an edited source");
    var stray = Path.Combine(generated, "Nested", "Stray.lean");
    Directory.CreateDirectory(Path.GetDirectoryName(stray)!);
    File.WriteAllText(stray, "-- stray\n");
    Fails(Bindings("--check"), "No catalog row produces", "Check mode accepted a source no row produces");
    var warned = Bindings();
    Expect(warned.Code == 0 && warned.Output.Contains("WARNING No catalog row produces") && File.Exists(stray),
        "Writing did not warn about a stray source, or deleted it:\n" + warned.Output);
    File.Delete(stray);
    Console.WriteLine("PASS catalog rows, exact LF sources, check mode without writes, edits and strays");

    void Invalid(string expected, string message, Action<JsonObject> edit)
    {
        var document = JsonNode.Parse(Baseline)!.AsObject();
        edit(document["families"]![0]!.AsObject());
        File.WriteAllText(catalog, document.ToJsonString());
        Fails(Bindings("--check"), expected, message);
    }
    JsonObject Variables(string json) => JsonNode.Parse(json)!.AsObject();
    Invalid("yields gate Add32-scalar twice", "A duplicated gate was accepted", family =>
        family["rows"]!.AsArray().Add(Variables(
            """{ "op": "Add", "symbol": "+", "width": "32", "family": "scalar", "profile": "scalar" }""")));
    Invalid("is given by two dimensions", "A variable of two dimensions was accepted", family =>
        family["dimensions"]![2]![0]!.AsObject().Add("width", "16"));
    Invalid("variable spare of row", "A variable no placeholder uses was accepted", family =>
        family["rows"]![0]!.AsObject().Add("spare", "1"));
    Invalid("cannot fill the template: Template placeholders without a value: tactic",
        "A row without a template value was accepted", family => family["assign"]!.AsArray().RemoveAt(1));
    Invalid("variable tactic of row", "A variable set twice was accepted", family =>
        family["rows"]![0]!.AsObject().Add("tactic", "  omega"));
    Invalid("matches no row of the product", "An exclude that matches nothing was accepted", family =>
        family["exclude"]![0]!["width"] = "16");
    Invalid("rows generate different sources at Add32.lean", "Different sources at one path were accepted",
        family => family["gate"]!["proof"] = "@op@@width@.lean");
    Invalid("Expected a relative Lean source path", "A generated path outside generatedRoot was accepted",
        family => family["gate"]!["proof"] = "../@op@@width@@family@.lean");
    Invalid("outside generatedRoot", "A handwritten proof inside generatedRoot was accepted", family =>
        family["handwritten"]![0]!["proof"] = "proofs/Bindings/Hand.lean");
    Invalid("two handwritten entries match row", "Two handwritten entries for one row were accepted", family =>
        family["handwritten"]!.AsArray().Add(Variables(
            """{ "op": "Add", "width": "64", "proof": "proofs/Other.lean", "theorem": "Hand.other" }""")));
    Invalid("Invalid binding catalog", "An unknown catalog key was accepted", family => family.Add("extra", 1));

    Console.WriteLine("PASS catalog rejects duplicate gates, unused or missing variables, conflicts and unsafe paths");
}
finally
{
    if (Directory.Exists(root)) Directory.Delete(root, recursive: true);
}
