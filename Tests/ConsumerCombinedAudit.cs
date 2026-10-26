#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Diagnostics;
using System.Text.Json;

var cli = new[] { "dotnet", args.FirstOrDefault(argument => !argument.StartsWith("--")) ?? ExtractorPath };
var checkHiddenDependency = !args.Contains("--without-hidden", StringComparer.Ordinal);
var profileReplay = args.Contains("--profile", StringComparer.Ordinal);
var directory = At("artifacts/ConsumerCombinedAudit-" + Guid.NewGuid().ToString("N"));
var root = Path.Combine(directory, "Package");
Directory.CreateDirectory(root);
var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
File.WriteAllText(Path.Combine(root, "lakefile.toml"),
    "name = \"consumer\"\n[[require]]\nname = \"leancil\"\ngit = " +
    JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) + "\n");
File.Copy(At("lean-toolchain"), Path.Combine(root, "lean-toolchain"));
Run(["lake", "update"], root);
// Exercise the current verifier sources even before the working changes are committed.
var framework = Path.Combine(root, ".lake/packages/leancil");
CopyTree(At("CIL"), Path.Combine(framework, "CIL"));
File.Copy(At("CIL.lean"), Path.Combine(framework, "CIL.lean"), true);
File.Copy(At("lean-toolchain"), Path.Combine(framework, "lean-toolchain"), true);
var extracted = Path.Combine(directory, "Extracted");
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "Arithmetic::Add(ulong,ulong)", extracted]);
var requests = new List<object>();
var outputs = new List<string>();
void Add(string name, string theorem, bool axiomatic = false, bool hidden = false)
{
    var proof = Path.Combine(root, name + ".lean");
    var source = "import Extracted\nnamespace " + name + "\n" +
        (axiomatic ? "axiom assume : True\n" : "") +
        "theorem correctness : True := " + (axiomatic ? "assume" : "True.intro") + "\n" +
        "#print axioms correctness\nend " + name + "\n";
    File.WriteAllText(proof, hidden ? """
        import Lean
        import Extracted
        set_option debug.skipKernelTC true
        run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
          name := `Hidden.correctness
          levelParams := []
          type := Lean.mkConst ``True
          value := Lean.mkConst `Unapproved.correctness
        })
        """ : source);
    var output = Path.Combine(directory, name);
    CopyTree(extracted, output);
    File.WriteAllText(Path.Combine(output, "verified.json"), "{}");
    outputs.Add(output);
    requests.Add(new { output, proof, theorem });
}

for (var index = 0; index < 8; index++) Add("Correct" + index, "Correct" + index + ".correctness");
// The requested theorem exists in a different proof but is absent from this proof's imports.
Add("Missing", "Correct0.correctness");
Add("Unapproved", "Unapproved.correctness", axiomatic: true);
if (checkHiddenDependency) Add("Hidden", "Hidden.correctness", hidden: true);
var manifest = Path.Combine(directory, "batch.json");
var results = Path.Combine(directory, "results.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new { schema = 1, proofRoot = root, requests }));
var savedCache = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
var savedTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
var savedProfile = Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY");
var trace = Path.Combine(directory, "Trace");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", profileReplay ? "true" : null);
    var timer = Stopwatch.StartNew();
    var run = Execute([.. cli, "verify-batch", manifest, "--results", results]);
    timer.Stop();
    var outcomes = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(results))!;
    if (run.Code != 1 || outcomes.Length != requests.Count ||
        outcomes.Take(8).Any(item => item.GetProperty("status").GetString() != "verified") ||
        outcomes.Skip(8).Any(item => item.GetProperty("status").GetString() != "failed") ||
        outputs.Take(8).Any(output => !File.Exists(Path.Combine(output, "verified.json"))) ||
        outputs.Skip(8).Any(output => File.Exists(Path.Combine(output, "verified.json"))) ||
        !run.Output.Contains("Expected a theorem") || !run.Output.Contains("Unapproved proof axioms") ||
        (checkHiddenDependency && !run.Output.Contains(profileReplay ? "while replaying declaration" :
            "Theorem dependency is outside its request's import closure")))
        throw new InvalidOperationException("Combined audit lost request-local results: " + run.Output);
    for (var index = 0; index < 8; index++)
    {
        var report = JsonSerializer.Deserialize<JsonElement>(
            File.ReadAllText(Path.Combine(outputs[index], "verified.json")));
        if (report.GetProperty("theorem").GetString() != "Correct" + index + ".correctness")
            throw new InvalidOperationException("Combined theorem results were attributed to another request.");
    }
    File.WriteAllText(Path.Combine(directory, "seconds.json"),
        JsonSerializer.Serialize(new { seconds = timer.Elapsed.TotalSeconds, trace }));
    Console.WriteLine($"PASS combined audit: eight verified, {requests.Count - 8} request-local failures rejected " +
        $"({timer.Elapsed.TotalSeconds:F2}s); {directory}");
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", savedCache);
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", savedTrace);
    Environment.SetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY", savedProfile);
}
