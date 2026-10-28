using System.Diagnostics;
using System.Text.Json;

partial class Program
{
    // Fixed sources let independent rejection checks share one authenticated base.
    // Mutable-source, environment and receipt tests remain separate processes.
    static void CheckConsumerBatchOutcomes(string[] cli, string root, string proof,
        string batchA, string batchB, string batchC, string alternate, bool separate = false)
    {
        var forged = Path.Combine(root, "Client", "Forged.lean");
        var forgedProof = Path.Combine(root, "ProofForged.lean");
        var axiomatic = Path.Combine(root, "Client", "Axiomatic.lean");
        var axiomProof = Path.Combine(root, "ProofAxiom.lean");
        var missingProof = Path.Combine(root, "ProofMissingSibling.lean");
        var hiddenProof = Path.Combine(root, "ProofHiddenSibling.lean");
        var directory = Path.Combine(Path.GetDirectoryName(batchB)!, "OutcomeChecks-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        var trace = ConsumerTraceDirectory.Create(directory, "Trace");
        var savedTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
        var savedCache = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
        try
        {
            File.WriteAllText(forged, """
                import Lean
                set_option debug.skipKernelTC true
                run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
                  name := `Client.Batch.forged
                  levelParams := []
                  type := Lean.mkConst ``False
                  value := Lean.mkConst ``True.intro
                })
                """);
            File.WriteAllText(forgedProof, "import Client.Forged\n" + File.ReadAllText(proof));
            File.WriteAllText(axiomatic, """
                import Extracted
                import CIL.Semantics
                namespace Client.Axiomatic
                axiom hidden : False
                axiom execution (x y : CIL.W64) (memory : CIL.Memory) :
                    CIL.invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
                      some (memory, [.i64 (x + y)])
                end Client.Axiomatic
                """);
            File.WriteAllText(axiomProof, File.ReadAllText(proof)
                .Replace("import Client.Shared", "import Client.Axiomatic")
                .Replace("Client.execution", "Client.Axiomatic.execution"));
            File.WriteAllText(missingProof,
                "import Extracted\ntheorem MissingSibling.other : True := True.intro\n");
            File.WriteAllText(hiddenProof, """
                import Lean
                import Extracted
                set_option debug.skipKernelTC true
                run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
                  name := `HiddenSibling.false
                  levelParams := []
                  type := Lean.mkConst ``False
                  value := Lean.mkConst `Client.Axiomatic.hidden
                })
                """);
            var axiomOutput = Path.Combine(Path.GetDirectoryName(batchB)!, "Axiom-" + Guid.NewGuid().ToString("N"));
            var forgedOutput = Path.Combine(Path.GetDirectoryName(batchB)!, "Forged-" + Guid.NewGuid().ToString("N"));
            var missingOutput = Path.Combine(Path.GetDirectoryName(batchB)!,
                "MissingSibling-" + Guid.NewGuid().ToString("N"));
            var hiddenOutput = Path.Combine(Path.GetDirectoryName(batchB)!,
                "HiddenSibling-" + Guid.NewGuid().ToString("N"));
            foreach (var output in new[] { axiomOutput, forgedOutput, missingOutput, hiddenOutput })
                CopyTree(batchB, output);
            foreach (var output in new[] { axiomOutput, forgedOutput, missingOutput, hiddenOutput, batchC })
                File.WriteAllText(Path.Combine(output, "verified.json"), "{}");
            object Request(string output, string selectedProof, string theorem = "ExampleProof.correctness",
                string expect = "verified") => new { output, proof = selectedProof, theorem, expect };
            object[] requests =
            [
                Request(axiomOutput, axiomProof), Request(forgedOutput, forgedProof),
                Request(batchA, proof, expect: "rejected"), Request(batchA, proof),
                Request(batchB, forgedProof), Request(batchB, proof),
                Request(batchB, alternate, "AlternateProof.correctness"), Request(batchC, proof),
                Request(batchC, proof, expect: "rejected"),
                Request(missingOutput, missingProof, "AlternateProof.correctness"),
                Request(hiddenOutput, hiddenProof, "HiddenSibling.false")
            ];
            Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
            Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
            var timer = Stopwatch.StartNew();
            var statuses = new List<string>();
            var diagnostics = new List<string>();
            // The comparison isolates the first two checks while preserving all batch outcomes.
            var groups = separate ? new[] { requests[..1], requests[1..2], requests[2..] } : [requests];
            foreach (var group in groups)
            {
                var manifest = Path.Combine(directory, "batch.json");
                var results = Path.Combine(directory, "results.json");
                File.WriteAllText(manifest,
                    JsonSerializer.Serialize(new { schema = 1, proofRoot = root, requests = group }));
                var result = Execute([.. cli, "verify-batch", manifest, "--results", results]);
                if (result.Code != 1)
                    throw new InvalidOperationException("Expected mixed batch failure: " + result.Output);
                diagnostics.Add(result.Output);
                statuses.AddRange(JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(results))!
                    .Select(item => item.GetProperty("status").GetString() + "/" +
                        item.GetProperty("stage").GetString()));
            }
            timer.Stop();
            string[] expected = ["failed/theorem audit", "failed/kernel replay", "failed/proof checking",
                "verified/extraction integrity", "failed/kernel replay", "verified/extraction integrity",
                "verified/extraction integrity", "failed/proof checking", "rejected/proof checking",
                "failed/theorem audit", "failed/kernel replay"];
            var text = string.Join('\n', diagnostics);
            if (!statuses.SequenceEqual(expected) || !text.Contains("Unapproved proof axioms") ||
                !text.Contains("Client.Axiomatic.execution") || !text.Contains("Client.Batch.forged") ||
                !text.Contains("while replaying declaration") || !text.Contains("Expected a theorem") ||
                !text.Contains("HiddenSibling.false") || !text.Contains("Client.Axiomatic.hidden") ||
                !text.Contains(separate ? "Batch: 4 passed, 5 failed of 9 requests." :
                    "Batch: 4 passed, 7 failed of 11 requests."))
                throw new InvalidOperationException(
                    "Unexpected batch outcomes: " + string.Join(", ", statuses) + "\n" + text);
            CheckConsumerLeanSummary(text, "Client/Shared.lean:", "(building Client.Shared)");
            var certificateA = JsonSerializer.Deserialize<JsonElement>(
                File.ReadAllText(Path.Combine(batchA, "verified.json")));
            var certificateB = JsonSerializer.Deserialize<JsonElement>(
                File.ReadAllText(Path.Combine(batchB, "verified.json")));
            if (certificateA.GetProperty("initializedTypes")[0].GetString() != "Examples.InitializedTypes" ||
                certificateB.GetProperty("theorem").GetString() != "AlternateProof.correctness" ||
                !certificateB.GetProperty("inputs").TryGetProperty("proof:" + alternate, out _) ||
                new[] { axiomOutput, forgedOutput, missingOutput, hiddenOutput, batchC }.Any(output =>
                    File.Exists(Path.Combine(output, "verified.json"))))
                throw new InvalidOperationException(
                    "Batch certificates were not bound per request or a stale certificate survived.");
            var stages = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
                .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
            var forgedChecks = stages.Where(stage => stage.GetProperty("stage").GetString() is
                    "Kernel replay of consumer proof and dependencies" or "Profiled kernel replay of consumer modules")
                .SelectMany(stage => File.ReadLines(Path.Combine(trace, stage.GetProperty("transcript").GetString()!)))
                .Where(line => line.StartsWith('{')).Select(line => JsonSerializer.Deserialize<JsonElement>(line))
                .Count(record => record.TryGetProperty("module", out var module) &&
                    module.GetString() == "Client.Forged" && record.TryGetProperty("error", out _));
            if (!separate && forgedChecks != 1)
                throw new InvalidOperationException("A shared rejected helper was replayed more than once.");
            var opens = stages.Where(stage => stage.GetProperty("stage").GetString() ==
                "Opening certified Lean verification library").ToArray();
            if (!string.IsNullOrEmpty(Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY")) &&
                opens.Length != groups.Length)
                throw new InvalidOperationException("Unexpected certified-base open count: " + opens.Length);
            var measurements = new
            {
                separate, processes = groups.Length, seconds = timer.Elapsed.TotalSeconds, opens = opens.Length,
                stages = stages.Where(stage => stage.GetProperty("stage").GetString() is { } name &&
                    (name.StartsWith("Building ", StringComparison.Ordinal) ||
                     name.Contains("kernel replay", StringComparison.OrdinalIgnoreCase) ||
                     name == "Opening certified Lean verification library"))
                    .GroupBy(stage => stage.GetProperty("stage").GetString()!).ToDictionary(group => group.Key,
                    group => new { count = group.Count(),
                        seconds = group.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()) })
            };
            File.WriteAllText(Path.Combine(directory, separate ? "separate-timings.json" : "batch-timings.json"),
                JsonSerializer.Serialize(measurements, Json));
            Console.WriteLine(JsonSerializer.Serialize(measurements));
            Console.WriteLine("PASS imported axiom and unchecked declarations rejected without certificates");
            Console.WriteLine("PASS missing sibling theorem and hidden sibling axiom retain independent failures");
            Console.WriteLine("PASS batch requests keep independent outcomes, certificates and expected rejections");
        }
        finally
        {
            Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", savedTrace);
            Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", savedCache);
            foreach (var path in new[] { forged, forgedProof, axiomatic, axiomProof, missingProof, hiddenProof })
                File.Delete(path);
        }
    }

    static void CheckConsumerLeanSummary(string text, params string[] required)
    {
        var start = text.IndexOf("Lean errors (", StringComparison.Ordinal);
        var end = text.IndexOf("Full Lean output follows under Details.", StringComparison.Ordinal);
        var details = end < 0 ? -1 : text.IndexOf("Details:", end, StringComparison.Ordinal);
        if (start < 0 || end < start || details < end)
            throw new InvalidOperationException(
                "Proof-checking failure did not lead with a Lean error summary: " + text);
        var summary = text[start..end];
        if (summary.Split('\n').Length > 60 || summary.Contains("depends on axioms", StringComparison.Ordinal) ||
            summary.Contains("trace:", StringComparison.Ordinal) ||
            required.Any(item => !summary.Contains(item, StringComparison.Ordinal)) ||
            !text[details..].Contains("Command failed", StringComparison.Ordinal))
            throw new InvalidOperationException("Unexpected Lean error summary:\n" + summary + "\nFull text:\n" + text);
    }
}
