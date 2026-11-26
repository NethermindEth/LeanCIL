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
        var contract = Path.Combine(root, "Client", "Contract.lean");
        var contractProof = Path.Combine(root, "ContractProof.lean");
        var refutationProof = Path.Combine(root, "RefutationProof.lean");
        var brokenProof = Path.Combine(root, "BrokenRefutation.lean");
        var otherProof = Path.Combine(root, "OtherRefutation.lean");
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
                import CIL.Safety.Execution
                namespace Client.Axiomatic
                axiom hidden : False
                axiom execution (x y : CIL.W64) (memory : CIL.Safety.Memory) :
                    CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i64 x), .scalar (.i64 y)] memory =
                      .ok (memory, [.scalar (.i64 (x + y))])
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
            string Copy(string source, string name)
            {
                var copy = Path.Combine(Path.GetDirectoryName(source)!, name + "-" + Guid.NewGuid().ToString("N"));
                CopyTree(source, copy);
                return copy;
            }
            foreach (var output in new[] { axiomOutput, forgedOutput, missingOutput, hiddenOutput })
                CopyTree(batchB, output);
            // Expected rejections: a refutation of the contract the Add copy verifies, and one control per way a
            // rejection can fail; the tampered copy fails its extraction check.
            var (contractOutput, absentOutput) = (Copy(batchB, "ConsumerBatchContract"), Copy(batchB, "Absent"));
            var (refutedOutput, tamperedOutput) = (Copy(batchC, "Refuted"), Copy(batchC, "Tampered"));
            File.AppendAllText(Path.Combine(tamperedOutput, "Extracted.lean"), "\n-- changed after extraction\n");
            File.WriteAllText(contract, ContractSource);
            File.WriteAllText(contractProof, $"import Client.Contract\n{HoldsSource}");
            File.WriteAllText(refutationProof, Refuting("RefutationProof", "add", 0, 1));
            File.WriteAllText(brokenProof, Refuting("BrokenRefutation", "add", 0, 0));
            File.WriteAllText(otherProof, Refuting("OtherRefutation", "product", 1, 1));
            foreach (var output in new[] { axiomOutput, forgedOutput, missingOutput, hiddenOutput, batchC })
                File.WriteAllText(Path.Combine(output, "verified.json"), "{}");
            object Request(string output, string selectedProof, string theorem = "ExampleProof.correctness",
                string expect = "verified") => new { output, proof = selectedProof, theorem, expect };
            // Separate runs put every request from the third on in one manifest, which numbers them from zero.
            const int contractRequest = 9;
            var refutes = separate ? contractRequest - 2 : contractRequest;
            object Rejected(string output, string selectedProof, string theorem) =>
                new { output, proof = selectedProof, theorem, expect = "rejected", refutes };
            object[] requests =
            [
                Request(axiomOutput, axiomProof), Request(forgedOutput, forgedProof), Request(batchA, proof),
                Request(batchB, forgedProof), Request(batchB, proof),
                Request(batchB, alternate, "AlternateProof.correctness"), Request(batchC, proof),
                Request(missingOutput, missingProof, "AlternateProof.correctness"),
                Request(hiddenOutput, hiddenProof, "HiddenSibling.false"),
                Request(contractOutput, contractProof, "ContractProof.holds"),
                Rejected(refutedOutput, refutationProof, "RefutationProof.refuted"),
                Rejected(refutedOutput, brokenProof, "BrokenRefutation.refuted"),
                Rejected(refutedOutput, otherProof, "OtherRefutation.refuted"),
                Rejected(absentOutput, contractProof, "ContractProof.holds"),
                Rejected(tamperedOutput, refutationProof, "RefutationProof.refuted")
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
            // A rejection fails when its refutation does not build, refutes another contract, refutes nothing or
            // reads a changed extraction.
            string[] expected = ["failed/theorem audit", "failed/kernel replay", "verified/extraction integrity",
                "failed/kernel replay", "verified/extraction integrity", "verified/extraction integrity",
                "failed/proof checking", "failed/theorem audit", "failed/kernel replay",
                "verified/extraction integrity", "rejected/extraction integrity", "failed/proof checking",
                "failed/statement identity", "failed/statement identity", "failed/extraction integrity"];
            var text = string.Join('\n', diagnostics);
            if (!statuses.SequenceEqual(expected) || !text.Contains("Unapproved proof axioms") ||
                !text.Contains("Client.Axiomatic.execution") || !text.Contains("Client.Batch.forged") ||
                !text.Contains("while replaying declaration") || !text.Contains("Expected a theorem") ||
                !text.Contains("HiddenSibling.false") || !text.Contains("Client.Axiomatic.hidden") ||
                !text.Contains("PASS rejected") || !text.Contains("(refutes CIL.Safety.MethodContract.Holds for " +
                    "System.UInt64 Examples.Arithmetic::WrongAdd(System.UInt64,System.UInt64))") ||
                !text.Contains("so it refutes another contract") || !text.Contains("so it refutes nothing") ||
                text.Split($"no verified refutation of request {refutes}").Length != 5 ||
                !text.Contains(separate ? "Batch: 5 passed, 8 failed of 13 requests." :
                    "Batch: 5 passed, 10 failed of 15 requests."))
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
            foreach (var path in new[] { forged, forgedProof, axiomatic, axiomProof, missingProof, hiddenProof,
                contract, contractProof, refutationProof, brokenProof, otherProof })
                File.Delete(path);
        }
    }

    /// <summary>The addition contract the Add copy verifies, and the product contract a control refutes.</summary>
    const string ContractSource = """
        import Extracted
        import CIL.Safety.SymbolicExecution
        import CIL.Safety.MethodContract
        open CIL.Safety
        namespace Client.Contract
        /-- Every pair of words returns their wrapping sum and leaves memory unchanged. -/
        def add : MethodContract (CIL.W64 × CIL.W64) where
          args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
          pre _ _ := True
          footprint _ := []
          post input initial final values :=
            final = initial ∧ values = [.scalar (.i64 (input.1 + input.2))]
        /-- Every pair of words returns their wrapping product and leaves memory unchanged. -/
        def product : MethodContract (CIL.W64 × CIL.W64) where
          args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
          pre _ _ := True
          footprint _ := []
          post input initial final values :=
            final = initial ∧ values = [.scalar (.i64 (input.1 * input.2))]
        end Client.Contract
        """;

    /// <summary>The addition contract proved for the extracted Add.</summary>
    const string HoldsSource = """
        namespace ContractProof
        open CIL.Safety
        /-- The extracted method meets the addition contract. -/
        theorem holds : Client.Contract.add.Holds Extracted.program 0 := by
          rintro ⟨left, right⟩ memory -
          refine MethodContract.Holds.intro (c := Client.Contract.add) (input := (left, right)) memory
            [.scalar (.i64 (left + right))] ?_ (Confined.refl _ memory) ⟨rfl, rfl⟩
          dsimp only [Client.Contract.add]
          cil_checked_steps []
        #print axioms holds
        end ContractProof
        """;

    /// <summary>A refutation of `contract` whose witness is `(left, right)`.</summary>
    static string Refuting(string space, string contract, int left, int right) => $$"""
        import Client.Contract
        namespace {{space}}
        open CIL.Safety
        /-- The extracted method returns another value than the contract at `({{left}}, {{right}})`. -/
        theorem refuted : Client.Contract.{{contract}}.Refuted Extracted.program 0 :=
          .of_return (input := ({{left}}, {{right}})) (initial := Memory.empty) trivial
            (rfl : invoke Extracted.program 16 0 [.scalar (.i64 {{left}}), .scalar (.i64 {{right}})]
              Memory.empty = .ok _)
            (by rintro ⟨-, out, rfl, -, wrong⟩; revert wrong; decide)
        #print axioms refuted
        end {{space}}
        """;

    static void CheckConsumerLeanSummary(string text, params string[] required)
    {
        var start = text.IndexOf("Lean errors (", StringComparison.Ordinal);
        if (start < 0)
            throw new InvalidOperationException(
                "Proof-checking failure did not lead with a Lean error summary: " + text);
        // The summary runs to the shortened errors under Details, the proof's messages, or the end.
        var end = new[] { "\nDetails:", "  Lean messages (" }
            .Select(marker => text.IndexOf(marker, start, StringComparison.Ordinal))
            .Where(index => index >= 0).DefaultIfEmpty(text.Length).Min();
        var summary = text[start..end];
        // Each error is printed once, in the developer's files: no raw transcript or workspace copy follows.
        if (summary.Split('\n').Length > 60 || summary.Contains("depends on axioms", StringComparison.Ordinal) ||
            summary.Contains("trace:", StringComparison.Ordinal) ||
            required.Any(item => !summary.Contains(item, StringComparison.Ordinal)) ||
            text.Contains("Full Lean output follows under Details.", StringComparison.Ordinal) ||
            text[end..].StartsWith("\nDetails:\nCommand failed", StringComparison.Ordinal) ||
            summary.Contains("LeanCILProof", StringComparison.Ordinal) ||
            summary.Contains("leancil-consumer-", StringComparison.Ordinal))
            throw new InvalidOperationException("Unexpected Lean error summary:\n" + summary + "\nFull text:\n" + text);
    }
}
