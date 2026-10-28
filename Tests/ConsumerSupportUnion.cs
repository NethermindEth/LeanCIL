using System.Diagnostics;
using System.Text.Json;

partial class Program
{
    static void CheckConsumerSupportUnion(string[] args)
    {
        var measureOnly = args.Contains("--measure", StringComparer.Ordinal);
        var extractor = args.FirstOrDefault(argument => argument != "--measure") ?? ExtractorPath;
        var cli = new[] { "dotnet", Path.GetFullPath(extractor) };
        var root = At("artifacts/ConsumerSupportUnion-" + Guid.NewGuid().ToString("N"));
        var package = Path.Combine(root, "Package");
        var support = Path.Combine(package, "Client");
        Directory.CreateDirectory(support);
        File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
        var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
        File.WriteAllText(Path.Combine(package, "lakefile.toml"),
            "name = \"support-union\"\n[[require]]\nname = \"leancil\"\ngit = " +
            JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) +
            "\n[[lean_lib]]\nname = \"Client\"\n");
        Run(["lake", "update"], package);
        File.WriteAllText(Path.Combine(support, "Early.lean"), "theorem early : True := True.intro\n#print axioms early\n");
        File.WriteAllText(Path.Combine(support, "Late.lean"), "theorem late : True := True.intro\n#print axioms late\n");
        File.WriteAllText(Path.Combine(support, "Dependent.lean"), "import Extracted\ndef program := Extracted.program\n");
        File.WriteAllText(Path.Combine(support, "Indirect.lean"), "import Client.Dependent\n");
        File.WriteAllText(Path.Combine(support, "RepeatedImports.lean"), "import Client.Dependent import Client.Late\n");
        var requests = Enumerable.Range(0, 3).Select(index =>
        {
            var output = Path.Combine(root, "Extraction" + index);
            var proof = Path.Combine(package, "Proof" + index + ".lean");
            var method = index == 0 ? "InitializedTypes::Add(ulong,ulong)" : "Arithmetic::Add(ulong,ulong)";
            string[] options = index == 0 ? ["--assume-initialized", "Examples.InitializedTypes"]
                : index == 2 ? ["x64-v3"] : [];
            Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), method, output, .. options]);
            File.WriteAllText(proof, "import Client." + (index == 0 ? "Early" : "Late") + "\n" +
                (index == 0 ? "" : "import Client.RepeatedImports\n") + """
        import Client.Indirect
        import CIL.Semantics
        namespace ExampleProof
        theorem correctness (x y : CIL.W64) (memory : CIL.Memory) :
            CIL.invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
              some (memory, [.i64 (x + y)]) := by rfl
        #print axioms correctness
        end ExampleProof
        """);
            return new { output, proof, theorem = "ExampleProof.correctness" };
        }).ToArray();
        var saved = new[] { "LEANCIL_DISABLE_SUCCESS_CACHE", "LEANCIL_CONSUMER_SUPPORT",
            "LEANCIL_CONSUMER_SUPPORT_SHA256", "LEANCIL_EXPORT_CONSUMER_SUPPORT", "LEANCIL_TRACE_DIRECTORY" }
            .ToDictionary(name => name, Environment.GetEnvironmentVariable);
        var measurements = new List<object>();
        try
        {
            Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
            foreach (var name in saved.Keys.Where(name => name != "LEANCIL_DISABLE_SUCCESS_CACHE"))
                Environment.SetEnvironmentVariable(name, null);
            // A supplied library is already prepared; the batches authenticate it and verify every request.
            if (string.IsNullOrWhiteSpace(Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY")))
                Run([.. cli, "verify", requests[0].output, "--proof", requests[0].proof, "--proof-root", package]);
            foreach (var order in new[] { new[] { 0, 1, 2 }, new[] { 2, 0, 1 } })
            {
                var trace = ConsumerTraceDirectory.Create(root, "Trace");
                Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
                var manifest = Path.Combine(root, "batch.json");
                File.WriteAllText(manifest, JsonSerializer.Serialize(new
                {
                    schema = 1, proofRoot = package, requests = order.Select(index => requests[index]).ToArray()
                }));
                var timer = Stopwatch.StartNew();
                Run([.. cli, "verify-batch", manifest, "--parallel", "2"]);
                timer.Stop();
                var stages = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
                    .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
                var builds = stages.Where(stage => stage.GetProperty("stage").GetString() is
                    "Building shared consumer support" or "Building fresh consumer proof and dependencies").ToArray();
                var replays = stages.Where(stage => stage.GetProperty("stage").GetString() is
                    "Kernel replay of consumer proof and dependencies" or
                    "Joint kernel replay of consumer proof and dependencies").ToArray();
                string Transcript(JsonElement stage) => File.ReadAllText(Path.Combine(trace,
                    stage.GetProperty("transcript").GetString()!));
                var replayed = replays.SelectMany(stage => Transcript(stage).Split('\n')
                    .Where(line => line.StartsWith('{')).Select(line => JsonSerializer.Deserialize<JsonElement>(line)
                        .GetProperty("module").GetString()!)).ToArray();
                var counts = new[] { "Client.Early", "Client.Late", "Client.Dependent", "Client.Indirect",
                    "Client.RepeatedImports", "Extracted" }
                    .ToDictionary(module => module, module => replayed.Count(name => name == module));
                if (!measureOnly && (counts["Client.Early"] != 1 || counts["Client.Late"] != 1 ||
                    counts["Client.Dependent"] != 3 || counts["Client.Indirect"] != 3 ||
                    counts["Client.RepeatedImports"] != 2 || counts["Extracted"] != 3))
                    throw new Exception("Incorrect support replay counts: " + JsonSerializer.Serialize(counts));
                var lateBuilds = builds.Sum(stage => System.Text.RegularExpressions.Regex.Matches(Transcript(stage),
                    @"\bBuilt Client\.Late(?:\s|$)").Count);
                if (!measureOnly && lateBuilds != 1) throw new Exception("Late support was built " + lateBuilds + " times.");
                measurements.Add(new { order, seconds = timer.Elapsed.TotalSeconds, counts, lateBuilds,
                    buildSeconds = builds.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()),
                    replaySeconds = replays.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()) });
                var message = measureOnly ? "MEASURE consumer batch in order "
                    : "PASS support union and extraction-dependent replay in order ";
                Console.WriteLine(message + string.Join(',', order));
            }
            var timingPath = Path.Combine(root, "timings.json");
            File.WriteAllText(timingPath, JsonSerializer.Serialize(measurements, Json));
            Console.WriteLine(timingPath);
            Console.WriteLine(JsonSerializer.Serialize(measurements));
        }
        finally
        {
            foreach (var (name, value) in saved) Environment.SetEnvironmentVariable(name, value);
        }
    }
}
