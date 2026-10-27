using System.Diagnostics;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
    // Keep emitted definitions intact and select one independent validator obligation.
    // Its unchanged form must also be compiled as a positive control by the caller.
    static string NarrowEvidence(string source, string theorem)
    {
        var found = 0;
        var result = Regex.Replace(source,
            @"(?m)^(?:@\[[^\r\n]*\] )?theorem (\w+) [^\r\n]*(?:\r?\n[ \t]+[^\r\n]*)*\r?\n", match =>
            {
                // Byte-backed identity definitions carry these checked UTF-8 witnesses.
                if (Regex.IsMatch(match.Groups[1].Value, @"\AexternalIdentity(?:Chunk\d+|\d+Bytes)_valid\z"))
                    return match.Value;
                if (match.Groups[1].Value != theorem) return "";
                found++;
                return match.Value;
            });
        if (found != 1) throw new InvalidOperationException("Missing unique evidence obligation: " + theorem);
        return Regex.Replace(result, @"(?m)^#print axioms [^\r\n]*\r?\n", "");
    }

    // Only generated, namespace-relative evidence belongs here. Rejection fixtures use
    // their isolated environments and diagnostics; arbitrary consumer proofs use the verifier.
    sealed class GeneratedEvidence(string directory, bool measure = false)
    {
        readonly List<(string Path, string Source, string Passed, string Theorem)> cases = [];

        public void Add(string path, string passed, string theorem = "translation_valid") =>
            cases.Add((Path.GetFullPath(path), File.ReadAllText(path), passed, theorem));

        string BatchSource()
        {
            var imports = new SortedSet<string>(StringComparer.Ordinal);
            var bodies = new StringBuilder();
            for (var index = 0; index < cases.Count; index++)
            {
                var source = cases[index].Source;
                if (!source.Contains("namespace Extracted\n", StringComparison.Ordinal) ||
                    !source.Contains("theorem " + cases[index].Theorem + " :", StringComparison.Ordinal))
                    throw new InvalidOperationException("Expected generated extraction evidence: " + cases[index].Path);
                var body = Regex.Replace(source, @"^import[ \t]+([A-Za-z_][A-Za-z0-9_.]*)[ \t]*\r?$", match =>
                {
                    imports.Add(match.Groups[1].Value);
                    return "";
                }, RegexOptions.Multiline);
                bodies.AppendLine($"namespace EvidenceCase{index}");
                bodies.AppendLine(body);
                bodies.AppendLine("#print axioms Extracted." + cases[index].Theorem);
                bodies.AppendLine($"end EvidenceCase{index}");
            }
            return string.Join('\n', imports.Select(module => "import " + module)) + "\n" + bodies;
        }

        double MeasureSeparate()
        {
            var timer = Stopwatch.StartNew();
            foreach (var item in cases)
            {
                if (File.ReadAllText(item.Path) != item.Source)
                    throw new InvalidOperationException("Evidence changed before measurement: " + item.Path);
                var output = Run(["lake", "env", "lean", item.Path], cwd: FixturePackage());
                if (output.Contains("sorryAx", StringComparison.Ordinal))
                    throw new InvalidOperationException("Untrusted evidence: " + item.Path);
            }
            return timer.Elapsed.TotalSeconds;
        }

        // Direct semantic fixtures already kernel-check during elaboration. Certificate audit
        // fixtures additionally replay their serialized declarations in leanchecker.
        public void Check(bool replay = true)
        {
            if (cases.Count == 0) return;
            Directory.CreateDirectory(directory);
            var batch = Path.GetFullPath(Path.Combine(directory, "PositiveBatch.lean"));
            File.WriteAllText(batch, BatchSource());
            double? separateSeconds = measure ? MeasureSeparate() : null;
            var timer = Stopwatch.StartNew();
            var compiled = Path.ChangeExtension(batch, ".olean");
            File.Delete(compiled);
            var checkedBatch = Run(["lake", "env", "lean", "--root=" + Path.GetDirectoryName(batch),
                .. replay ? new[] { "-o", compiled } : [], batch], cwd: FixturePackage());
            if (checkedBatch.Contains("sorryAx", StringComparison.Ordinal))
                throw new InvalidOperationException("Untrusted generated evidence batch");
            var buildSeconds = timer.Elapsed.TotalSeconds;
            if (replay)
                Run(["leanchecker", "PositiveBatch"], leanPath: Path.GetDirectoryName(batch) + Path.PathSeparator +
                    FixtureLeanPath());
            timer.Stop();
            foreach (var item in cases)
            {
                if (File.ReadAllText(item.Path) != item.Source)
                    throw new InvalidOperationException("Evidence changed during checking: " + item.Path);
            }
            foreach (var item in cases) Console.WriteLine(item.Passed);
            var measurements = new { fixtures = cases.Count, separateSeconds, batchSeconds = timer.Elapsed.TotalSeconds,
                buildSeconds, replaySeconds = timer.Elapsed.TotalSeconds - buildSeconds,
                sources = cases.ToDictionary(item => item.Path, item => ContentKey(item.Source)) };
            File.WriteAllText(Path.Combine(directory, "batch-timings.json"),
                JsonSerializer.Serialize(measurements, Json));
            Console.WriteLine($"PASS {cases.Count} generated evidence fixtures in one checked batch");
            cases.Clear();
        }
    }
}
