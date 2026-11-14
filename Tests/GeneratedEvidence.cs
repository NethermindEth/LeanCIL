using System.Diagnostics;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
    // Heartbeats count the elaborator's and the kernel's work on one thread, so they repeat exactly where compile
    // time varies with the machine's load. Returns the count `text` costs, imports included, and Lean's output.
    static (long Heartbeats, string Output) CountHeartbeats(string path, string text)
    {
        File.WriteAllText(path, text + "\n#eval show IO Nat from IO.getNumHeartbeats\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        if (output.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidOperationException("A measured file depends on sorryAx: " + path);
        var count = HeartbeatCount().Match(output);
        if (!count.Success) throw new InvalidOperationException("Missing heartbeat count:\n" + output);
        return (long.Parse(count.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture), output);
    }

    // The line `#eval show IO Nat from IO.getNumHeartbeats` prints.
    [GeneratedRegex(@"(?m)^([0-9]+)\r?$")]
    private static partial Regex HeartbeatCount();

    /// <summary>One instruction of an extracted method, as its definition in `Extracted.lean` writes it.</summary>
    sealed record ExtractedInstruction(int Method, int Pc, string Op);

    // `cil_instruction_equations` states each lookup equation from the definition, which lists one op per line.
    static List<ExtractedInstruction> ExtractedInstructions(string source)
    {
        var instructions = new List<ExtractedInstruction>();
        var lines = source.Split('\n');
        for (var line = 0; line < lines.Length; line++)
        {
            var header = Regex.Match(lines[line], @"\Adef method(\d+) : Method := .* code := \[\r?\z");
            if (!header.Success) continue;
            var method = int.Parse(header.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture);
            // The line that closes the code list ends the definition, whatever follows it.
            for (var (pc, last) = (0, false); !last && ++line < lines.Length; pc++)
            {
                var op = lines[line].Trim();
                last = op.EndsWith("] }", StringComparison.Ordinal);
                if (op == "] }") break;
                instructions.Add(new(method, pc, last ? op[..^3] : op[..^1]));
            }
        }
        return instructions;
    }

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
                // A body obligation reads its module's lookup tables through their equality with the metadata, the
                // identity of each assembly it reaches through the assembly's own proof, and the pins through theirs.
                if (match.Groups[1].Value != theorem &&
                    Regex.IsMatch(match.Groups[1].Value,
                        @"\A(?:method\d+_tables_valid|assembly\d+_identified|pinned_identities_spelled)\z") &&
                    !theorem.EndsWith("_tables_valid", StringComparison.Ordinal))
                    return match.Value;
                if (match.Groups[1].Value != theorem) return "";
                found++;
                return match.Value;
            });
        if (found != 1) throw new InvalidOperationException("Missing unique evidence obligation: " + theorem);
        return Regex.Replace(result, @"(?m)^#print axioms [^\r\n]*\r?\n", "");
    }

    // Keep narrowed declarations and exact obligation types checked, but reuse the original
    // proof instead of reducing the same validator twice. Mutations never use these witnesses.
    static string CheckedEvidenceControl(string original, string narrowed, IEnumerable<string> theorems, int index)
    {
        // Explicit references could bypass the projected declarations and reach the original.
        var code = Regex.Replace(narrowed, @"""(?:\\.|[^""\\])*""", "\"\"");
        code = Regex.Replace(code, @"(?m)^(?:namespace|end) Extracted\r?$", "");
        if (Regex.IsMatch(code, @"\bExtracted\b"))
            throw new InvalidOperationException("Evidence controls require namespace-relative references.");
        if (Regex.Matches(narrowed, @"(?m)^namespace Extracted\r?$").Count != 1 ||
            Regex.Matches(narrowed, @"(?m)^end Extracted\r?$").Count != 1)
            throw new InvalidOperationException("Missing unique evidence control namespace.");
        var witnesses = new StringBuilder();
        var audits = new StringBuilder();
        foreach (var theorem in theorems)
        {
            var witness = $"evidenceControl{index}_{theorem}";
            var pattern = @"(?m)^(theorem " + Regex.Escape(theorem) + @" : [^\r\n]*?) := [^\r\n]*";
            var originalMatches = Regex.Matches(original, pattern);
            var narrowedMatches = Regex.Matches(narrowed, pattern);
            if (narrowedMatches.Count != 1 || originalMatches.Count != 1 ||
                narrowedMatches[0].Groups[1].Value != originalMatches[0].Groups[1].Value)
                throw new InvalidOperationException("Missing unique control obligation: " + theorem);
            var header = originalMatches[0].Groups[1].Value;
            var type = header[(header.IndexOf(" : ", StringComparison.Ordinal) + 3)..];
            witnesses.AppendLine($"open CIL Extracted in\nprivate theorem {witness} : {type} := Extracted.{theorem}");
            witnesses.AppendLine($"#print axioms {witness}");
            var obligation = narrowedMatches[0];
            narrowed = narrowed[..obligation.Index] + header + " := by exact " + witness +
                narrowed[(obligation.Index + obligation.Length)..];
            audits.AppendLine($"#print axioms EvidenceControl{index}.{theorem}");
        }
        narrowed = Regex.Replace(narrowed, @"(?m)^import [^\r\n]+\r?\n", "");
        // A nested Extracted namespace can resolve missing names in the original Extracted.
        narrowed = Regex.Replace(narrowed, @"(?m)^(?:namespace|end) Extracted\r?\n", "");
        return witnesses + $"\nnamespace EvidenceControl{index}\nset_option autoImplicit false\n" + narrowed +
            $"\nend EvidenceControl{index}\n" + audits;
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
        // fixtures additionally replay every serialized declaration with the authenticated auditor.
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
                fixtureVerification!.ReplayCheckedModules(["PositiveBatch"],
                    Path.GetDirectoryName(batch) + Path.PathSeparator + FixtureLeanPath(),
                    "Kernel replay of generated evidence");
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
