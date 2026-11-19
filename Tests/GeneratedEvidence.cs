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
        var count = HeartbeatCount.Match(output);
        if (!count.Success) throw new InvalidOperationException("Missing heartbeat count:\n" + output);
        return (long.Parse(count.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture), output);
    }

    // The line `#eval show IO Nat from IO.getNumHeartbeats` prints.
    [GeneratedRegex(@"(?m)^([0-9]+)\r?$")]
    private static partial Regex HeartbeatCount { get; }

    [GeneratedRegex(@"(?m)^cil_resolution_facts [A-Za-z_][A-Za-z0-9_]*\r?\n")]
    private static partial Regex ResolutionFactsCommand { get; }

    [GeneratedRegex(@"\Adef method(\d+) : Method := .* code := \[\r?\z")]
    private static partial Regex LiteralMethodHeader { get; }

    const string LiteralMethodDefinition = """def method(?<number>\d+) : Method""";
    const string DecodedMethodDefinition = """cil_decoded_method method(?<number>\d+)(?: \[[^\]\r\n]*\])?""";

    [GeneratedRegex($"""(?m)^(?:{LiteralMethodDefinition}|{DecodedMethodDefinition}) :=""")]
    private static partial Regex DefinedMethod { get; }

    // A decoded method's definition line: its options, then its decoder over the method's own definitions.
    const string DecodedMethodHead = """(?m)^cil_decoded_method method(?<number>\d+)( \[[^\]\r\n]*\])? := """;
    const string DecoderCall = """Method\.ofClosed\? profile environment method\k<number>Links """;
    const string DecoderInput = """method\k<number>Closed method\k<number>RawArguments""";

    [GeneratedRegex($"""{DecodedMethodHead}{DecoderCall}{DecoderInput}(?=\r?$)""")]
    internal static partial Regex DecodedMethod { get; }

    [GeneratedRegex(@"(?m)^def method(\d+)Original : Extraction\.RawMethod := [^\r\n]*")]
    private static partial Regex RawDefinition { get; }

    [GeneratedRegex(@"(?m)^def method(?<number>\d+)Closed : [^\r\n]*?returnType := (?<type>[^\r\n]*?), parameters := ")]
    private static partial Regex ClosedReturnType { get; }

    [GeneratedRegex(@"(?m)^@\[cil_code\] def method(\d+)Link(\d+) : Link := [^\r\n]*")]
    private static partial Regex MethodLink { get; }

    [GeneratedRegex(@"(?m)^@\[cil_code\] def method(\d+)Link(\d+) : Link := \.direct (\d+)\r?$")]
    private static partial Regex DirectLink { get; }

    // The head of a one-line theorem, up to its proof.
    [GeneratedRegex(@"(?m)^(theorem (?<name>[\w?!']+) : [^\r\n]*?) := [^\r\n]*")]
    private static partial Regex TheoremHead { get; }

    // A theorem and its indented continuation lines; a Lean name may end in ?, ! or '.
    [GeneratedRegex(@"(?m)^(?:@\[[^\r\n]*\] )?theorem ([\w?!']+) [^\r\n]*(?:\r?\n[ \t]+[^\r\n]*)*\r?\n")]
    private static partial Regex GeneratedTheorem { get; }

    [GeneratedRegex(@" := method\d+_instruction_checks(?:\.[12])+(?=\r?$)", RegexOptions.Multiline)]
    private static partial Regex InstructionCheckProjection { get; }

    [GeneratedRegex(@"\AexternalIdentity(?:Chunk\d+|\d+Bytes)_valid\z")]
    private static partial Regex IdentityWitnessName { get; }

    [GeneratedRegex(@"\A(?:method\d+_tables_valid|assembly\d+_identified|pinned_identities_spelled)\z")]
    private static partial Regex RetainedObligationName { get; }

    // A generated report names one theorem or a bracketed group spanning several lines.
    [GeneratedRegex(@"(?m)^#print axioms (?:\[(?<members>[\w'?!.,\s]+)\]|[\w'?!.]+)[ \t]*\r?(?:\n|\z)")]
    private static partial Regex AxiomsCommand { get; }

    [GeneratedRegex(@"""(?:\\.|[^""\\])*""")]
    private static partial Regex StringLiteral { get; }

    [GeneratedRegex(@"(?m)^(?:namespace|end) Extracted\r?$")]
    private static partial Regex ExtractedNamespaceLine { get; }

    [GeneratedRegex(@"\bExtracted\b")]
    private static partial Regex ExtractedWord { get; }

    [GeneratedRegex(@"(?m)^namespace Extracted\r?$")]
    private static partial Regex NamespaceExtracted { get; }

    [GeneratedRegex(@"(?m)^end Extracted\r?$")]
    private static partial Regex EndExtracted { get; }

    [GeneratedRegex(@"(?m)^import [^\r\n]+\r?\n")]
    private static partial Regex ImportCommand { get; }

    [GeneratedRegex(@"(?m)^(?:namespace|end) Extracted\r?\n")]
    private static partial Regex ExtractedNamespaceCommand { get; }

    [GeneratedRegex(@"^import[ \t]+([A-Za-z_][A-Za-z0-9_.]*)[ \t]*\r?$", RegexOptions.Multiline)]
    private static partial Regex ImportedModule { get; }

    /// <summary>One instruction of an extracted method, as its definition in `Extracted.lean` writes it.</summary>
    sealed record ExtractedInstruction(int Method, int Pc, string Op);

    // `cil_instruction_equations` states each lookup equation from the definition, which lists one op per line.
    static List<ExtractedInstruction> ExtractedInstructions(string source)
    {
        var instructions = new List<ExtractedInstruction>();
        var lines = source.Split('\n');
        for (var line = 0; line < lines.Length; line++)
        {
            var header = LiteralMethodHeader.Match(lines[line]);
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

    // An extraction's definition of method `method` from its decoder, with the field operand definitions it names.
    static Match DecodedDefinition(string source, int method) => DecodedMethod.Matches(source)
        .FirstOrDefault(match => match.Groups["number"].Value == $"{method}") ?? Match.Empty;

    /// <summary>Whether an extraction defines method `method` from its decoder rather than by a literal.</summary>
    static bool IsDecodedMethod(string source, int method) => DecodedDefinition(source, method).Success;

    /// <summary>The numbers of the methods an extraction defines, by a literal or by its decoder.</summary>
    static int[] DefinedMethods(string source) => [.. DefinedMethod.Matches(source)
        .Select(match => int.Parse(match.Groups["number"].Value, System.Globalization.CultureInfo.InvariantCulture))];

    /// <summary>
    /// The line defining the raw method a decoded method is decoded from, the decoder's input. A method kept as a
    /// literal fails, so a reader never takes an absent body for an empty one.
    /// </summary>
    static string DecodedOriginal(string source, int method)
    {
        if (!IsDecodedMethod(source, method))
            throw new InvalidOperationException($"method{method} is not defined from its decoder");
        return RawDefinition.Matches(source)
            .FirstOrDefault(match => match.Groups[1].Value == $"{method}")?.Value ?? "";
    }

    /// <summary>
    /// Decodes the forged original so the emitted code differs from the closed evidence used by the checks.
    /// </summary>
    static string ForgeDecodedOriginal(string source, int method, string before, string after)
    {
        var original = DecodedOriginal(source, method);
        if (!original.Contains(before, StringComparison.Ordinal))
            throw new InvalidOperationException($"method{method}Original has no {before}");
        var definition = DecodedDefinition(source, method);
        var name = $"method{method}";
        var decoder = $"Method.ofRaw? profile environment {name}Links {name}Original {name}TypeArgumentsRaw";
        var command = definition.Value[..definition.Value.IndexOf("Method.ofClosed?", StringComparison.Ordinal)];
        var changed = source.Replace(definition.Value, $"""{command}{decoder}""", StringComparison.Ordinal);
        return changed.Replace(original, original.Replace(before, after, StringComparison.Ordinal),
            StringComparison.Ordinal);
    }

    /// <summary>
    /// `source` with decoded method `method` defined by a forged decoder: the extraction's decoder call with
    /// `update`, a structure update of the decoded `method`, applied to the method it gives.
    /// </summary>
    static string ForgeDecodedMethod(string source, int method, string update)
    {
        // The definition writes a decoded method's links as the table constant its decoder is given.
        if (update.Contains("links :=", StringComparison.Ordinal))
            throw new InvalidOperationException(
                $"Forge method{method}Links, the decoder's input, to change its links");
        var call = DecodedDefinition(source, method);
        if (!call.Success) throw new InvalidOperationException($"method{method} is not defined from its decoder");
        var forged = $"method{method}Forged";
        var name = $"method{method}";
        var decoder = $"{forged} profile environment {name}Links {name}Closed {name}RawArguments";
        return $$"""
            {{source[..call.Index]}}def {{forged}} (profile : FeatureProfile) (environment : LayoutEnvironment)
                (links : List (Prod Nat Link)) (closed : Extraction.RawMethod) (storage : Extraction.RawArguments) :
                Option Method := (Method.ofClosed? profile environment links closed storage).map fun method =>
                  { method with {{update}} }
            cil_decoded_method {{name}}{{call.Groups[1].Value}} := {{decoder}}{{source[(call.Index + call.Length)..]}}
            """;
    }

    /// <summary>
    /// `source` with decoded method `method` declaring its closed definition's return type with `atom` replaced by
    /// `replacement`, through a forged decoder.
    /// </summary>
    static string ForgeDecodedReturnType(string source, int method, string atom, string replacement)
    {
        var closed = ClosedReturnType.Matches(source)
            .FirstOrDefault(match => match.Groups["number"].Value == $"{method}");
        var returnType = closed?.Groups["type"].Value ?? "";
        if (!returnType.Contains(atom, StringComparison.Ordinal))
            throw new InvalidOperationException($"method{method}Closed returns no {atom}");
        return ForgeDecodedMethod(source, method, "declared := { method.declared with returnType := " +
            returnType.Replace(atom, replacement, StringComparison.Ordinal) + " }");
    }

    /// <summary>
    /// `source` with the link of the call at `pc` of method `method` changed to `link`: the definition the method's
    /// link table names, whether the method is decoded or kept as a literal.
    /// </summary>
    static string ForgeLink(string source, int method, int pc, string link)
    {
        var definition = MethodLink.Matches(source).FirstOrDefault(match =>
                match.Groups[1].Value == $"{method}" && match.Groups[2].Value == $"{pc}")
            ?? throw new InvalidOperationException($"method{method} has no link at pc {pc}");
        return source[..definition.Index] + $"@[cil_code] def method{method}Link{pc} : Link := {link}" +
            source[(definition.Index + definition.Length)..];
    }

    /// <summary>
    /// The arguments of method `method`'s feature-flow obligation that a decided-false report prints on one line,
    /// naming that method's raw definition and certificate.
    /// </summary>
    static string FeatureObligation(object method) =>
        $"method{method}Closed profile method{method}FeatureStates method{method}Reachable";

    /// <summary>The method and pc of each call whose link in `source` is the direct link to method `callee`.</summary>
    static (int Method, int Pc)[] DirectLinks(string source, int callee) => [.. DirectLink.Matches(source)
        .Where(match => match.Groups[3].Value == $"{callee}")
        .Select(match => (int.Parse(match.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture),
            int.Parse(match.Groups[2].Value, System.Globalization.CultureInfo.InvariantCulture)))];

    // Keep emitted definitions intact and select one independent validator obligation.
    // Its unchanged form must also be compiled as a positive control by the caller.
    static string NarrowEvidence(string source, string theorem)
    {
        var found = 0;
        var result = GeneratedTheorem.Replace(source, match =>
            {
                // Byte-backed identity definitions carry these checked UTF-8 witnesses.
                if (IdentityWitnessName.IsMatch(match.Groups[1].Value))
                    return match.Value;
                // A body obligation reads its module's lookup tables through their equality with the metadata, the
                // identity of each assembly it reaches through the assembly's own proof, and the pins through theirs.
                if (match.Groups[1].Value != theorem &&
                    RetainedObligationName.IsMatch(match.Groups[1].Value) &&
                    !theorem.EndsWith("_tables_valid", StringComparison.Ordinal))
                    return match.Value;
                if (match.Groups[1].Value != theorem) return "";
                found++;
                // Isolated layout and scalar checks decide all claims against the fixture's definitions.
                if (match.Value.Contains(" : Extraction.MethodLayoutsValid ", StringComparison.Ordinal) ||
                    match.Value.Contains(" : And (Extraction.ScalarFlowValid ", StringComparison.Ordinal))
                    return TheoremHead.Replace(match.Value, "$1 := by decide +kernel");
                return InstructionCheckProjection.Replace(match.Value, " := by decide +kernel");
            });
        if (found != 1) throw new InvalidOperationException("Missing unique evidence obligation: " + theorem);
        result = ResolutionFactsCommand.Replace(result, "");
        return AxiomsCommand.Replace(result, "");
    }

    // Keep narrowed declarations and exact obligation types checked, but reuse the original
    // proof instead of reducing the same validator twice. Mutations never use these witnesses.
    static string CheckedEvidenceControl(string original, string narrowed, IEnumerable<string> theorems, int index)
    {
        // Explicit references could bypass the projected declarations and reach the original.
        var code = StringLiteral.Replace(narrowed, "\"\"");
        code = ExtractedNamespaceLine.Replace(code, "");
        if (ExtractedWord.IsMatch(code))
            throw new InvalidOperationException("Evidence controls require namespace-relative references.");
        if (NamespaceExtracted.Count(narrowed) != 1 || EndExtracted.Count(narrowed) != 1)
            throw new InvalidOperationException("Missing unique evidence control namespace.");
        var witnesses = new StringBuilder();
        var audits = new StringBuilder();
        foreach (var theorem in theorems)
        {
            var witness = $"evidenceControl{index}_{theorem}";
            Match[] Stated(string text) =>
                [.. TheoremHead.Matches(text).Where(match => match.Groups["name"].Value == theorem)];
            var (originalMatches, narrowedMatches) = (Stated(original), Stated(narrowed));
            if (narrowedMatches.Length != 1 || originalMatches.Length != 1 ||
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
        narrowed = ImportCommand.Replace(narrowed, "");
        // A nested Extracted namespace can resolve missing names in the original Extracted.
        narrowed = ExtractedNamespaceCommand.Replace(narrowed, "");
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
                var body = ImportedModule.Replace(source, match =>
                {
                    imports.Add(match.Groups[1].Value);
                    return "";
                });
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
