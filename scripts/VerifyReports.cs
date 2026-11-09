using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

// The opt-in machine-readable result of `leancil verify --format json`: established facts only, read from
// FailureReports' taxonomy, the failure records `CIL.Observe` logs and the integrity-checked manifest.
internal static partial class VerifyReports
{
    /// <summary>The version of the report's shape; a change that removes or renames a field increments it.</summary>
    internal const int Schema = 1;

    /// <summary>The version of the `verify-batch --format json` document's shape, which holds one report per request.
    /// </summary>
    internal const int BatchSchema = 1;

    /// <summary>`CIL.Safety.obligationTags`, the first component of every tag a LeanCIL tactic gives a goal.</summary>
    internal static readonly string[] ObligationTags =
        ["invariant", "measure", "precondition", "wellFormed", "staticWorld", "raises", "postcondition"];

    static readonly JsonSerializerOptions Json = new()
    {
        WriteIndented = true, Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping
    };

    // Lean's goal display heads each goal of an `unsolved goals` error with `case <tag>` when the goal has a tag.
    [GeneratedRegex(@"^case (?<tag>\S+)$")]
    private static partial Regex GoalCase();

    // A manifest instruction line, `IL_0002: add`.
    [GeneratedRegex(@"\AIL_(?<offset>[0-9a-fA-F]+): (?<text>.*)\z")]
    private static partial Regex ManifestInstruction();

    // One sequence point of `ExtractedSymbols.points`: `(pc, "file", line, column)`.
    [GeneratedRegex("""\((?<pc>\d+), (?<file>"(?:[^"\\]|\\.)*"), (?<line>\d+), (?<column>\d+)\)""")]
    private static partial Regex SymbolPoint();

    /// <summary>A visible sequence point of the PDB: the first pc it covers and its C# location.</summary>
    internal sealed record SourcePoint(int Pc, string File, int Line, int Column);

    /// <summary>
    /// A method of the manifest: its signature, its instructions by pc, as `IL_0002: add`, and its sequence points
    /// in pc order, null when the extraction has no symbols.
    /// </summary>
    internal sealed record ManifestMethod(string Signature, string[] Instructions, SourcePoint[]? Points = null);

    /// <summary>Why a record carries no C# location when the extraction has no symbols.</summary>
    internal const string NoSymbols =
        "the extraction has no Symbols.lean: the assembly was extracted without a matching portable PDB";

    /// <summary>A failure record of `text`, a message `CIL.Observe` logged, or null for any other message.</summary>
    internal static JsonObject? Record(string text)
    {
        if (!text.StartsWith(Program.FailureMarker, StringComparison.Ordinal)) return null;
        try { return JsonNode.Parse(text[Program.FailureMarker.Length..]) as JsonObject; }
        catch (JsonException) { return null; }
    }

    /// <summary>
    /// The open goal of `text`, a message `CIL.Observe` logged under `cil.goals`, or null for any other message:
    /// why it is open, in the report's words, and the goal as Lean prints it.
    /// </summary>
    internal static (string Kind, string Goal)? Goal(string text)
    {
        if (!text.StartsWith(Program.GoalMarker, StringComparison.Ordinal)) return null;
        var parts = text[Program.GoalMarker.Length..].Split('\n', 2);
        var kind = parts[0] switch
        {
            "sorry" => "sorry",
            "error" => "failing tactic",
            "unsolved" => "unsolved",
            _ => null
        };
        return kind is null || parts.Length != 2 ? null : (kind, parts[1]);
    }

    /// <summary>Whether `text` is a step of the `CIL.step` trace.</summary>
    internal static bool IsStep(string text) => text.StartsWith(Program.TraceHeader, StringComparison.Ordinal);

    /// <summary>The obligation tags of the goals an `unsolved goals` message lists, checked against the tags.</summary>
    internal static string[] UnsolvedObligations(string message) =>
        message.Split('\n').Select(line => GoalCase().Match(line)).Where(match => match.Success)
            .Select(match => match.Groups["tag"].Value)
            .Where(tag => ObligationTags.Contains(tag.Split('.')[0], StringComparer.Ordinal)).ToArray();

    /// <summary>The manifest's methods, in program order, with the sequence points of Symbols.lean.</summary>
    internal static ManifestMethod[] Methods(string output)
    {
        try
        {
            var identity = JsonNode.Parse(File.ReadAllText(Path.Combine(output, "identity.json")));
            var points = Points(output);
            return identity?["methods"]?.AsArray().Select((method, index) => new ManifestMethod(
                method?["signature"]?.GetValue<string>() ?? "",
                method?["instructions"]?.AsArray().Select(line => line?.GetValue<string>() ?? "").ToArray() ?? [],
                points is null ? null : index < points.Length ? points[index] : []))
                .ToArray() ?? [];
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException
            or InvalidOperationException)
        {
            return [];
        }
    }

    // `ExtractedSymbols.points` of the extraction, one line per method in program order; null without symbols.
    static SourcePoint[][]? Points(string output)
    {
        var path = Path.Combine(output, "Symbols.lean");
        if (!File.Exists(path)) return null;
        return File.ReadAllLines(path).SkipWhile(line => !line.StartsWith("def points ", StringComparison.Ordinal))
            .Skip(1).TakeWhile(line => line.StartsWith("  [", StringComparison.Ordinal))
            .Select(line => SymbolPoint().Matches(line).Select(point => new SourcePoint(
                int.Parse(point.Groups["pc"].Value), JsonSerializer.Deserialize<string>(point.Groups["file"].Value)!,
                int.Parse(point.Groups["line"].Value), int.Parse(point.Groups["column"].Value)))
                .OrderBy(point => point.Pc).ToArray())
            .ToArray();
    }

    /// <summary>
    /// The failure records of `messages`, the proof's, keyed by the line and column of the error each explains;
    /// a record with no error explains no failure the report lists.
    /// </summary>
    internal static ILookup<(int Line, int Column), JsonObject> Records(
        IEnumerable<(string Severity, int Line, int Column, string Text)> messages) =>
        messages.Select(message => Record(message.Text))
            .Where(record => record?["error"] is JsonObject)
            .ToLookup(record => (record!["error"]!["line"]!.GetValue<int>(),
                record["error"]!["column"]!.GetValue<int>()), record => record!);

    /// <summary>
    /// The report's failures for `diagnostic`: one per record `CIL.Observe` logged for it, or one with the
    /// diagnostic's facts alone when no LeanCIL tactic recorded it.
    /// </summary>
    internal static IEnumerable<JsonObject> Failures(FailureReports.Diagnostic diagnostic, string proof,
        ManifestMethod[] methods, ILookup<(int Line, int Column), JsonObject> records)
    {
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        var own = diagnostic is { file: { } file, line: { } line, column: { } column } &&
            string.Equals(Path.GetFullPath(file), Path.GetFullPath(proof), comparison)
            ? records[(line, column)].ToArray() : [];
        return own.Length == 0 ? [Failure(diagnostic, methods, null)]
            : own.Select(record => Failure(diagnostic, methods, record));
    }

    /// <summary>
    /// One failure: the diagnostic's established facts, the fields `tactic`, its LeanCIL failure record, reported,
    /// and for every field left null the reason it is unknown. Suggestions are kept in their own field.
    /// </summary>
    internal static JsonObject Failure(FailureReports.Diagnostic diagnostic, ManifestMethod[] methods,
        JsonObject? tactic, string? stageReason = null)
    {
        var unknown = new JsonObject();
        var record = new JsonObject
        {
            ["kind"] = diagnostic.kind,
            ["resource"] = diagnostic.resource,
            ["module"] = diagnostic.module,
            ["source"] = diagnostic.file is null ? null : new JsonObject
            {
                ["file"] = diagnostic.file, ["line"] = diagnostic.line, ["column"] = diagnostic.column
            },
            ["message"] = diagnostic.message,
        };
        if (diagnostic.file is null) unknown["source"] = stageReason ?? "Lean reported no location for this error";
        var obligations = new JsonArray();
        if (tactic is null)
        {
            var listed = diagnostic.kind == FailureReports.UnsolvedGoal ? UnsolvedObligations(diagnostic.message) : [];
            foreach (var tag in listed) obligations.Add(tag);
            record["tactic"] = null;
            record["stopped"] = null;
            record["method"] = null;
            record["cil"] = null;
            record["state"] = null;
            record["missing"] = null;
            record["suggestions"] = new JsonArray();
            var untraced = stageReason ?? (diagnostic.kind == FailureReports.UnsolvedGoal
                ? "the proof left these goals open; no LeanCIL tactic stopped on them"
                : "no LeanCIL tactic raised this error: it is Lean's own, or a tactic's outside the LeanCIL framework");
            foreach (var field in new[] { "tactic", "stopped", "method", "cil", "state", "missing" })
                unknown[field] = untraced;
            if (obligations.Count == 0)
                unknown["obligations"] = diagnostic.kind == FailureReports.UnsolvedGoal
                    ? "no unsolved goal carries a LeanCIL obligation tag" : untraced;
        }
        else
        {
            // The record's field names, as this report places them.
            foreach (var (field, reason) in tactic["unknown"]?.AsObject() ?? [])
                unknown[field switch
                {
                    "instruction" => "cil.leanInstruction",
                    "expected" => "state.expected",
                    "reached" => "state.reached",
                    _ => field
                }] = reason?.DeepClone();
            if (tactic["obligation"]?.GetValue<string>() is { } obligation) obligations.Add(obligation);
            else unknown["obligations"] = unknown["obligation"]?.DeepClone() ?? "the goal carries no obligation tag";
            unknown.Remove("obligation");
            record["tactic"] = tactic["tactic"]?.DeepClone();
            record["stopped"] = tactic["stopped"]?.DeepClone();
            var index = tactic["method"]?.GetValue<int>();
            var pc = tactic["pc"]?.GetValue<int>();
            var known = index is { } i && i >= 0 && i < methods.Length ? methods[i] : null;
            record["method"] = index is null ? null
                : new JsonObject { ["index"] = index, ["signature"] = known?.Signature };
            if (index is not null && known is null)
                unknown["method.signature"] = "the manifest lists no method " + index;
            var line = known is { } method && pc is { } at && at >= 0 && at < method.Instructions.Length
                ? ManifestInstruction().Match(method.Instructions[at]) : null;
            // The C# statement the pc belongs to starts at the last visible sequence point at or before it.
            var point = pc is { } stepped ? known?.Points?.LastOrDefault(point => point.Pc <= stepped) : null;
            record["cil"] = pc is null ? null : new JsonObject
            {
                ["pc"] = pc,
                ["ilOffset"] = line is { Success: true } ? Convert.ToInt32(line.Groups["offset"].Value, 16) : null,
                ["instruction"] = line is { Success: true } ? line.Groups["text"].Value : null,
                ["leanInstruction"] = tactic["instruction"]?.DeepClone(),
                ["source"] = point is null ? null
                    : new JsonObject { ["file"] = point.File, ["line"] = point.Line, ["column"] = point.Column },
            };
            if (pc is not null && line is not { Success: true })
                unknown["cil.ilOffset"] = "the manifest lists no instruction at this method and pc";
            if (pc is not null && point is null)
                unknown["cil.source"] = known is null ? "the manifest lists no method " + index
                    : known.Points is null ? NoSymbols
                    : "the PDB has no visible sequence point at or before this pc in the method";
            if (pc is null)
            {
                unknown["cil"] = unknown["pc"]?.DeepClone() ?? "the tactic reported no pc";
                unknown.Remove("cil.leanInstruction");
            }
            unknown.Remove("pc");
            var reached = tactic["reached"]?.AsObject();
            var expected = tactic["expected"]?.AsObject();
            record["state"] = reached is { Count: > 0 } || expected is { Count: > 0 }
                ? new JsonObject { ["reached"] = reached?.DeepClone(), ["expected"] = expected?.DeepClone() } : null;
            if (record["state"] is null) unknown["state"] ??= "the tactic reported no state";
            record["missing"] = tactic["missing"] is { } shape
                ? new JsonObject { ["shape"] = shape.DeepClone(), ["residual"] = tactic["residual"]?.DeepClone() }
                : null;
            if (record["missing"] is null) unknown["missing"] ??= "the tactic reported no missing fact";
            record["suggestions"] = tactic["suggestions"]?.DeepClone() ?? new JsonArray();
        }
        record["obligations"] = obligations;
        record["unknown"] = unknown;
        return record;
    }

    /// <summary>The report of a run: `verified`, or `failed` with one record per failure, never both.</summary>
    /// <param name="result">`verified` or `failed`.</param>
    /// <param name="failure">The failure behind a `failed` result; null when the run verified.</param>
    /// <param name="theorem">The theorem the run checked.</param>
    /// <param name="proof">The proof file, which every located message and failure names.</param>
    /// <param name="output">The extraction the proof was checked against.</param>
    /// <param name="proofRoot">The proof root the rerun command passes, if the run had one.</param>
    /// <param name="stage">The stage the run reached or failed at.</param>
    /// <param name="axioms">The theorem's axioms, when the proof was checked far enough to read them.</param>
    /// <param name="statement">The theorem's statement, when it was read.</param>
    /// <param name="messages">The proof's informational and warning messages, failure records and trace included.
    /// </param>
    /// <param name="traceRequested">Whether `--trace` asked for each step the proof took.</param>
    /// <param name="proofChecked">Whether Lean checked the proof, so its trace messages exist.</param>
    /// <param name="goalsRequested">Whether `--goals` asked for the goal at each `sorry` and failing tactic.</param>
    /// <param name="specification">The proof module's definitions the statement is stated with, when read.</param>
    internal static JsonObject Result(string result, FailureReports.Report? failure, string theorem, string proof,
        string output, string? proofRoot, string? stage, string[]? axioms, string? statement,
        IEnumerable<(string Severity, int Line, int Column, string Text)> messages, bool traceRequested = false,
        bool proofChecked = true, bool goalsRequested = false,
        IEnumerable<(string Name, string Text)>? specification = null)
    {
        var all = messages.ToArray();
        var methods = Methods(output);
        var records = Records(all);
        var failures = new JsonArray();
        if (failure is not null)
        {
            if (failure.diagnostics.Length > 0)
                foreach (var diagnostic in failure.diagnostics)
                    foreach (var entry in Failures(diagnostic, proof, methods, records)) failures.Add(entry);
            else
            {
                failures.Add(Failure(new(failure.kind, failure.resource, failure.module, failure.file, failure.line,
                    failure.column, failure.message), methods, null,
                    $"the failure is at the {failure.stage} stage, not in a Lean error"));
            }
        }
        var method = failure?.method ?? FailureReports.MethodOf(output);
        JsonObject Located((string Severity, int Line, int Column, string Text) message, bool severity) => new()
        {
            ["file"] = proof, ["line"] = message.Line, ["column"] = message.Column,
            ["severity"] = severity ? message.Severity : null, ["text"] = message.Text
        };
        var unknown = new JsonObject();
        if (!traceRequested || !proofChecked)
            unknown["trace"] = traceRequested ? "the proof was not checked, so no step was traced"
                : "not requested; --trace traces each step the proof takes";
        if (!goalsRequested || !proofChecked)
            unknown["goals"] = goalsRequested ? "the proof was not checked, so no goal was read"
                : "not requested; --goals reports the goal at each sorry and failing tactic";
        return new JsonObject
        {
            ["schema"] = Schema,
            ["result"] = result,
            ["stage"] = stage,
            ["theorem"] = theorem,
            ["method"] = method is null ? null : JsonSerializer.SerializeToNode(method),
            ["proof"] = proof,
            ["output"] = output,
            ["axioms"] = axioms is null ? null : new JsonArray([.. axioms.Select(axiom => (JsonNode?)axiom)]),
            ["statement"] = statement,
            // The definitions of the proof module the statement names, as Lean prints their elaborated bodies.
            ["specification"] = specification is null ? null : new JsonArray([.. specification.Select(definition =>
                (JsonNode?)new JsonObject { ["name"] = definition.Name, ["text"] = definition.Text })]),
            ["failures"] = failures,
            // The proof's own messages; the observer's records are in `failures`, its steps in `trace` and
            // the open goals in `goals`.
            ["messages"] = new JsonArray([.. all.Where(message => Record(message.Text) is null &&
                    !(traceRequested && IsStep(message.Text)) && !(goalsRequested && Goal(message.Text) is not null))
                .Select(message => (JsonNode?)Located(message, true))]),
            // Each goal at a `sorry`, before a failing tactic or left unsolved, as `CIL.Observe` logged it.
            ["goals"] = !goalsRequested || !proofChecked ? null
                : new JsonArray([.. all.Where(message => Goal(message.Text) is not null).Select(message =>
                {
                    var (kind, goal) = Goal(message.Text)!.Value;
                    return (JsonNode?)new JsonObject
                    {
                        ["file"] = proof, ["line"] = message.Line, ["column"] = message.Column,
                        ["kind"] = kind, ["goal"] = goal
                    };
                })]),
            // Each step the proof took, as `CIL.Observe` traced it under `--trace`.
            ["trace"] = !traceRequested || !proofChecked ? null
                : new JsonArray([.. all.Where(message => IsStep(message.Text)).Select(message =>
                {
                    var step = Located(message, false);
                    step.Remove("severity");
                    return (JsonNode?)step;
                })]),
            ["unknown"] = unknown,
            ["rerun"] = new JsonArray([.. FailureReports.Rerun(theorem, proof, output, proofRoot)
                .Concat(["--format", "json", .. traceRequested ? ["--trace"] : Array.Empty<string>(),
                    .. goalsRequested ? ["--goals"] : Array.Empty<string>()])
                .Select(argument => (JsonNode?)argument)]),
        };
    }

    internal static string Serialize(JsonNode report) => report.ToJsonString(Json) + "\n";
}
