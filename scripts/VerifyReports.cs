using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

// The opt-in machine-readable result of `leancil verify --format json`: established facts only, read from
// FailureReports' taxonomy, the failure records LeanCIL tactics append and the integrity-checked manifest.
internal static partial class VerifyReports
{
    /// <summary>The version of the report's shape; a change that removes or renames a field increments it.</summary>
    internal const int Schema = 1;

    /// <summary>`CIL.Safety.failureMarker`, starting the line a tactic appends under `cil.diagnostics`.</summary>
    internal const string FailureMarker = "[LeanCIL failure v1] ";

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

    /// <summary>A message with its failure records split off, each parsed from its JSON line.</summary>
    internal static (string Message, JsonObject[] Records) SplitRecords(string message)
    {
        var records = new List<JsonObject>();
        var kept = new List<string>();
        foreach (var line in message.Split('\n'))
        {
            if (line.StartsWith(FailureMarker, StringComparison.Ordinal) &&
                JsonNode.Parse(line[FailureMarker.Length..]) is JsonObject record)
                records.Add(record);
            else kept.Add(line);
        }
        return (string.Join('\n', kept), [.. records]);
    }

    /// <summary>The obligation tags of the goals an `unsolved goals` message lists, checked against the tags.</summary>
    internal static string[] UnsolvedObligations(string message) =>
        message.Split('\n').Select(line => GoalCase().Match(line)).Where(match => match.Success)
            .Select(match => match.Groups["tag"].Value)
            .Where(tag => ObligationTags.Contains(tag.Split('.')[0], StringComparer.Ordinal)).ToArray();

    /// <summary>A method of the manifest: its signature and its instructions by pc, as `IL_0002: add`.</summary>
    internal sealed record ManifestMethod(string Signature, string[] Instructions);

    /// <summary>The manifest's methods, in program order.</summary>
    internal static ManifestMethod[] Methods(string output)
    {
        try
        {
            var identity = JsonNode.Parse(File.ReadAllText(Path.Combine(output, "identity.json")));
            return identity?["methods"]?.AsArray().Select(method => new ManifestMethod(
                method?["signature"]?.GetValue<string>() ?? "",
                method?["instructions"]?.AsArray().Select(line => line?.GetValue<string>() ?? "").ToArray() ?? []))
                .ToArray() ?? [];
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException
            or InvalidOperationException)
        {
            return [];
        }
    }

    /// <summary>
    /// One failure record: the diagnostic's established facts, the fields a LeanCIL tactic reported, and for every
    /// field left null the reason it is unknown. Suggestions are kept in their own field.
    /// </summary>
    internal static JsonObject Failure(FailureReports.Diagnostic diagnostic,
        ManifestMethod[] methods, string? stageReason = null)
    {
        var (message, records) = SplitRecords(diagnostic.message);
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
            ["message"] = message,
        };
        if (diagnostic.file is null) unknown["source"] = stageReason ?? "Lean reported no location for this error";
        var tactic = records.LastOrDefault();
        var obligations = new JsonArray();
        if (tactic is null)
        {
            foreach (var tag in diagnostic.kind == FailureReports.UnsolvedGoal ? UnsolvedObligations(message) : [])
                obligations.Add(tag);
            record["tactic"] = null;
            record["method"] = null;
            record["cil"] = null;
            record["state"] = null;
            record["missing"] = null;
            record["suggestions"] = new JsonArray();
            var untraced = stageReason ?? (diagnostic.kind == FailureReports.UnsolvedGoal
                ? "the proof left these goals open; no LeanCIL tactic stopped on them"
                : "the error carries no LeanCIL failure record: it is Lean's own error, or comes from a tactic " +
                    "that does not report one");
            foreach (var field in new[] { "tactic", "method", "cil", "state", "missing" }) unknown[field] = untraced;
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
            var index = tactic["method"]?.GetValue<int>();
            var pc = tactic["pc"]?.GetValue<int>();
            var known = index is { } i && i >= 0 && i < methods.Length ? methods[i] : null;
            record["method"] = index is null ? null
                : new JsonObject { ["index"] = index, ["signature"] = known?.Signature };
            if (index is not null && known is null)
                unknown["method.signature"] = "the manifest lists no method " + index;
            var line = known is { } method && pc is { } at && at >= 0 && at < method.Instructions.Length
                ? ManifestInstruction().Match(method.Instructions[at]) : null;
            record["cil"] = pc is null ? null : new JsonObject
            {
                ["pc"] = pc,
                ["ilOffset"] = line is { Success: true } ? Convert.ToInt32(line.Groups["offset"].Value, 16) : null,
                ["instruction"] = line is { Success: true } ? line.Groups["text"].Value : null,
                ["leanInstruction"] = tactic["instruction"]?.DeepClone(),
            };
            if (pc is not null && line is not { Success: true })
                unknown["cil.ilOffset"] = "the manifest lists no instruction at this method and pc";
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
    internal static JsonObject Result(string result, FailureReports.Report? failure, string theorem, string proof,
        string output, string? proofRoot, string? stage, string[]? axioms, string? statement,
        IEnumerable<(string Severity, int Line, int Column, string Text)> messages)
    {
        var methods = Methods(output);
        var failures = new JsonArray();
        if (failure is not null)
        {
            if (failure.diagnostics.Length > 0)
                foreach (var diagnostic in failure.diagnostics) failures.Add(Failure(diagnostic, methods));
            else
            {
                failures.Add(Failure(new(failure.kind, failure.resource, failure.module, failure.file, failure.line,
                    failure.column, failure.message), methods,
                    $"the failure is at the {failure.stage} stage, not in a Lean error"));
            }
        }
        var method = failure?.method ?? FailureReports.MethodOf(output);
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
            ["failures"] = failures,
            ["messages"] = new JsonArray([.. messages.Select(message => (JsonNode?)new JsonObject
            {
                ["file"] = proof, ["line"] = message.Line, ["column"] = message.Column,
                ["severity"] = message.Severity, ["text"] = message.Text
            })]),
            ["rerun"] = new JsonArray([.. FailureReports.Rerun(theorem, proof, output, proofRoot)
                .Concat(["--format", "json"]).Select(argument => (JsonNode?)argument)]),
        };
    }

    internal static string Serialize(JsonObject report) => report.ToJsonString(Json) + "\n";
}
