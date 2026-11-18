using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;

// Deterministic failure taxonomy from the stage, LeanCIL's own messages and Lean's stable error prefixes.
internal static partial class FailureReports
{
    internal const string FileName = "failed.json";
    internal const string UnsupportedExtraction = "unsupported-extraction";
    internal const string StaleInput = "stale-input";
    internal const string ElaborationError = "elaboration-error";
    internal const string UnsolvedGoal = "unsolved-goal";
    internal const string ResourceLimit = "resource-limit";
    internal const string ReplayOrAuditRejected = "replay-or-audit-rejected";
    internal const string Refutation = "refutation";
    internal const string InvalidRequest = "invalid-request";
    internal const string InternalError = "internal-error";
    internal const string Unclassified = "unclassified";

    internal sealed record Method(string entry, string assembly, string assemblySha256);
    internal sealed record Diagnostic(string kind, string? resource, string? module, string? file, int? line, int? column, string message);
    internal sealed record Report(int schema, string kind, string? resource, string stage, string theorem, string module,
        string proof, string output, Method? method, string? file, int? line, int? column, Diagnostic[] diagnostics,
        string message, string[] rerun,
        [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] BindingFailure? binding = null);

    /// <summary>A failed attempt can identify a rejected check or an incomplete check.</summary>
    [JsonConverter(typeof(BindingFailureStatusNames))]
    internal enum BindingFailureStatus { NotCovered, Failed }

    sealed class BindingFailureStatusNames : JsonConverter<BindingFailureStatus>
    {
        public override BindingFailureStatus Read(ref Utf8JsonReader reader, Type type,
            JsonSerializerOptions options) => reader.TokenType == JsonTokenType.String
            ? reader.GetString() switch
            {
                "not covered" => BindingFailureStatus.NotCovered,
                "failed" => BindingFailureStatus.Failed,
                _ => throw new JsonException("Expected not covered or failed")
            }
            : throw new JsonException("Expected a binding failure status string");

        public override void Write(Utf8JsonWriter writer, BindingFailureStatus value,
            JsonSerializerOptions options) => writer.WriteStringValue(value switch
            {
                BindingFailureStatus.NotCovered => "not covered",
                BindingFailureStatus.Failed => "failed",
                _ => throw new JsonException("Invalid binding failure status")
            });
    }

    internal sealed record BindingFailureDigest(string path, string sha256);
    internal sealed record BindingFailureImage(string identity, string sha256,
        BindingFailureStatus status, string reason);
    internal sealed record BindingFailureFact(string id, BindingFailureStatus status, string reason);
    internal sealed record BindingFailure(BindingFailureDigest digests, BindingFailureImage[] images,
        BindingFailureFact[] facts);

    // Elaborator and kernel exhaustion messages.
    static readonly (string Prefix, string Resource)[] Resources =
    [
        ("(deterministic) timeout", "heartbeats"), ("(kernel) deterministic timeout", "heartbeats"),
        ("maximum recursion depth has been reached", "recursion"), ("(kernel) deep recursion detected", "recursion")
    ];

    // LeanCIL's messages for inputs that changed after extraction or during verification.
    static readonly string[] StaleMarkers =
    [
        "Stale or mismatched verification artifact", "Stale verification report", "Inputs changed during",
        "Sources changed in the fresh consumer build", "Compiled artifacts changed during", "Generated CIL changed during",
        "PDB names changed during", "Consumer source changed during"
    ];

    static readonly JsonSerializerOptions Json = new() { WriteIndented = true, Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };

    [GeneratedRegex(@"\A(?<file>.+?\.lean):(?<line>\d+):(?<column>\d+)\z")]
    private static partial Regex Location { get; }

    // The stage line of a nested `leancil check` diagnostic.
    [GeneratedRegex(@"^  Stage: (?<stage>.+?)\r?$", RegexOptions.Multiline)]
    private static partial Regex ChildStage { get; }

    // Workspace copies of the selected proof, line for line.
    [GeneratedRegex(@"\ALeanCILProof\d*\z")]
    private static partial Regex ProofModule { get; }

    internal static Report Failed(string stage, Exception error, string theorem, string proof, string output, string? proofRoot) =>
        Classify(stage, error.Message, error.Data[LeanDiagnostics.HiddenModulesKey] as string[], theorem, proof, output,
            proofRoot, error.Data[SourceCopies.Key] as SourceCopies);

    internal static Report Classify(string stage, string message, IReadOnlyCollection<string>? hidden, string theorem,
        string proof, string output, string? proofRoot, SourceCopies? copies = null)
    {
        var module = ModuleOf(proof, proofRoot);
        // Internal errors lead: after one, a tactic ran on a default value and no later diagnostic is reliable.
        var internalErrors = LeanOutput.InternalErrors(message, hidden).Distinct().Select(error =>
        {
            var (file, line, column) = Place(error.Location, copies);
            var origin = error.Module is { } name && ProofModule.IsMatch(name) ? module : error.Module;
            return new Diagnostic(InternalError, null, origin ?? (file == proof ? module : null), file, line, column,
                error.Message);
        });
        var diagnostics = internalErrors.Concat(LeanDiagnostics.Errors(message, hidden).Select(error =>
        {
            var (kind, resource) = KindOf(stage, error.Lines[0]);
            var (file, line, column) = Place(error.Location, copies);
            var origin = error.Module is { } name && ProofModule.IsMatch(name) ? module : error.Module;
            return new Diagnostic(kind, resource, origin ?? (file == proof ? module : null), file, line, column, string.Join("\n", error.Lines));
        })).ToArray();
        string requestKind;
        string? requestResource = null;
        if (diagnostics.Length > 0 && diagnostics[0].kind == InternalError)
            requestKind = InternalError;
        else if (stage == "extraction integrity")
            requestKind = ChildStage.Match(message) is { Success: true } child && child.Groups["stage"].Value == "metadata and CIL validation"
                ? UnsupportedExtraction : StaleInput;
        else if (diagnostics.Length > 0)
            (requestKind, requestResource) = (diagnostics[0].kind, diagnostics[0].resource);
        else if (StaleMarkers.Any(marker => message.Contains(marker, StringComparison.Ordinal)))
            requestKind = StaleInput;
        else
            requestKind = stage switch
            {
                "kernel replay" or "theorem audit" => ReplayOrAuditRejected,
                "proof selection" or "arguments" => InvalidRequest,
                "open goals" => UnsolvedGoal,
                _ => Unclassified
            };
        var first = diagnostics.FirstOrDefault();
        return new(1, requestKind, requestResource, stage, theorem, module, proof, output, MethodOf(output),
            first?.file, first?.line, first?.column, diagnostics, message, Rerun(theorem, proof, output, proofRoot));
    }

    /// <summary>
    /// A refutation report when the audit found the verified theorem to state a contract's `Refuted`, else null;
    /// `audit` is shown as the message and decides nothing.
    /// </summary>
    internal static Report? Refuted(Program.AuditRefutation? refutation, string audit, string theorem, string proof,
        string output, string? proofRoot) =>
        refutation is null ? null
            : new(1, Refutation, null, "theorem audit", theorem, ModuleOf(proof, proofRoot), proof, output,
                MethodOf(output), proof, refutation.line, refutation.column, [], audit,
                Rerun(theorem, proof, output, proofRoot));

    static (string Kind, string? Resource) KindOf(string stage, string first)
    {
        foreach (var (prefix, resource) in Resources)
            if (first.StartsWith(prefix, StringComparison.Ordinal)) return (ResourceLimit, resource);
        return stage switch
        {
            "extraction certificate audit" => (UnsupportedExtraction, null),
            "kernel replay" or "theorem audit" => (ReplayOrAuditRejected, null),
            _ => (first.StartsWith("unsolved goals", StringComparison.Ordinal) ? UnsolvedGoal : ElaborationError, null)
        };
    }

    // A location in a file the session copied cites the original the user edits; any other keeps its printed path.
    static (string? File, int? Line, int? Column) Place(string? location, SourceCopies? copies)
    {
        if (location is null) return (null, null, null);
        var match = Location.Match(location);
        if (!match.Success) return (location, null, null);
        var (file, line, column) = (match.Groups["file"].Value, int.Parse(match.Groups["line"].Value),
            int.Parse(match.Groups["column"].Value));
        return copies?.Position(file, line, column) ?? (file, line, column);
    }

    static string ModuleOf(string proof, string? proofRoot) => proofRoot is null ? "Proof"
        : Path.GetRelativePath(proofRoot, proof).Replace('\\', '/')[..^".lean".Length].Replace('/', '.');

    internal static Method? MethodOf(string output)
    {
        try
        {
            var identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
            return new(identity.GetProperty("entry").GetString()!, identity.GetProperty("assemblyIdentity").GetString()!,
                identity.GetProperty("assemblySha256").GetString()!);
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or JsonException or KeyNotFoundException or InvalidOperationException)
        {
            return null;
        }
    }

    internal static string[] Rerun(string theorem, string proof, string output, string? proofRoot) =>
        ["leancil", "verify", output, "--proof", proof, "--theorem", theorem, .. proofRoot is null ? Array.Empty<string>() : ["--proof-root", proofRoot]];

    internal static void Write(string output, Report report)
    {
        if (Directory.Exists(output)) File.WriteAllText(Path.Combine(output, FileName), JsonSerializer.Serialize(report, Json) + "\n");
    }

    internal static void Delete(string output)
    {
        if (Directory.Exists(output)) File.Delete(Path.Combine(output, FileName));
    }
}
