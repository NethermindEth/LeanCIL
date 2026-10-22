using System.Text.Encodings.Web;
using System.Text.Json;
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
    internal const string Unclassified = "unclassified";

    internal sealed record Method(string entry, string assembly, string assemblySha256);
    internal sealed record Diagnostic(string kind, string? resource, string? module, string? file, int? line, int? column, string message);
    internal sealed record Report(int schema, string kind, string? resource, string stage, string theorem, string module,
        string proof, string output, Method? method, string? file, int? line, int? column, Diagnostic[] diagnostics,
        string message, string[] rerun);

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

    [GeneratedRegex(@"^LeanCIL refutes: (?<name>\S+) at (?<line>\d+):(?<column>\d+)\r?$", RegexOptions.Multiline)]
    private static partial Regex RefutationMarker();

    [GeneratedRegex(@"\A(?<file>.+?\.lean):(?<line>\d+):(?<column>\d+)\z")]
    private static partial Regex Location();

    // The stage line of a nested `leancil check` diagnostic.
    [GeneratedRegex(@"^  Stage: (?<stage>.+?)\r?$", RegexOptions.Multiline)]
    private static partial Regex ChildStage();

    // Workspace copies of the selected proof, line for line.
    [GeneratedRegex(@"\ALeanCILProof\d*\z")]
    private static partial Regex ProofModule();

    internal static Report Failed(string stage, Exception error, string theorem, string proof, string output, string? proofRoot) =>
        Classify(stage, error.Message, error.Data[LeanDiagnostics.HiddenModulesKey] as string[], theorem, proof, output, proofRoot);

    internal static Report Classify(string stage, string message, IReadOnlyCollection<string>? hidden, string theorem,
        string proof, string output, string? proofRoot)
    {
        var module = ModuleOf(proof, proofRoot);
        var diagnostics = LeanDiagnostics.Errors(message, hidden).Select(error =>
        {
            var (kind, resource) = KindOf(stage, error.Lines[0]);
            var (file, line, column) = Place(error, proof, output, proofRoot);
            var origin = error.Module is { } name && ProofModule().IsMatch(name) ? module : error.Module;
            return new Diagnostic(kind, resource, origin ?? (file == proof ? module : null), file, line, column, string.Join("\n", error.Lines));
        }).ToArray();
        string requestKind;
        string? requestResource = null;
        if (stage == "extraction integrity")
            requestKind = ChildStage().Match(message) is { Success: true } child && child.Groups["stage"].Value == "metadata and CIL validation"
                ? UnsupportedExtraction : StaleInput;
        else if (diagnostics.Length > 0)
            (requestKind, requestResource) = (diagnostics[0].kind, diagnostics[0].resource);
        else if (StaleMarkers.Any(marker => message.Contains(marker, StringComparison.Ordinal)))
            requestKind = StaleInput;
        else
            requestKind = stage switch
            {
                "kernel replay" or "theorem audit" => ReplayOrAuditRejected,
                "proof selection" => InvalidRequest,
                _ => Unclassified
            };
        var first = diagnostics.FirstOrDefault();
        return new(1, requestKind, requestResource, stage, theorem, module, proof, output, MethodOf(output),
            first?.file, first?.line, first?.column, diagnostics, message, Rerun(theorem, proof, output, proofRoot));
    }

    /// <summary>A refutation report when the audit marks the verified theorem as `Not (contract.Holds ...)`, else null.</summary>
    internal static Report? Refuted(string audit, string theorem, string proof, string output, string? proofRoot)
    {
        var markers = RefutationMarker().Matches(audit);
        if (markers.Count != 1) return null;
        var marker = markers[0];
        return new(1, Refutation, null, "theorem audit", theorem, ModuleOf(proof, proofRoot), proof, output, MethodOf(output),
            proof, int.Parse(marker.Groups["line"].Value), int.Parse(marker.Groups["column"].Value), [], audit,
            Rerun(theorem, proof, output, proofRoot));
    }

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

    // Maps workspace and temporary copies back to the files the user edits.
    static (string? File, int? Line, int? Column) Place(LeanDiagnostics.Diagnostic error, string proof, string output, string? proofRoot)
    {
        if (error.Location is null) return (null, null, null);
        var match = Location().Match(error.Location);
        if (!match.Success) return (error.Location, null, null);
        var file = match.Groups["file"].Value;
        var name = file.Replace('\\', '/').Split('/')[^1][..^".lean".Length];
        var mapped = (error.Module is { } module && ProofModule().IsMatch(module)) || ProofModule().IsMatch(name) ||
            (proofRoot is null && name == "Proof") ? proof
            : name == "Extracted" ? Path.Combine(output, "Extracted.lean")
            : proofRoot is not null && !Path.IsPathRooted(file) ? Path.GetFullPath(file, proofRoot) : file;
        return (mapped, int.Parse(match.Groups["line"].Value), int.Parse(match.Groups["column"].Value));
    }

    static string ModuleOf(string proof, string? proofRoot) => proofRoot is null ? "Proof"
        : Path.GetRelativePath(proofRoot, proof).Replace('\\', '/')[..^".lean".Length].Replace('/', '.');

    static Method? MethodOf(string output)
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

    static string[] Rerun(string theorem, string proof, string output, string? proofRoot) =>
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
