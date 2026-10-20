using System.Text;
using System.Text.RegularExpressions;

// Presentation only: verification outcomes never depend on this summary.
internal static partial class LeanDiagnostics
{
    internal const int MaxErrors = 20;
    internal const int MaxLines = 40;
    internal const int MaxLineLength = 400;

    // Exception.Data key naming the proof modules of other requests in a shared workspace.
    internal const string HiddenModulesKey = "LeanCIL.HiddenModules";

    // Lake job headers: failed, warned, informational and built.
    [GeneratedRegex(@"^(?:\u2716|\u26A0|\u2139|\u2714) \[\d+/\d+\] \S+ (?<module>\S+)")]
    private static partial Regex Job();

    [GeneratedRegex(@"^(?:error|warning|info|trace): ")]
    private static partial Regex Entry();

    [GeneratedRegex(@"^error: (?:(?<location>.+?\.lean:\d+:\d+): )?(?<message>.*)$")]
    private static partial Regex LakeError();

    [GeneratedRegex(@"^(?<location>.+?\.lean:\d+:\d+): error: (?<message>.*)$")]
    private static partial Regex LeanError();

    [GeneratedRegex(@"^.+?\.lean:\d+:\d+: (?:error|warning|info): ")]
    private static partial Regex LeanEntry();

    [GeneratedRegex(@"^Some required (?:targets|builds) logged failures:")]
    private static partial Regex FailureList();

    [GeneratedRegex(@"^(?:build failed|Lean exited with code \d+)$")]
    private static partial Regex Boilerplate();

    internal sealed record Diagnostic(string? Module, string? Location, IReadOnlyList<string> Lines);

    /// <summary>Every error diagnostic in Lake or Lean output, each with its full message block.</summary>
    internal static List<Diagnostic> Errors(string output, IReadOnlyCollection<string>? hidden = null)
    {
        var lines = output.Replace("\r\n", "\n").Split('\n');
        var result = new List<Diagnostic>();
        string? module = null;
        for (var i = 0; i < lines.Length; i++)
        {
            var line = lines[i];
            var job = Job().Match(line);
            if (job.Success) { module = job.Groups["module"].Value; continue; }
            if (FailureList().IsMatch(line)) { module = null; continue; }
            var match = LakeError().Match(line);
            if (!match.Success) match = LeanError().Match(line);
            if (!match.Success) continue;
            var location = match.Groups["location"].Success ? match.Groups["location"].Value : null;
            var message = match.Groups["message"].Value;
            var block = new List<string> { message };
            while (i + 1 < lines.Length && !IsBoundary(lines[i + 1])) block.Add(lines[++i]);
            while (block.Count > 1 && block[^1].Trim().Length == 0) block.RemoveAt(block.Count - 1);
            if (location is null && block.Count == 1 && Boilerplate().IsMatch(message)) continue;
            if (module is not null && hidden?.Contains(module) == true) continue;
            result.Add(new(module, location, block));
        }
        return result;
    }

    static bool IsBoundary(string line) => Job().IsMatch(line) || Entry().IsMatch(line) || LeanEntry().IsMatch(line) ||
        FailureList().IsMatch(line) || line.StartsWith("Build completed", StringComparison.Ordinal);

    /// <summary>A bounded summary of the error diagnostics, or null when the output has none.</summary>
    internal static string? Summarize(string output, IReadOnlyCollection<string>? hidden = null)
    {
        var errors = Errors(output, hidden);
        if (errors.Count == 0) return null;
        var text = new StringBuilder($"Lean errors ({errors.Count}):\n");
        foreach (var error in errors.Take(MaxErrors))
        {
            var origin = error.Module is null ? "" : $" (building {error.Module})";
            text.Append("  ").Append(error.Location ?? "error").Append(origin).Append('\n');
            foreach (var line in error.Lines.Take(MaxLines))
                text.Append("    ").Append(line.Length <= MaxLineLength ? line : line[..MaxLineLength] + " ...").Append('\n');
            if (error.Lines.Count > MaxLines)
                text.Append($"    ... {error.Lines.Count - MaxLines} more lines in the full output\n");
        }
        if (errors.Count > MaxErrors)
            text.Append($"  ... {errors.Count - MaxErrors} more errors in the full output\n");
        return text.ToString();
    }
}
