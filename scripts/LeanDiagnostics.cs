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

    [GeneratedRegex(@"^(?<level>error|warning|info|trace): (?<message>.*)$")]
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
            var job = LeanOutput.Job().Match(line);
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

    /// <summary>Each `level: message` entry Lake logged, with the lines its message continues on.</summary>
    internal static IEnumerable<(string Level, string Message)> Entries(string output)
    {
        var lines = output.Replace("\r\n", "\n").Split('\n');
        for (var i = 0; i < lines.Length; i++)
        {
            var entry = Entry().Match(lines[i]);
            if (!entry.Success) continue;
            var block = new List<string> { entry.Groups["message"].Value };
            while (i + 1 < lines.Length && !IsBoundary(lines[i + 1])) block.Add(lines[++i]);
            while (block.Count > 1 && block[^1].Trim().Length == 0) block.RemoveAt(block.Count - 1);
            yield return (entry.Groups["level"].Value, string.Join('\n', block));
        }
    }

    static bool IsBoundary(string line) => LeanOutput.Job().IsMatch(line) || Entry().IsMatch(line) ||
        LeanEntry().IsMatch(line) || FailureList().IsMatch(line) ||
        line.StartsWith("Build completed", StringComparison.Ordinal);

    /// <summary>
    /// A bounded summary of the error diagnostics, and in full only the errors it cut or left out, so a report
    /// prints each error once.
    /// `locate` rewrites each `file:line:column` and `module` each module name, such as to a session copy's original.
    /// </summary>
    internal sealed record Report(string Text, string Shortened);

    /// <summary>
    /// The <see cref="Report"/> of the internal errors and the error diagnostics in `output`, internal errors
    /// first, or null when it has neither.
    /// </summary>
    internal static Report? Summarize(string output, IReadOnlyCollection<string>? hidden = null,
        Func<string, string>? locate = null, Func<string, string>? module = null)
    {
        var errors = Errors(output, hidden);
        var internalErrors = LeanOutput.InternalErrors(output, hidden).GroupBy(error => error).ToArray();
        if (errors.Count == 0 && internalErrors.Length == 0) return null;
        var text = new StringBuilder();
        if (internalErrors.Length > 0) text.Append($"Internal errors ({internalErrors.Length}):\n");
        foreach (var group in internalErrors)
        {
            var (count, error) = (group.Count(), group.Key);
            text.Append("  ").Append(error.Location is { } location ? locate?.Invoke(location) ?? location : "output")
                .Append(error.Module is { } name ? $" (building {module?.Invoke(name) ?? name})" : "").Append('\n')
                .Append("    ").Append(error.Message).Append(count > 1 ? $" ({count} times)" : "").Append('\n');
        }
        if (errors.Count > 0) text.Append($"Lean errors ({errors.Count}):\n");
        var shortened = new StringBuilder();
        string Header(Diagnostic error) =>
            (error.Location is { } location ? locate?.Invoke(location) ?? location : "error") +
            (error.Module is { } name ? $" (building {module?.Invoke(name) ?? name})" : "");
        for (var index = 0; index < errors.Count; index++)
        {
            var error = errors[index];
            var cut = index >= MaxErrors || error.Lines.Count > MaxLines ||
                error.Lines.Any(line => line.Length > MaxLineLength);
            if (cut)
                shortened.Append(Header(error)).Append('\n').AppendJoin('\n', error.Lines).Append('\n');
            if (index >= MaxErrors) continue;
            text.Append("  ").Append(Header(error)).Append('\n');
            foreach (var line in error.Lines.Take(MaxLines))
                text.Append("    ").Append(line.Length <= MaxLineLength ? line : line[..MaxLineLength] + " ...").Append('\n');
            if (error.Lines.Count > MaxLines)
                text.Append($"    ... {error.Lines.Count - MaxLines} more lines under Details\n");
        }
        if (errors.Count > MaxErrors)
            text.Append($"  ... {errors.Count - MaxErrors} more errors under Details\n");
        return new(text.ToString(), shortened.ToString());
    }
}
