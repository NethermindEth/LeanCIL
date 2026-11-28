using System.Globalization;
using System.Text.Json;
using System.Text.Json.Nodes;

internal static class VerificationTimings
{
    internal static readonly JsonSerializerOptions Json = new() { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.CamelCase };

    internal sealed record Stage(string Suite, string StageName, int Count, double DurationSeconds, double MaxSeconds, int Failures);

    internal static List<JsonObject> Collect(string root)
    {
        var records = new List<JsonObject>();
        if (!Directory.Exists(root)) return records;
        foreach (var path in Directory.EnumerateFiles(root, "*.jsonl", SearchOption.AllDirectories).Order(StringComparer.Ordinal))
        {
            var lineNumber = 0;
            foreach (var line in File.ReadLines(path))
            {
                lineNumber++;
                if (string.IsNullOrWhiteSpace(line)) continue;
                try
                {
                    var record = JsonNode.Parse(line) as JsonObject ?? throw new FormatException("Expected an object");
                    var duration = record["durationSeconds"]?.GetValue<double>() ?? throw new FormatException("Missing duration");
                    var exit = record["exitCode"]?.ToJsonString() ?? "";
                    if (!double.IsFinite(duration) || duration < 0 || exit.Length == 0 ||
                        !exit.TrimStart('-').All(char.IsAsciiDigit) || exit == "-" ||
                        record["stage"] is not JsonValue stage || !stage.TryGetValue<string>(out _) ||
                        record["transcript"] is not JsonValue transcript || !transcript.TryGetValue<string>(out _) ||
                        record["suite"] is not null && (record["suite"] is not JsonValue suite || !suite.TryGetValue<string>(out _)) ||
                        record["command"] is not JsonArray command || command.Any(part => part is not JsonValue value || !value.TryGetValue<string>(out _)))
                        throw new FormatException("Invalid stage record");
                    record["suite"] = record["suite"]?.GetValue<string>() is { Length: > 0 } name ? name : "local";
                    record["traceFile"] = Path.GetRelativePath(root, path).Replace('\\', '/');
                    record["traceLine"] = lineNumber;
                    records.Add(record);
                }
                catch (Exception error) when (error is JsonException or InvalidOperationException or FormatException)
                {
                    throw new FormatException($"{path}:{lineNumber}: invalid timing record: {error.Message}", error);
                }
            }
        }
        return records;
    }

    internal static List<Stage> Summarize(IEnumerable<JsonObject> records) => records
        .GroupBy(record => (Suite: record["suite"]!.GetValue<string>(), Name: record["stage"]!.GetValue<string>()))
        .Select(group => new Stage(group.Key.Suite, group.Key.Name, group.Count(),
            group.Sum(record => record["durationSeconds"]!.GetValue<double>()),
            group.Max(record => record["durationSeconds"]!.GetValue<double>()),
            group.Count(record => record["exitCode"]!.ToJsonString() is not ("0" or "-0"))))
        .OrderByDescending(group => group.DurationSeconds).ThenBy(group => group.Suite, StringComparer.Ordinal)
        .ThenBy(group => group.StageName, StringComparer.Ordinal).ToList();

    internal static string Markdown(IReadOnlyList<Stage> groups, int count)
    {
        static string Cell(string value) => value.Replace("&", "&amp;").Replace("<", "&lt;").Replace(">", "&gt;")
            .Replace("\"", "&quot;").Replace("'", "&#x27;").Replace("|", "\\|").Replace('\n', ' ').Replace('\r', ' ');
        var lines = new List<string>
        {
            "## Verification stage timings", "",
            $"{count} completed stages. Durations are inclusive: parent suite commands overlap child stages, so these totals must not be added to estimate wall time.", "",
            "Full command transcripts and all timing records are retained in the verification artifacts. Combined reports include retained rerun attempts; each record identifies its source artifact."
        };
        if (groups.Count > 0)
        {
            lines.AddRange(["", "Longest accumulated stages (up to 20):", "",
                "| Suite | Stage | Calls | Inclusive seconds | Longest call | Nonzero exits |",
                "| --- | --- | ---: | ---: | ---: | ---: |"]);
            foreach (var group in groups.Take(20))
                lines.Add(string.Create(CultureInfo.InvariantCulture, $"| {Cell(group.Suite)} | {Cell(group.StageName)} | {group.Count} | {group.DurationSeconds:F1} | {group.MaxSeconds:F1} | {group.Failures} |"));
            lines.AddRange(["", "Nonzero exits include intentionally rejected negative tests; the suite job result determines success."]);
        }
        else lines.AddRange(["", "No completed stage timings were available; inspect the job log and any partial transcripts."]);
        return string.Join('\n', lines) + "\n";
    }

    internal static void Run(string[] args)
    {
        const string usage = "Usage: --root <directory> --output <json> --markdown <markdown> [--github-summary]";
        if (args.Contains("--help") || args.Contains("-h"))
        {
            Console.WriteLine("Summarize completed verification stages while retaining every original record.\n" + usage);
            return;
        }
        args = args.SelectMany(argument => argument.StartsWith("--", StringComparison.Ordinal) && argument.Contains('=')
            ? argument.Split('=', 2) : [argument]).ToArray();
        string? root = null, output = null, markdown = null;
        var githubSummary = false;
        for (var index = 0; index < args.Length; index++)
        {
            switch (args[index])
            {
                case "--root" when index + 1 < args.Length: root = args[++index]; break;
                case "--output" when index + 1 < args.Length: output = args[++index]; break;
                case "--markdown" when index + 1 < args.Length: markdown = args[++index]; break;
                case "--github-summary": githubSummary = true; break;
                default: throw new ArgumentException(usage);
            }
        }
        if (root is null || output is null || markdown is null) throw new ArgumentException("--root, --output and --markdown are required");
        var records = Collect(root);
        var groups = Summarize(records);
        var report = Markdown(groups, records.Count);
        foreach (var path in new[] { output, markdown }) Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(path))!);
        File.WriteAllText(output, JsonSerializer.Serialize(new
        {
            durationSemantics = "inclusive, possibly overlapping",
            stages = groups.Select(group => new { group.Suite, stage = group.StageName, group.Count, group.DurationSeconds, group.MaxSeconds, group.Failures }),
            records
        }, Json) + "\n");
        File.WriteAllText(markdown, report);
        if (githubSummary && Environment.GetEnvironmentVariable("GITHUB_STEP_SUMMARY") is { Length: > 0 } summary)
            File.AppendAllText(summary, report);
        Console.WriteLine($"Recorded {records.Count} completed stages in {output}");
    }
}
