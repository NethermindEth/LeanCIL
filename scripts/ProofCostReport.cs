using System.Collections.Concurrent;
using System.Diagnostics;
using System.Globalization;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

// Measures what each proof of a checkout costs to elaborate and compares two measurements.
// Only reproducible measures decide the result; elapsed times are carried for the reader.
internal static partial class ProofCostReport
{
    internal const int Schema = 1;
    internal const string ModuleKind = "module";
    internal const string ModuleRow = "(module)";
    internal const string AcceptedFile = "scripts/proof-cost-accepted.json";

    // A regression must exceed both the relative threshold and the measure's absolute floor.
    internal const double DefaultThresholdPercent = 5;

    internal static readonly JsonSerializerOptions Json = new()
    {
        WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.CamelCase
    };

    // One measured thing: a declaration, a module, or a fixture row another producer supplies.
    internal sealed record Row(string Group, string Name, string Kind, SortedDictionary<string, long> Measures);

    internal sealed record Unmeasured(string Group, string Reason);

    internal sealed record Measurement(int Schema, string Tree, List<Row> Rows, List<Unmeasured> Unmeasured);

    // A reviewed increase of one measure of one row, bound to the values it was accepted at.
    internal sealed record Accepted(string Group, string Name, string Measure, long From, long To, string Reason);

    // Deciding measures are reproducible and can fail the comparison; the others are only reported.
    // Tolerance is how far a rerun may move the measure; an accepted increase still matches within it.
    internal sealed record Policy(string Measure, string Title, bool Decides, long Floor, long Tolerance = 0);

    internal static readonly Policy[] Policies =
    [
        new("heartbeats", "Heartbeats", Decides: true, Floor: 50_000, Tolerance: 1_000),
        new("oleanBytes", "Olean bytes", Decides: true, Floor: 4_096),
        new("kernelHeartbeats", "Kernel heartbeats", Decides: false, Floor: 0),
        new("proofObjects", "Proof objects", Decides: false, Floor: 0),
        new("sourceLines", "Lines", Decides: false, Floor: 0),
        new("elapsedMs", "Elapsed ms", Decides: false, Floor: 0),
        new("kernelMs", "Kernel ms", Decides: false, Floor: 0)
    ];

    // Ordered by how much attention a row needs, least first.
    internal enum Status { Unchanged, Removed, Added, Decreased, Increased, Accepted, Regression }

    internal sealed record Change(string Group, string Name, string Kind, string Measure, long? Base, long? Head,
        Status Status);

    internal sealed record Comparison(List<Change> Changes, List<string> Failures, List<Accepted> UnusedAccepted,
        Measurement Base, Measurement Head, double ThresholdPercent)
    {
        internal IEnumerable<Change> Regressions => Changes.Where(change => change.Status == Status.Regression);
        internal bool Failed => Failures.Count > 0 || Regressions.Any();
    }

    static Policy? PolicyOf(string measure) => Policies.FirstOrDefault(policy => policy.Measure == measure);

    internal static bool Exceeds(long before, long after, long floor, double thresholdPercent)
    {
        var growth = after - before;
        return growth > floor && growth * 100.0 > before * thresholdPercent;
    }

    internal static Comparison Compare(Measurement before, Measurement after, IReadOnlyList<Accepted> accepted,
        double thresholdPercent = DefaultThresholdPercent)
    {
        static Dictionary<(string, string), Row> Index(Measurement measurement, List<string> failures, string side)
        {
            var rows = new Dictionary<(string, string), Row>();
            foreach (var row in measurement.Rows)
                if (!rows.TryAdd((row.Group, row.Name), row))
                    failures.Add($"{side} measurement repeats the row {row.Group} {row.Name}");
            return rows;
        }

        var failures = new List<string>();
        var baseRows = Index(before, failures, "base");
        var headRows = Index(after, failures, "head");
        var used = new HashSet<Accepted>();
        var changes = new List<Change>();
        // A module that gained or lost rows grows for that reason, so its totals are then reported only.
        static ILookup<string, string> Members(Measurement measurement) => measurement.Rows
            .Where(row => row.Kind != ModuleKind).ToLookup(row => row.Group, row => row.Name);
        var baseMembers = Members(before);
        var headMembers = Members(after);
        foreach (var key in baseRows.Keys.Union(headRows.Keys).Order())
        {
            baseRows.TryGetValue(key, out var baseRow);
            headRows.TryGetValue(key, out var headRow);
            var kind = (headRow ?? baseRow)!.Kind;
            var comparable = kind != ModuleKind ||
                baseMembers[key.Item1].ToHashSet(StringComparer.Ordinal).SetEquals(headMembers[key.Item1]);
            var measures = (baseRow?.Measures.Keys ?? Enumerable.Empty<string>())
                .Union(headRow?.Measures.Keys ?? Enumerable.Empty<string>()).Order(StringComparer.Ordinal);
            foreach (var measure in measures)
            {
                long? baseValue = baseRow is not null && baseRow.Measures.TryGetValue(measure, out var first)
                    ? first : null;
                long? headValue = headRow is not null && headRow.Measures.TryGetValue(measure, out var second)
                    ? second : null;
                var status = (baseValue, headValue) switch
                {
                    (null, _) => Status.Added,
                    (_, null) => Status.Removed,
                    var (old, current) when current == old => Status.Unchanged,
                    var (old, current) when current < old => Status.Decreased,
                    _ => Status.Increased
                };
                if (status == Status.Increased && comparable && PolicyOf(measure) is { Decides: true } policy &&
                    Exceeds(baseValue!.Value, headValue!.Value, policy.Floor, thresholdPercent))
                {
                    var entry = accepted.FirstOrDefault(entry => entry.Group == key.Item1 && entry.Name == key.Item2 &&
                        entry.Measure == measure && Math.Abs(entry.From - baseValue.Value) <= policy.Tolerance &&
                        headValue <= entry.To + policy.Tolerance);
                    status = entry is null ? Status.Regression : Status.Accepted;
                    if (entry is not null) used.Add(entry);
                }
                changes.Add(new Change(key.Item1, key.Item2, kind, measure, baseValue, headValue, status));
            }
        }
        if (after.Rows.Count == 0) failures.Add("nothing was measured at the head");
        // A proof the base could measure must stay measurable, or its cost goes untracked.
        var baseGroups = before.Rows.Select(row => row.Group).ToHashSet(StringComparer.Ordinal);
        foreach (var lost in after.Unmeasured.Where(lost => baseGroups.Contains(lost.Group)))
            failures.Add($"{lost.Group} was measured at the base but not at the head: {lost.Reason}");
        return new Comparison(changes, failures, accepted.Where(entry => !used.Contains(entry)).ToList(), before, after,
            thresholdPercent);
    }

    static string Cell(string value) => value.Replace("&", "&amp;").Replace("<", "&lt;").Replace(">", "&gt;")
        .Replace("|", "\\|").Replace('\n', ' ').Replace('\r', ' ');

    static string Number(long? value) => value is { } number ? number.ToString("N0", CultureInfo.InvariantCulture) : "";

    static string Percent(long? before, long? after) => (before, after) switch
    {
        (null, _) => "new",
        (_, null) => "removed",
        var (old, current) when old == current => "",
        (0, _) => "from 0",
        var (old, current) => Math.Round((current!.Value - old!.Value) * 100.0 / old.Value, 1) switch
        {
            0 => current > old ? "+<0.1%" : "-<0.1%",
            var percent => string.Create(CultureInfo.InvariantCulture, $"{percent:+0.0;-0.0}%")
        }
    };

    static string Mark(Status status) => status switch
    {
        Status.Regression => "**regression**",
        Status.Accepted => "accepted",
        _ => ""
    };

    const int UnchangedRowLimit = 50;
    const int ChangedRowLimit = 400;
    const int NotablePercent = 1;
    const int RegressionLimit = 100;

    // Heartbeats differ by a few units between runs of one tree; such changes are not worth a reader's time.
    static bool Notable(Change change) => change.Status switch
    {
        Status.Unchanged => false,
        Status.Decreased or Status.Increased =>
            Math.Abs(change.Head!.Value - change.Base!.Value) * 100 >= change.Base.Value * NotablePercent,
        _ => true
    };

    // Rows that moved come first, largest growth first; unchanged rows follow by cost.
    static List<IGrouping<(string Group, string Name), Change>> Ordered(IEnumerable<Change> changes,
        string[] columns) => changes.GroupBy(change => (change.Group, change.Name))
        .Where(row => row.Any(change => columns.Contains(change.Measure)))
        .OrderByDescending(row => row.Where(change => PolicyOf(change.Measure) is { Decides: true } && Notable(change))
            .Select(change => change.Status).DefaultIfEmpty().Max())
        .ThenByDescending(row => row.Where(change => PolicyOf(change.Measure) is { Decides: true } && Notable(change))
            .Select(change => Math.Abs((change.Head ?? 0) - (change.Base ?? 0))).DefaultIfEmpty().Max())
        .ThenByDescending(row => row.FirstOrDefault(change => change.Measure == columns[0])?.Head ?? 0)
        .ThenBy(row => row.Key.Group, StringComparer.Ordinal).ThenBy(row => row.Key.Name, StringComparer.Ordinal)
        .ToList();

    static void Table(List<string> lines, string heading, string label, IEnumerable<Change> changes,
        string[] columns)
    {
        var rows = Ordered(changes, columns);
        if (rows.Count == 0) return;
        static bool Moved(IGrouping<(string, string), Change> row, string[] columns) => row.Any(change =>
            columns.Contains(change.Measure) && PolicyOf(change.Measure) is { Decides: true } && Notable(change));
        var moved = rows.Where(row => Moved(row, columns)).ToList();
        var still = rows.Where(row => !Moved(row, columns)).ToList();
        var shown = moved.Take(ChangedRowLimit).Concat(still.Take(UnchangedRowLimit)).ToList();
        lines.AddRange(["", $"### {heading}", "",
            $"{moved.Count} of {rows.Count} changed a deciding measure by {NotablePercent}% or more, or were added " +
            "or removed; they come first. A changed cell is base, head and the change.", ""]);
        lines.Add($"| {label} | " + string.Join(" | ", columns.Select(column => PolicyOf(column)!.Title)) + " | |");
        lines.Add("| --- | " + string.Join(" | ", columns.Select(_ => "---:")) + " | --- |");
        foreach (var row in shown)
        {
            var cells = columns.Select(column => row.FirstOrDefault(change => change.Measure == column) switch
            {
                null => "",
                { Status: Status.Unchanged } change => Number(change.Head),
                { Base: null } change => Number(change.Head) + " new",
                { Head: null } change => Number(change.Base) + " removed",
                var change => $"{Number(change.Base)} -> {Number(change.Head)} ({Percent(change.Base, change.Head)})"
            });
            var marks = row.Select(change => Mark(change.Status)).Where(mark => mark.Length > 0).Distinct();
            var name = row.Key.Name == ModuleRow ? row.Key.Group : $"{row.Key.Group} `{row.Key.Name}`";
            lines.Add($"| {Cell(name)} | {string.Join(" | ", cells)} | {string.Join(", ", marks)} |");
        }
        if (shown.Count < rows.Count)
            lines.AddRange(["", $"{rows.Count - shown.Count} more rows are in the JSON report."]);
    }

    internal static string Markdown(Comparison comparison)
    {
        var deciding = Policies.Where(policy => policy.Decides).ToArray();
        var limits = string.Join(" or ", deciding.Select(policy => string.Create(CultureInfo.InvariantCulture,
            $"{policy.Title.ToLowerInvariant()} by more than {comparison.ThresholdPercent:0.##}% and " +
            $"{policy.Floor:N0}")));
        var regressions = comparison.Regressions.ToList();
        var lines = new List<string>
        {
            "## Proof cost against the merge base", "",
            $"Base `{comparison.Base.Tree}`, head `{comparison.Head.Tree}`: {comparison.Head.Rows.Count} rows " +
            $"measured at the head, {comparison.Base.Rows.Count} at the base.", "",
            $"A row fails when it grows in {limits}, unless `{AcceptedFile}` accepts that increase. " +
            "A module's totals fail only while it holds the same rows at the base and the head. " +
            "Elapsed times, kernel heartbeats, proof objects and lines are reported and never fail.", "",
            comparison.Failed
                ? $"**Failed:** {regressions.Count} regressions and {comparison.Failures.Count} other failures."
                : comparison.Base.Rows.Count == 0
                    ? "**Not compared:** nothing was measured at the base, so every row is new."
                    : "**Passed:** no deciding measure grew beyond its threshold."
        };
        var baseGroups = comparison.Base.Rows.Select(row => row.Group).ToHashSet(StringComparer.Ordinal);
        var headGroups = comparison.Head.Rows.Select(row => row.Group).ToHashSet(StringComparer.Ordinal);
        var withoutBase = headGroups.Count(group => !baseGroups.Contains(group));
        if (withoutBase > 0 && comparison.Base.Rows.Count > 0)
            lines.AddRange(["", $"{withoutBase} of {headGroups.Count} modules at the head have no rows at the base " +
                "and were not compared."]);
        if (regressions.Count > 0)
        {
            lines.AddRange(["", "### Regressions", "", "| Row | Measure | Base | Head | Change |",
                "| --- | --- | ---: | ---: | ---: |"]);
            var listed = regressions.OrderByDescending(change => change.Head - change.Base).Take(RegressionLimit)
                .ToList();
            foreach (var change in listed)
                lines.Add($"| {Cell(change.Group)} `{Cell(change.Name)}` | {PolicyOf(change.Measure)!.Title} | " +
                    $"{Number(change.Base)} | {Number(change.Head)} | {Percent(change.Base, change.Head)} |");
            if (listed.Count < regressions.Count)
                lines.AddRange(["", $"The largest {listed.Count} are listed; all are in the JSON report."]);
            var entries = listed.Select(change => new Accepted(change.Group, change.Name, change.Measure,
                change.Base!.Value, change.Head!.Value, "why this increase is worth its cost"));
            lines.AddRange(["", $"To accept these increases, add the entries to `{AcceptedFile}` with the reason:",
                "", "```json", JsonSerializer.Serialize(entries, Json), "```"]);
        }
        if (comparison.Failures.Count > 0)
        {
            lines.AddRange(["", "### Failures", ""]);
            lines.AddRange(comparison.Failures.Select(failure => "- " + Cell(failure)));
        }
        var standard = Policies.Select(policy => policy.Measure).ToHashSet(StringComparer.Ordinal);
        Table(lines, "Modules", "Module", comparison.Changes.Where(change => change.Kind == ModuleKind),
            ["heartbeats", "oleanBytes", "sourceLines", "elapsedMs"]);
        Table(lines, "Proofs and declarations", "Declaration", comparison.Changes.Where(change =>
                change.Kind != ModuleKind && standard.Contains(change.Measure)),
            ["heartbeats", "kernelHeartbeats", "proofObjects", "sourceLines", "elapsedMs"]);
        var other = comparison.Changes.Where(change => !standard.Contains(change.Measure)).ToList();
        if (other.Count > 0)
        {
            lines.AddRange(["", "### Other measures", "", "Reported only.", "",
                "| Row | Measure | Base | Head | Change |", "| --- | --- | ---: | ---: | ---: |"]);
            foreach (var change in other.Take(ChangedRowLimit))
                lines.Add($"| {Cell(change.Group)} `{Cell(change.Name)}` | {Cell(change.Measure)} | " +
                    $"{Number(change.Base)} | {Number(change.Head)} | {Percent(change.Base, change.Head)} |");
        }
        foreach (var (side, unmeasured) in new[]
            { ("head", comparison.Head.Unmeasured), ("base", comparison.Base.Unmeasured) })
        {
            if (unmeasured.Count == 0) continue;
            lines.AddRange(["", $"### Not measured at the {side}", ""]);
            lines.AddRange(unmeasured.Select(lost => $"- {Cell(lost.Group)}: {Cell(lost.Reason)}"));
        }
        if (comparison.UnusedAccepted.Count > 0)
        {
            lines.AddRange(["", "### Accepted increases that matched nothing", "",
                $"These entries of `{AcceptedFile}` no longer apply and can be removed:", ""]);
            lines.AddRange(comparison.UnusedAccepted.Select(entry =>
                $"- {Cell(entry.Group)} `{Cell(entry.Name)}` {entry.Measure} {entry.From:N0} -> {entry.To:N0}"));
        }
        return string.Join('\n', lines) + "\n";
    }

    // The frontend reports commands in source order; repeated labels are numbered so rows stay distinct.
    internal static List<Row> Rows(string group, JsonElement report, long oleanBytes, long sourceLines)
    {
        var rows = new List<Row>();
        var seen = new Dictionary<string, int>(StringComparer.Ordinal);
        var totals = new SortedDictionary<string, long>(StringComparer.Ordinal);
        foreach (var command in report.GetProperty("commands").EnumerateArray())
        {
            var measures = new SortedDictionary<string, long>(StringComparer.Ordinal);
            foreach (var policy in Policies)
                if (command.TryGetProperty(policy.Measure, out var value) && policy.Measure != "oleanBytes")
                {
                    measures[policy.Measure] = value.GetInt64();
                    if (policy.Measure != "sourceLines")
                        totals[policy.Measure] = totals.GetValueOrDefault(policy.Measure) + value.GetInt64();
                }
            var label = command.GetProperty("label").GetString()!;
            var count = seen[label] = seen.GetValueOrDefault(label) + 1;
            rows.Add(new Row(group, count == 1 ? label : $"{label} #{count}",
                command.GetProperty("kind").GetString()!, measures));
        }
        totals["oleanBytes"] = oleanBytes;
        totals["sourceLines"] = sourceLines;
        rows.Add(new Row(group, ModuleRow, ModuleKind, totals));
        return rows;
    }

    [GeneratedRegex("""(?ms)^\[\[lean_lib\]\][ \t]*\r?$(?<body>.*?)(?=^\[|\z)""")]
    private static partial Regex LibraryTable();

    [GeneratedRegex("""^name[ \t]*=[ \t]*"(?<name>[^"]+)"$""")]
    private static partial Regex LibraryName();

    // Test libraries are the tables that only name a library: no source directory, roots or facets.
    internal static string[] TestLibraries(string lakefile) => LibraryTable().Matches(lakefile)
        .Select(table => table.Groups["body"].Value.Split('\n').Select(line => line.Trim())
            .Where(line => line.Length > 0 && !line.StartsWith('#')).ToArray())
        .Where(body => body.Length == 1 && LibraryName().IsMatch(body[0]))
        .Select(body => LibraryName().Match(body[0]).Groups["name"].Value)
        .Where(name => name != "CIL").ToArray();

    [GeneratedRegex("""^(?:(?:public|meta|private)[ \t]+)*import[ \t]+(?:all[ \t]+)?(?<modules>[^-/]+)""")]
    private static partial Regex ImportLine();

    // Imports end at the first command; comments may precede or separate them.
    internal static string[] Imports(string source)
    {
        var modules = new List<string>();
        var inComment = false;
        foreach (var raw in source.Split('\n'))
        {
            var line = raw.Trim();
            if (inComment)
            {
                inComment = !line.Contains("-/", StringComparison.Ordinal);
                continue;
            }
            if (line.Length == 0 || line.StartsWith("--", StringComparison.Ordinal)) continue;
            if (line.StartsWith("/-", StringComparison.Ordinal))
            {
                inComment = !line.Contains("-/", StringComparison.Ordinal);
                continue;
            }
            if (line == "module" || line == "prelude") continue;
            if (ImportLine().Match(line) is not { Success: true } import) break;
            modules.AddRange(import.Groups["modules"].Value
                .Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries));
        }
        return [.. modules];
    }

    internal static (int Code, string Output) Execute(string[] command, string directory,
        IReadOnlyDictionary<string, string>? environment = null)
    {
        var start = new ProcessStartInfo(command[0])
        {
            WorkingDirectory = directory, RedirectStandardOutput = true, RedirectStandardError = true,
            StandardOutputEncoding = Encoding.UTF8, StandardErrorEncoding = Encoding.UTF8,
            UseShellExecute = false, CreateNoWindow = true
        };
        foreach (var argument in command[1..]) start.ArgumentList.Add(argument);
        foreach (var (name, value) in environment ?? new Dictionary<string, string>()) start.Environment[name] = value;
        using var process = Process.Start(start)
            ?? throw new InvalidOperationException("Could not start " + command[0]);
        var output = new StringBuilder();
        void Append(object _, DataReceivedEventArgs data)
        {
            if (data.Data is not null) lock (output) output.AppendLine(data.Data);
        }
        process.OutputDataReceived += Append;
        process.ErrorDataReceived += Append;
        process.BeginOutputReadLine();
        process.BeginErrorReadLine();
        process.WaitForExit();
        return (process.ExitCode, output.ToString());
    }

    static string ScriptDirectory([CallerFilePath] string path = "") => Path.GetDirectoryName(path)!;

    static string Sha(string path) => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));

    // Lean's first error explains a failure better than whatever line happens to come first.
    static string Diagnostic(int code, string output)
    {
        var lines = output.Split('\n').Select(line => line.Trim()).Where(line => line.Length > 0).ToArray();
        return lines.FirstOrDefault(line => line.Contains("error:", StringComparison.Ordinal)) ?? lines.FirstOrDefault()
            ?? $"lean exited with code {code} and no diagnostic";
    }

    // Measures the modules of one checkout against one compiled library.
    sealed class Measurer(string tree, string library, string work, int jobs)
    {
        readonly string frontend = Path.Combine(ScriptDirectory(), "ProofCost.lean");
        readonly string shared = Path.Combine(work, "modules");
        readonly SemaphoreSlim slots = new(jobs);
        readonly ConcurrentDictionary<string, Task<string?>> modules = new(StringComparer.Ordinal);
        internal readonly ConcurrentBag<Row> Rows = [];
        internal readonly ConcurrentBag<Unmeasured> Lost = [];

        string? TreeSource(string module) =>
            module != "CIL" && !module.StartsWith("CIL.", StringComparison.Ordinal) &&
            Path.Combine(tree, module.Replace('.', Path.DirectorySeparatorChar) + ".lean") is var path &&
            File.Exists(path) ? path : null;

        // Returns why the module could not be measured, or null once its rows and olean exist.
        async Task<string?> Compile(string group, string module, string source, string root)
        {
            foreach (var import in Imports(File.ReadAllText(source)))
                if (TreeSource(import) is not null && await TreeModule(import) is { } reason)
                    return $"its import {import} was not measured: {reason}";
            var olean = Path.Combine(root, module.Replace('.', Path.DirectorySeparatorChar) + ".olean");
            var report = Path.ChangeExtension(olean, ".cost.json");
            Directory.CreateDirectory(Path.GetDirectoryName(olean)!);
            await slots.WaitAsync();
            try
            {
                var path = string.Join(Path.PathSeparator, new[] { root, shared, library }.Distinct());
                var result = await Task.Run(() => Execute(["lean", "--run", frontend, module, source, report, olean],
                    tree, new Dictionary<string, string> { ["LEAN_PATH"] = path }));
                if (result.Code != 0 || !File.Exists(report)) return Diagnostic(result.Code, result.Output);
            }
            finally { slots.Release(); }
            // A module's compiled size is every part Lean wrote for it.
            var bytes = Directory.EnumerateFiles(Path.GetDirectoryName(olean)!, Path.GetFileName(olean) + "*")
                .Sum(part => new FileInfo(part).Length);
            using var parsed = JsonDocument.Parse(File.ReadAllText(report));
            foreach (var row in ProofCostReport.Rows(group, parsed.RootElement, bytes,
                File.ReadLines(source).LongCount()))
                Rows.Add(row);
            return null;
        }

        // A module of the checkout is measured once, however many modules import it.
        internal Task<string?> TreeModule(string module) => modules.GetOrAdd(module, async name =>
        {
            var reason = await Compile(name, name, TreeSource(name)!, shared);
            if (reason is not null) Lost.Add(new Unmeasured(name, reason));
            return reason;
        });

        // A verified output directory keeps its extraction; its report names the proof it accepted.
        internal async Task Verified(string artifacts, string directory)
        {
            var output = Path.GetRelativePath(artifacts, directory).Replace('\\', '/');
            var stage = Path.Combine(work, "verified", output.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(stage);
            using var report = JsonDocument.Parse(File.ReadAllText(Path.Combine(directory, "verified.json")));
            var proofs = report.RootElement.TryGetProperty("inputs", out var inputs)
                ? inputs.EnumerateObject().Where(input => input.Name.StartsWith("proof:", StringComparison.Ordinal))
                    .Select(input => (Path: input.Name["proof:".Length..], Sha256: input.Value.GetString())).ToArray()
                : [];
            string? unusable = proofs switch
            {
                not [_] => "the report does not name exactly one proof source",
                [var proof] when !File.Exists(proof.Path) => "the proof source no longer exists",
                [var proof] when Sha(proof.Path) != proof.Sha256 => "the proof source changed after verification",
                _ => null
            };
            var sources = new List<(string Module, string Source)>
            {
                ("Extracted", Path.Combine(directory, "Extracted.lean"))
            };
            if (File.Exists(Path.Combine(directory, "Symbols.lean")))
                sources.Add(("ExtractedSymbols", Path.Combine(directory, "Symbols.lean")));
            if (unusable is null) sources.Add(("Proof", proofs[0].Path));
            else Lost.Add(new Unmeasured($"{output}/Proof", unusable));
            // Each module is its own group; one that fails takes the modules after it with it.
            string? blocked = null;
            foreach (var (module, source) in sources)
            {
                var staged = Path.Combine(stage, module + ".lean");
                File.Copy(source, staged, true);
                var reason = blocked ?? await Compile($"{output}/{module}", module, staged, stage);
                if (reason is null) continue;
                Lost.Add(new Unmeasured($"{output}/{module}", reason));
                blocked ??= $"{module} was not measured";
            }
        }
    }

    static string LibraryPath(string tree, string? library)
    {
        const string compiled = ".lake/build/lib/lean";
        var candidates = library is null ? [Path.Combine(tree, compiled)]
            : new[] { library, Path.Combine(library, compiled) };
        return candidates.Select(Path.GetFullPath).FirstOrDefault(path => File.Exists(Path.Combine(path, "CIL.olean")))
            ?? throw new ArgumentException("No compiled CIL library in " + string.Join(" or ", candidates) +
                "; build every CIL module there or pass --library");
    }

    internal static Measurement Measure(string tree, string? library, string work, bool libraries,
        IReadOnlyList<string> artifacts, IReadOnlyList<string> modules, int jobs, string label)
    {
        tree = Path.GetFullPath(tree);
        work = Path.GetFullPath(work);
        if (Directory.Exists(work)) Directory.Delete(work, true);
        var measurer = new Measurer(tree, LibraryPath(tree, library), work, jobs);
        var tasks = new List<Task>();
        var roots = modules.ToList();
        if (libraries) roots.AddRange(TestLibraries(File.ReadAllText(Path.Combine(tree, "lakefile.toml"))));
        foreach (var module in roots.Distinct(StringComparer.Ordinal))
        {
            var source = Path.Combine(tree, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
            if (File.Exists(source)) tasks.Add(measurer.TreeModule(module));
            else measurer.Lost.Add(new Unmeasured(module, "the checkout has no source for this module"));
        }
        foreach (var root in artifacts.Select(Path.GetFullPath))
        {
            // A suite the tree does not have leaves no outputs, which is a measurement without rows.
            if (!Directory.Exists(root)) continue;
            foreach (var report in Directory.EnumerateFiles(root, "verified.json", SearchOption.AllDirectories)
                .Where(report => File.Exists(Path.Combine(Path.GetDirectoryName(report)!, "Extracted.lean")) &&
                    !Path.GetFullPath(report).StartsWith(work + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                .Order(StringComparer.Ordinal))
                tasks.Add(measurer.Verified(root, Path.GetDirectoryName(report)!));
        }
        Task.WaitAll([.. tasks]);
        return new Measurement(Schema, label,
            [.. measurer.Rows.OrderBy(row => row.Group, StringComparer.Ordinal)
                .ThenBy(row => row.Kind == ModuleKind ? 1 : 0).ThenBy(row => row.Name, StringComparer.Ordinal)],
            [.. measurer.Lost.OrderBy(lost => lost.Group, StringComparer.Ordinal)]);
    }

    internal const string LibrariesSource = "libraries";

    static readonly string[] LibraryInputs = ["lakefile.toml", "lean-toolchain", "lake-manifest.json"];

    // What a change needs measured: the test libraries when Lean inputs changed, and each selected proof suite.
    internal static string[] Sources(string selectionMatrix, IEnumerable<string> changedPaths)
    {
        using var matrix = JsonDocument.Parse(selectionMatrix);
        var selected = matrix.RootElement.GetProperty("include").EnumerateArray()
            .SelectMany(group => group.GetProperty("suites").EnumerateArray()).Select(suite => suite.GetString())
            .ToHashSet(StringComparer.Ordinal);
        var lean = changedPaths.Any(path => path.EndsWith(".lean", StringComparison.Ordinal) ||
            LibraryInputs.Contains(path));
        return [.. lean ? [LibrariesSource] : Array.Empty<string>(),
            .. VerificationSuites.ProofSuites.Where(selected.Contains)];
    }

    internal static Measurement Read(IEnumerable<string> paths)
    {
        var parts = paths.Select(path =>
        {
            var part = JsonSerializer.Deserialize<Measurement>(File.ReadAllText(path), Json)
                ?? throw new InvalidDataException(path + " is not a measurement");
            return part.Schema == Schema ? part
                : throw new InvalidDataException($"{path} has schema {part.Schema}, expected {Schema}");
        }).ToArray();
        return new Measurement(Schema, string.Join(", ", parts.Select(part => part.Tree).Distinct()),
            [.. parts.SelectMany(part => part.Rows)], [.. parts.SelectMany(part => part.Unmeasured)]);
    }

    const string Usage = """
        Usage:
          ProofCost.cs measure --tree <checkout> --output <json> [--library <compiled library>]
              [--libraries] [--module <name>]... [--artifacts <verification outputs>]...
              [--work <directory>] [--jobs <count>] [--label <name>]
          ProofCost.cs compare --base <json>... --head <json>... [--accepted <json>]
              [--threshold-percent <number>] [--markdown <file>] [--output <json>] [--github-summary]
          ProofCost.cs sources --matrix <selection json> [--tree <checkout> --base <commit>] [--output <file>]
        """;

    internal static int Run(string[] args)
    {
        if (args.Length == 0 || args.Contains("--help") || args.Contains("-h"))
        {
            Console.WriteLine(Usage);
            return args.Length == 0 ? 2 : 0;
        }
        var options = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        for (var index = 1; index < args.Length; index++)
        {
            var name = args[index];
            if (!name.StartsWith("--", StringComparison.Ordinal)) throw new ArgumentException(Usage);
            var values = options.TryGetValue(name, out var existing) ? existing : options[name] = [];
            if (name is not ("--libraries" or "--github-summary"))
                values.Add(index + 1 < args.Length ? args[++index] : throw new ArgumentException(Usage));
        }
        string? One(string name) => options.TryGetValue(name, out var values) ? values[^1] : null;
        string Required(string name) => One(name) ?? throw new ArgumentException(name + " is required\n" + Usage);
        IReadOnlyList<string> Many(string name) => options.TryGetValue(name, out var values) ? values : [];
        void Write(string path, string text)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(path))!);
            File.WriteAllText(path, text);
        }

        switch (args[0])
        {
            case "measure":
            {
                var output = Required("--output");
                var tree = Required("--tree");
                var elapsed = Stopwatch.StartNew();
                var measurement = Measure(tree, One("--library"),
                    One("--work") ?? Path.ChangeExtension(Path.GetFullPath(output), ".work"),
                    options.ContainsKey("--libraries"), Many("--artifacts"), Many("--module"),
                    int.Parse(One("--jobs") ?? Math.Max(1, Environment.ProcessorCount / 2).ToString(
                        CultureInfo.InvariantCulture), CultureInfo.InvariantCulture),
                    One("--label") ?? Execute(["git", "rev-parse", "--short=12", "HEAD"], tree).Output.Trim());
                Write(output, JsonSerializer.Serialize(measurement, Json) + "\n");
                foreach (var lost in measurement.Unmeasured)
                    Console.Error.WriteLine($"Not measured: {lost.Group}: {lost.Reason}");
                Console.WriteLine($"Measured {measurement.Rows.Count(row => row.Kind == ModuleKind)} modules and " +
                    $"{measurement.Rows.Count(row => row.Kind != ModuleKind)} commands in " +
                    $"{elapsed.Elapsed.TotalSeconds:F0}s; {measurement.Unmeasured.Count} not measured: {output}");
                return 0;
            }
            case "compare":
            {
                var accepted = One("--accepted") is { } path && File.Exists(path)
                    ? JsonSerializer.Deserialize<List<Accepted>>(File.ReadAllText(path), Json) ?? [] : [];
                var comparison = Compare(Read(Many("--base")), Read(Many("--head")), accepted,
                    double.Parse(One("--threshold-percent") ?? DefaultThresholdPercent.ToString(
                        CultureInfo.InvariantCulture), CultureInfo.InvariantCulture));
                var report = Markdown(comparison);
                if (One("--markdown") is { } markdown) Write(markdown, report);
                if (One("--output") is { } json)
                    Write(json, JsonSerializer.Serialize(new
                    {
                        schema = Schema, comparison.ThresholdPercent, comparison.Failed, comparison.Failures,
                        changes = comparison.Changes.Select(change => new
                        {
                            change.Group, change.Name, change.Kind, change.Measure, change.Base, change.Head,
                            status = change.Status.ToString().ToLowerInvariant()
                        })
                    }, Json) + "\n");
                if (options.ContainsKey("--github-summary") &&
                    Environment.GetEnvironmentVariable("GITHUB_STEP_SUMMARY") is { Length: > 0 } summary)
                    File.AppendAllText(summary, report);
                Console.Write(report);
                return comparison.Failed ? 1 : 0;
            }
            case "sources":
            {
                // Without a base every source is measured, as a manual run of the unchanged tree does.
                var changed = One("--base") is { } before
                    ? Execute(["git", "diff", "--name-only", "--no-renames", before, "HEAD"], Required("--tree"))
                        is { Code: 0 } diff ? diff.Output.Split('\n', StringSplitOptions.TrimEntries)
                        : throw new InvalidOperationException("Could not list the paths changed since " + before)
                    : ["lakefile.toml"];
                var sources = JsonSerializer.Serialize(Sources(Required("--matrix"), changed));
                if (One("--output") is { } output) File.AppendAllText(output, $"sources={sources}\n");
                Console.WriteLine(sources);
                return 0;
            }
            default:
                throw new ArgumentException(Usage);
        }
    }
}
