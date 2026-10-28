#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationSelection.cs
#:include ExportVerificationSuites.cs

using System.Diagnostics;
using System.Text;
using System.Text.Json;

var options = new Dictionary<string, string>(StringComparer.Ordinal);
for (var i = 0; i < args.Length; i++)
{
    if (args[i] is not ("--event" or "--base" or "--head" or "--output") || i + 1 == args.Length)
        throw new ArgumentException("Usage: SelectVerification.cs --event <event> [--base <commit> --head <commit>] --output <file>");
    options[args[i]] = args[++i];
}
if (!options.TryGetValue("--event", out var eventName) || !options.TryGetValue("--output", out var output))
    throw new ArgumentException("--event and --output are required");
string[] paths = [];
if (eventName == "pull_request")
{
    if (!options.TryGetValue("--base", out var first) || !options.TryGetValue("--head", out var last) ||
        string.IsNullOrEmpty(first) || string.IsNullOrEmpty(last))
        throw new ArgumentException("PR selection requires base and head commits");
    // Include both sides of renames/deletions, using the PR merge-base diff.
    var start = new ProcessStartInfo("git")
    {
        WorkingDirectory = VerificationSelection.Root,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        StandardOutputEncoding = Encoding.UTF8,
        StandardErrorEncoding = Encoding.UTF8,
        UseShellExecute = false,
        CreateNoWindow = true
    };
    foreach (var arg in new[] { "diff", "--name-only", "--no-renames", "-z", $"{first}...{last}" })
        start.ArgumentList.Add(arg);
    using var process = Process.Start(start) ?? throw new InvalidOperationException("Could not start git");
    var stderr = process.StandardError.ReadToEndAsync();
    var changed = process.StandardOutput.ReadToEnd();
    process.WaitForExit();
    if (process.ExitCode != 0) throw new InvalidOperationException(stderr.GetAwaiter().GetResult());
    paths = changed.Split('\0', StringSplitOptions.RemoveEmptyEntries);
}
var suites = VerificationSelection.Schedule(VerificationSelection.Select(paths, eventName));
Console.WriteLine(JsonSerializer.Serialize(new { changed = paths, suites }, new JsonSerializerOptions { WriteIndented = true }));
// GitHub validates the matrix even when the suite job is skipped.
var groups = VerificationSelection.Groups(suites.Length == 0 ? ["core"] : suites);
File.AppendAllText(output, "matrix=" + JsonSerializer.Serialize(new { include = groups },
    new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.CamelCase }) +
    "\nhas-suites=" + (suites.Length > 0 ? "true" : "false") + "\n");
