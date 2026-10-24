#!/usr/bin/env dotnet
#:property PublishAot=false

using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;

if (args is not [var consumer, var candidate])
    throw new ArgumentException("Usage: PrepareConsumer.cs <consumer checkout> <LeanCIL checkout>");

candidate = Path.GetFullPath(candidate);
string Git(params string[] arguments)
{
    var start = new ProcessStartInfo("git") { RedirectStandardOutput = true, UseShellExecute = false };
    foreach (var argument in new[] { "-C", candidate }.Concat(arguments))
        start.ArgumentList.Add(argument);
    using var process = Process.Start(start) ?? throw new InvalidOperationException("Could not start git.");
    var output = process.StandardOutput.ReadToEnd().Trim();
    process.WaitForExit();
    if (process.ExitCode != 0) throw new InvalidOperationException("Could not inspect the candidate repository.");
    return output;
}
if (Git("rev-parse", "--is-shallow-repository") != "false")
    throw new InvalidOperationException("Consumer checks require a full candidate checkout; use fetch-depth: 0.");
var revision = Git("rev-parse", "--verify", "HEAD");
if (!Regex.IsMatch(revision, "^[0-9a-f]{40}$"))
    throw new InvalidOperationException("Could not identify the candidate commit.");

var path = Path.Combine(Path.GetFullPath(consumer), "verification", "lakefile.toml");
var source = File.ReadAllText(path);
var dependency = new Regex("(?m)(name = \"leancil\"\\r?\\n)git = [^\\r\\n]+\\r?\\nrev = [^\\r\\n]+");
if (dependency.Matches(source).Count != 1)
    throw new InvalidOperationException("Expected exactly one pinned LeanCIL git dependency.");
File.WriteAllText(path, dependency.Replace(source, match => match.Groups[1].Value +
    "git = " + JsonSerializer.Serialize(candidate.Replace('\\', '/')) + "\nrev = \"" + revision + "\""));
Console.WriteLine($"Consumer will build committed candidate {revision} from {candidate}");
