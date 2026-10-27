#!/usr/bin/env dotnet
#:property PublishAot=false
#:include CertifiedLibraryDonor.cs

using System.ComponentModel;
using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;

// Donors are runs of this exact commit, then main pushes of the commit this checkout merges onto.
// Their own code built the library and printed its digest; PrepareLibrary --reuse rechecks both.
const int RunsPerCommit = 10;
var options = new Dictionary<string, string>(StringComparer.Ordinal);
for (var i = 0; i < args.Length; i++)
{
    if (args[i] is not ("--repository" or "--workflow" or "--head" or "--base" or "--output") || i + 1 == args.Length)
        throw new ArgumentException("Usage: FindCertifiedLibrary.cs --repository <owner/name> --workflow <file> " +
            "--head <commit> --base <commit> --output <file>");
    options[args[i]] = args[++i];
}
string repository = options["--repository"], workflow = options["--workflow"], output = options["--output"];
string runs = $"repos/{repository}/actions/workflows/{workflow}/runs?per_page={RunsPerCommit}&head_sha=";
string RunPath(long run) => $"repos/{repository}/actions/runs/{run}";
try
{
    IEnumerable<long> candidates = Runs(options["--head"], "").Concat(Runs(options["--base"], "&event=push&branch=main"))
        .Distinct();
    foreach (long run in candidates)
    foreach ((int attempt, long job) in
        CertifiedLibraryDonor.PreparedAttempts(Api(RunPath(run) + "/jobs?filter=all&per_page=100")))
    {
        string name = CertifiedLibraryDonor.ArtifactName(run, attempt);
        long? artifact = CertifiedLibraryDonor.Artifact(Api(RunPath(run) + "/artifacts?name=" + name), run, attempt,
            DateTimeOffset.UtcNow);
        if (artifact is null) continue;
        // Job logs carry ANSI colour codes, which gh refuses to print unless allowed.
        string? digest = CertifiedLibraryDonor.Digest(
            Gh($"repos/{repository}/actions/jobs/{job}/logs", "--allow-escape-sequences"));
        if (digest is null) continue;
        File.AppendAllText(output, $"run-id={run}\nartifact-id={artifact}\nmanifest-sha256={digest}\n");
        Console.WriteLine($"Reusing {name} (artifact {artifact}) with manifest SHA256 {digest}");
        return;
    }
    Console.WriteLine("No certified library to reuse; building from sources.");
}
// Reuse only saves time, so an unavailable API falls back to a fresh build.
catch (Exception error) when (error is InvalidOperationException or JsonException or Win32Exception)
{
    Console.WriteLine("::warning::Certified library lookup failed; building from sources. " + error.Message);
}

// An empty or abbreviated commit would match unrelated runs instead of none.
IEnumerable<long> Runs(string commit, string filter) => Regex.IsMatch(commit, "^[0-9a-f]{40}$")
    ? Api(runs + commit + filter).GetProperty("workflow_runs").EnumerateArray()
        .Select(run => run.GetProperty("id").GetInt64()).ToArray()
    : [];

JsonElement Api(string path) => JsonSerializer.Deserialize<JsonElement>(Gh(path));

string Gh(string path, params string[] flags)
{
    var start = new ProcessStartInfo("gh")
    {
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false,
        CreateNoWindow = true
    };
    string[] arguments = ["api", "-H", "X-GitHub-Api-Version: 2022-11-28", .. flags, path];
    foreach (string arg in arguments) start.ArgumentList.Add(arg);
    using var process = Process.Start(start) ?? throw new InvalidOperationException("Could not start gh");
    var stderr = process.StandardError.ReadToEndAsync();
    var stdout = process.StandardOutput.ReadToEnd();
    process.WaitForExit();
    if (process.ExitCode != 0) throw new InvalidOperationException($"gh api {path} failed: {stderr.Result.Trim()}");
    return stdout;
}
