#!/usr/bin/env dotnet
#:property PublishAot=false
#:include CertifiedLibraryDonor.cs

using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;

// A PR run donates once its prepare job succeeded, even if its suites failed. That job's own code
// built the library and printed its digest; PrepareLibrary --reuse rechecks both.
const int RunsPerCommit = 10;
var options = new Dictionary<string, string>(StringComparer.Ordinal);
for (var i = 0; i < args.Length; i++)
{
    if (args[i] is not ("--repository" or "--workflow" or "--head" or "--base" or "--output" or "--event" or
        "--pull-request") ||
        i + 1 == args.Length)
        throw new ArgumentException("Usage: FindCertifiedLibrary.cs --repository <owner/name> --workflow <file> " +
            "--head <commit> --base <commit> --output <file> [--event <event>] [--pull-request <number>]");
    options[args[i]] = args[++i];
}
string repository = options["--repository"], workflow = options["--workflow"], output = options["--output"];
string runs = $"repos/{repository}/actions/workflows/{workflow}/runs?per_page={RunsPerCommit}&head_sha=";
string RunPath(long run) => $"repos/{repository}/actions/runs/{run}";
var selected = CertifiedLibraryDonor.Find(CertifiedLibraryDonor.Candidates(() => Runs(options["--head"], ""),
        PullAncestorRuns, MergedPullRuns, () => Runs(options["--base"], "&event=push&branch=main"), RecentMainRuns),
    (run, suffix) => Api(RunPath(run) + suffix),
    job => Gh($"repos/{repository}/actions/jobs/{job}/logs", "--allow-escape-sequences"),
    DateTimeOffset.UtcNow, Warning);
if (selected is null)
    Console.WriteLine("No certified library to reuse; building from sources.");
else
{
    // Run metadata, not the donated bytes, decides whether the producer ran reviewed code.
    var reviewed = CertifiedLibraryDonor.Available("Run " + selected.Run, () =>
        new[] { CertifiedLibraryDonor.ReviewedProducer(Api(RunPath(selected.Run)), repository,
            path => Api($"repos/{repository}/{path}"), Warning) }, Warning).FirstOrDefault();
    File.AppendAllText(output,
        $"run-id={selected.Run}\nartifact-id={selected.Artifact}\nmanifest-sha256={selected.Digest}\n" +
        $"archive-sha256={selected.ArchiveDigest}\nreviewed-producer={(reviewed ? "true" : "false")}\n");
    Console.WriteLine($"Reusing artifact {selected.Artifact} from run {selected.Run} " +
        $"with manifest SHA256 {selected.Digest}");
    Console.WriteLine(reviewed ? "The donor ran reviewed producer code; reuse skips kernel replay."
        : "The donor may have run unreviewed producer code; reuse kernel-replays the library.");
}

void Warning(string message) => Console.WriteLine("::warning::" + message);

// An empty or abbreviated commit would match unrelated runs instead of none.
IEnumerable<long> Runs(string commit, string filter) => Regex.IsMatch(commit, "^[0-9a-f]{40}$")
    ? CertifiedLibraryDonor.Available("Commit " + commit, () =>
        Api(runs + commit + filter).GetProperty("workflow_runs").EnumerateArray()
            .Select(run => run.GetProperty("id").GetInt64()), Warning)
    : [];

JsonElement Api(string path) => JsonSerializer.Deserialize<JsonElement>(Gh(path));

// The exact base may have skipped preparation or reused a library without republishing it.
IEnumerable<long> RecentMainRuns() => CertifiedLibraryDonor.Available("Recent main runs", () =>
    CertifiedLibraryDonor.RecentMainRuns(Api(
        $"repos/{repository}/actions/workflows/{workflow}/runs?per_page={RunsPerCommit}" +
        "&event=push&branch=main&status=success"), repository, RunsPerCommit), Warning);

IEnumerable<long> PullAncestorRuns()
{
    if (options.GetValueOrDefault("--event") != "pull_request" ||
        !int.TryParse(options.GetValueOrDefault("--pull-request"), out var pull) || pull <= 0) return [];
    return CertifiedLibraryDonor.Available("Earlier PR libraries", () =>
    {
        var request = Api($"repos/{repository}/pulls/{pull}");
        var head = request.GetProperty("head");
        if (head.GetProperty("repo").GetProperty("full_name").GetString() != repository ||
            head.GetProperty("sha").GetString() != options["--head"]) return Array.Empty<long>();
        var branch = Uri.EscapeDataString(head.GetProperty("ref").GetString()!);
        var previous = Api($"repos/{repository}/actions/workflows/{workflow}/runs?per_page={RunsPerCommit}" +
            "&event=pull_request&branch=" + branch);
        return CertifiedLibraryDonor.PullAncestors(previous, repository, pull, options["--head"],
            commit => Api($"repos/{repository}/compare/{commit}...{options["--head"]}")
                .GetProperty("status").GetString() == "ahead", RunsPerCommit);
    }, Warning);
}

IEnumerable<long> MergedPullRuns()
{
    if (options.GetValueOrDefault("--event") != "push") return [];
    return CertifiedLibraryDonor.Available("Merged PR libraries", () =>
        CertifiedLibraryDonor.MergedHeads(repository, options["--head"], Api)
            .SelectMany(head => Runs(head, "&event=pull_request")), Warning);
}

string Gh(string path, params string[] flags) =>
    CertifiedLibraryDonor.Request(() => Send(path, flags), Thread.Sleep);

(int ExitCode, string Output, string Error) Send(string path, string[] flags)
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
    return (process.ExitCode, stdout, $"gh api {path} failed: {stderr.Result.Trim()}");
}
