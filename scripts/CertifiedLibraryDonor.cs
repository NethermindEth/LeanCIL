using System.ComponentModel;
using System.Text.Json;
using System.Text.RegularExpressions;

/// <summary>
/// Chooses a certified library that an earlier CI run already built. Only runs whose code is
/// trusted may donate, and the trusted digest comes from that run's job log, never the artifact.
/// </summary>
static class CertifiedLibraryDonor
{
    /// <summary>A producer artifact authenticated by the digest printed in its job log.</summary>
    public sealed record Selection(long Run, long Artifact, string Digest, string? ArchiveDigest = null);

    /// <summary>Unavailable candidate listings do not prevent independent donors from being checked.</summary>
    public static T[] Available<T>(string description, Func<IEnumerable<T>> lookup, Action<string> warning)
    {
        try { return lookup().ToArray(); }
        catch (Exception error) when (error is InvalidOperationException or JsonException or
                                      Win32Exception or KeyNotFoundException or FormatException or OverflowException)
        {
            warning(description + " unavailable; trying other donors. " + error.Message);
            return [];
        }
    }

    /// <summary>Finds a complete authenticated candidate; failures never supply partial evidence.</summary>
    public static Selection? Find(IEnumerable<long> runs, Func<long, string, JsonElement> api,
        Func<long, string> log, DateTimeOffset now, Action<string> warning)
    {
        foreach (long run in runs.Distinct())
        foreach (var (attempt, job) in Available($"Run {run} jobs",
            () => PreparedAttempts(api(run, "/jobs?filter=all&per_page=100")), warning))
        {
            var selected = Available($"Run {run} attempt {attempt}", () =>
            {
                var artifact = Artifact(api(run, "/artifacts?name=" + ArtifactName(run, attempt)), run, attempt, now);
                if (artifact is null) return Array.Empty<Selection>();
                var producerLog = log(job);
                var digest = Digest(producerLog);
                var archiveDigest = ArchiveDigest(producerLog);
                if (digest is null || (producerLog.Contains(ArchiveDigestLine, StringComparison.Ordinal) &&
                    archiveDigest is null)) return [];
                return new[] { new Selection(run, artifact.Value, digest, archiveDigest) };
            }, warning);
            if (selected.Length != 0) return selected[0];
        }
        return null;
    }

    /// <summary>Retries transient HTTP failures at most twice; unsuccessful responses are never parsed.</summary>
    public static string Request(Func<(int ExitCode, string Output, string Error)> send, Action<TimeSpan> delay)
    {
        const int maximumAttempts = 3;
        for (var attempt = 1; ; attempt++)
        {
            var result = send();
            if (result.ExitCode == 0) return result.Output;
            if (attempt == maximumAttempts ||
                !Regex.IsMatch(result.Error, @"\(HTTP (408|429|500|502|503|504)\)"))
                throw new InvalidOperationException(result.Error.Trim());
            delay(TimeSpan.FromSeconds(attempt));
        }
    }

    /// <summary>The line <c>PrepareLibrary.cs</c> prints for the library it certified.</summary>
    public const string DigestLine = "Certified library manifest SHA256: ";

    /// <summary>The packed library's digest, printed by its producer before upload.</summary>
    public const string ArchiveDigestLine = "Certified library archive SHA256: ";

    /// <summary>A donated artifact must outlive every suite job that downloads it.</summary>
    public static readonly TimeSpan MinimumRemainingRetention = TimeSpan.FromDays(1);

    static readonly Regex DigestPattern = new(Regex.Escape(DigestLine) + "([0-9a-f]{64})\\s*$", RegexOptions.Multiline);

    /// <summary>The artifact one prepare attempt uploads.</summary>
    public static string ArtifactName(long run, int attempt) => $"certified-library-{run}-{attempt}";

    /// <summary>Recent successful main pushes from this repository, bounded before filtering.</summary>
    public static IEnumerable<long> RecentMainRuns(JsonElement runs, string repository, int limit) =>
        runs.GetProperty("workflow_runs").EnumerateArray().Take(limit)
            .Where(run => run.GetProperty("event").GetString() == "push" &&
                run.GetProperty("head_branch").GetString() == "main" &&
                run.GetProperty("status").GetString() == "completed" &&
                run.GetProperty("conclusion").GetString() == "success" &&
                SameRepository(run.GetProperty("head_repository"), repository) &&
                Regex.IsMatch(run.GetProperty("head_sha").GetString() ?? "", "^[0-9a-f]{40}$"))
            .Select(run => run.GetProperty("id").GetInt64()).Where(id => id > 0).Distinct();

    /// <summary>Earlier successful runs of this same-repository PR, restricted to ancestors of its head.</summary>
    public static IEnumerable<long> PullAncestors(JsonElement runs, string repository, int pull, string head,
        Func<string, bool> isAncestor, int limit)
    {
        if (pull <= 0 || !Regex.IsMatch(head, "^[0-9a-f]{40}$")) yield break;
        foreach (var run in runs.GetProperty("workflow_runs").EnumerateArray().Take(limit))
        {
            if (run.GetProperty("event").GetString() != "pull_request" ||
                run.GetProperty("status").GetString() != "completed" ||
                run.GetProperty("conclusion").GetString() != "success" ||
                !SameRepository(run.GetProperty("head_repository"), repository) ||
                !run.GetProperty("pull_requests").EnumerateArray().Any(request =>
                    request.GetProperty("number").GetInt32() == pull)) continue;
            var commit = run.GetProperty("head_sha").GetString() ?? "";
            var id = run.GetProperty("id").GetInt64();
            if (id > 0 && commit != head && Regex.IsMatch(commit, "^[0-9a-f]{40}$") && isAncestor(commit))
                yield return id;
        }
    }

    /// <summary>Same-repository merged PR heads whose complete tree equals the push commit.</summary>
    public static IEnumerable<string> MergedHeads(string repository, string commit, Func<string, JsonElement> api)
    {
        if (!Regex.IsMatch(commit, "^[0-9a-f]{40}$")) return [];
        var prefix = $"repos/{repository}/";
        var pulls = api(prefix + $"commits/{commit}/pulls?per_page=10");
        var heads = pulls.EnumerateArray().Take(10).Where(pull =>
            pull.GetProperty("merged_at").ValueKind == JsonValueKind.String &&
            pull.GetProperty("merge_commit_sha").GetString() == commit &&
            SameRepository(pull.GetProperty("base").GetProperty("repo"), repository) &&
            SameRepository(pull.GetProperty("head").GetProperty("repo"), repository))
            .Select(pull => pull.GetProperty("head").GetProperty("sha").GetString() ?? "")
            .Where(head => Regex.IsMatch(head, "^[0-9a-f]{40}$")).Distinct().ToArray();
        if (heads.Length == 0) return [];
        var tree = api(prefix + "git/commits/" + commit).GetProperty("tree").GetProperty("sha").GetString();
        if (tree is null || !Regex.IsMatch(tree, "^[0-9a-f]{40}$")) return [];
        return heads.Where(head => api(prefix + "git/commits/" + head)
            .GetProperty("tree").GetProperty("sha").GetString() == tree).ToArray();
    }

    static bool SameRepository(JsonElement repository, string expected) =>
        repository.ValueKind == JsonValueKind.Object &&
        string.Equals(repository.GetProperty("full_name").GetString(), expected, StringComparison.OrdinalIgnoreCase);

    // Matches the prepare job under its earlier name too, so runs from before a rename still donate.
    static bool IsPrepareJob(string name) =>
        name.StartsWith("Prepare ", StringComparison.Ordinal) &&
        name.EndsWith("certified Lean library", StringComparison.Ordinal);

    /// <summary>Successful prepare jobs of one run, newest attempt first.</summary>
    public static IEnumerable<(int Attempt, long Job)> PreparedAttempts(JsonElement jobs) =>
        jobs.GetProperty("jobs").EnumerateArray()
            .Where(job => IsPrepareJob(job.GetProperty("name").GetString() ?? "") &&
                job.GetProperty("conclusion").ValueKind == JsonValueKind.String &&
                job.GetProperty("conclusion").GetString() == "success")
            .Select(job => (job.GetProperty("run_attempt").GetInt32(), job.GetProperty("id").GetInt64()))
            .OrderByDescending(prepared => prepared.Item1);

    /// <summary>The id of the attempt's library artifact, if it exists and stays downloadable.</summary>
    public static long? Artifact(JsonElement artifacts, long run, int attempt, DateTimeOffset now)
    {
        string name = ArtifactName(run, attempt);
        foreach (JsonElement artifact in artifacts.GetProperty("artifacts").EnumerateArray())
            if (artifact.GetProperty("name").GetString() == name && !artifact.GetProperty("expired").GetBoolean() &&
                artifact.GetProperty("expires_at").GetDateTimeOffset() - now >= MinimumRemainingRetention &&
                artifact.GetProperty("workflow_run").GetProperty("id").GetInt64() == run)
                return artifact.GetProperty("id").GetInt64();
        return null;
    }

    /// <summary>The one digest a prepare job printed, or null when it printed none or several.</summary>
    public static string? Digest(string log)
    {
        string[] digests = DigestPattern.Matches(log).Select(match => match.Groups[1].Value)
            .Distinct(StringComparer.Ordinal).ToArray();
        return digests.Length == 1 ? digests[0] : null;
    }

    /// <summary>The one archive digest from the same prepare-job log, absent for legacy raw artifacts.</summary>
    public static string? ArchiveDigest(string log)
    {
        var pattern = Regex.Escape(ArchiveDigestLine) + "([^\\r\\n]*)";
        var digests = Regex.Matches(log, pattern).Select(match => match.Groups[1].Value.Trim())
            .Distinct(StringComparer.Ordinal).ToArray();
        return digests.Length == 1 && Regex.IsMatch(digests[0], "^[0-9a-f]{64}$") ? digests[0] : null;
    }
}
