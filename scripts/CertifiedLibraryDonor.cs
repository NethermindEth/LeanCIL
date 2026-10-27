using System.Text.Json;
using System.Text.RegularExpressions;

/// <summary>
/// Chooses a certified library that an earlier CI run already built. Only runs whose code is
/// trusted may donate, and the trusted digest comes from that run's job log, never the artifact.
/// </summary>
static class CertifiedLibraryDonor
{
    /// <summary>The line <c>PrepareLibrary.cs</c> prints for the library it certified.</summary>
    public const string DigestLine = "Certified library manifest SHA256: ";

    /// <summary>A donated artifact must outlive every suite job that downloads it.</summary>
    public static readonly TimeSpan MinimumRemainingRetention = TimeSpan.FromDays(1);

    static readonly Regex DigestPattern = new(Regex.Escape(DigestLine) + "([0-9a-f]{64})\\s*$", RegexOptions.Multiline);

    /// <summary>The artifact one prepare attempt uploads.</summary>
    public static string ArtifactName(long run, int attempt) => $"certified-library-{run}-{attempt}";

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
}
