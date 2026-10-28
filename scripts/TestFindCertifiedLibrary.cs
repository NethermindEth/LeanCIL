#!/usr/bin/env dotnet
#:property PublishAot=false
#:include CertifiedLibraryDonor.cs

using System.Text.Json;

var checks = 0;
void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}
void Test(string name, Action action)
{
    action();
    checks++;
    Console.WriteLine("PASS " + name);
}
JsonElement Json(string text) => JsonSerializer.Deserialize<JsonElement>(text);
const string Digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
const string Other = "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210";
DateTimeOffset now = DateTimeOffset.Parse("2026-10-27T00:00:00Z");

Test("only successful prepare jobs donate, newest attempt first", () =>
{
    var jobs = Json("""
        {"jobs":[
          {"id":1,"name":"Prepare fresh certified Lean library","run_attempt":1,"conclusion":"success"},
          {"id":2,"name":"Prepare certified Lean library","run_attempt":3,"conclusion":"success"},
          {"id":3,"name":"Prepare certified Lean library","run_attempt":2,"conclusion":"failure"},
          {"id":4,"name":"Prepare certified Lean library","run_attempt":4,"conclusion":null},
          {"id":5,"name":"Verify (core)","run_attempt":3,"conclusion":"success"}]}
        """);
    var attempts = CertifiedLibraryDonor.PreparedAttempts(jobs).ToArray();
    Require(attempts.SequenceEqual([(3, 2L), (1, 1L)]), "Unexpected donors: " + string.Join(", ", attempts));
});

Test("an artifact donates only when its own run uploaded it and it outlives the suites", () =>
{
    string Listing(string name, bool expired, string expires, long run) => $$$"""
        {"artifacts":[{"id":9,"name":"{{{name}}}","expired":{{{(expired ? "true" : "false")}}},
          "expires_at":"{{{expires}}}","workflow_run":{"id":{{{run}}}}}]}
        """;
    Require(CertifiedLibraryDonor.Artifact(Json(Listing("certified-library-7-2", false, "2026-11-05T00:00:00Z", 7)),
        7, 2, now) == 9, "A live artifact must donate");
    Require(CertifiedLibraryDonor.Artifact(Json(Listing("certified-library-7-1", false, "2026-11-05T00:00:00Z", 7)),
        7, 2, now) is null, "Another attempt's artifact must not donate");
    Require(CertifiedLibraryDonor.Artifact(Json(Listing("certified-library-7-2", true, "2026-11-05T00:00:00Z", 7)),
        7, 2, now) is null, "An expired artifact must not donate");
    Require(CertifiedLibraryDonor.Artifact(Json(Listing("certified-library-7-2", false, "2026-10-27T12:00:00Z", 7)),
        7, 2, now) is null, "An artifact expiring during the run must not donate");
    Require(CertifiedLibraryDonor.Artifact(Json(Listing("certified-library-7-2", false, "2026-11-05T00:00:00Z", 8)),
        7, 2, now) is null, "An artifact from another run must not donate");
});

Test("the trusted digest is the single one the prepare job printed", () =>
{
    string Line(string digest) => "2026-10-27T06:39:34.1Z " + CertifiedLibraryDonor.DigestLine + digest + "\r\n";
    Require(CertifiedLibraryDonor.Digest("build\n" + Line(Digest) + "done\n") == Digest, "Missing digest");
    Require(CertifiedLibraryDonor.Digest(Line(Digest) + Line(Digest)) == Digest, "Repeated digest");
    Require(CertifiedLibraryDonor.Digest(Line(Digest) + Line(Other)) is null, "Conflicting digests must not donate");
    Require(CertifiedLibraryDonor.Digest("build failed\n") is null, "A log without a digest must not donate");
    Require(CertifiedLibraryDonor.Digest(Line(Digest[..63])) is null, "A truncated digest must not donate");
});
Test("merged PR donors require exact trees and same-repository merge provenance", () =>
{
    var commit = new string('a', 40);
    var head = new string('b', 40);
    var tree = new string('c', 40);
    string Pull(string merge, string? merged, string? source, string target, string revision) =>
        JsonSerializer.Serialize(new
        {
            merge_commit_sha = merge, merged_at = merged,
            @base = new { repo = new { full_name = target } },
            head = new { sha = revision, repo = source is null ? null : new { full_name = source } }
        });
    var valid = Pull(commit, "2026-10-27T00:00:00Z", "owner/repo", "owner/repo", head);
    var calls = new List<string>();
    string listing = "[" + valid + "]", donorTree = tree;
    string? pushTree = tree;
    JsonElement Api(string path)
    {
        calls.Add(path);
        if (path.EndsWith("/pulls?per_page=10", StringComparison.Ordinal)) return Json(listing);
        return Json(JsonSerializer.Serialize(new { tree = new { sha = path.EndsWith(head) ? donorTree : pushTree } }));
    }
    Require(CertifiedLibraryDonor.MergedHeads("owner/repo", commit, Api).SequenceEqual([head]),
        "Identical merged head was not selected");
    donorTree = new string('d', 40);
    Require(!CertifiedLibraryDonor.MergedHeads("owner/repo", commit, Api).Any(), "Different tree donated");
    donorTree = tree;
    foreach (var invalidTree in new[] { null, "", tree[..7], new string('z', 40) })
    {
        pushTree = invalidTree;
        Require(!CertifiedLibraryDonor.MergedHeads("owner/repo", commit, Api).Any(), "Invalid tree donated");
    }
    pushTree = tree;
    try
    {
        _ = CertifiedLibraryDonor.MergedHeads("owner/repo", commit, path =>
            path.EndsWith("/pulls?per_page=10", StringComparison.Ordinal) ? Json(listing) : Json("{\"tree\":{}}"));
        throw new InvalidOperationException("Missing tree SHA was accepted");
    }
    catch (KeyNotFoundException) { } // The lookup treats incomplete API responses as unavailable.
    foreach (var invalid in new[]
             {
                 Pull(head, "merged", "owner/repo", "owner/repo", head),
                 Pull(commit, null, "owner/repo", "owner/repo", head),
                 Pull(commit, "merged", "fork/repo", "owner/repo", head),
                 Pull(commit, "merged", null, "owner/repo", head),
                 Pull(commit, "merged", "owner/repo", "other/repo", head),
                 Pull(commit, "merged", "owner/repo", "owner/repo", head[..7])
             })
    {
        listing = "[" + invalid + "]";
        calls.Clear();
        Require(!CertifiedLibraryDonor.MergedHeads("owner/repo", commit, Api).Any(), "Untrusted PR donated");
        Require(calls.Count == 1, "Ineligible PR performed a tree lookup");
    }
    listing = "[" + string.Join(',', Enumerable.Repeat(valid, 11)) + "]";
    calls.Clear();
    Require(CertifiedLibraryDonor.MergedHeads("owner/repo", commit, Api).SequenceEqual([head]) && calls.Count == 3,
        "Repeated PR heads were not deduplicated");
    listing = "[" + string.Join(',', Enumerable.Repeat(
        Pull(commit, null, "owner/repo", "owner/repo", head), 10).Append(valid)) + "]";
    calls.Clear();
    Require(!CertifiedLibraryDonor.MergedHeads("owner/repo", commit, Api).Any() && calls.Count == 1,
        "PR lookup exceeded its bounded candidate set");
    calls.Clear();
    Require(!CertifiedLibraryDonor.MergedHeads("owner/repo", commit[..7], Api).Any() && calls.Count == 0,
        "Abbreviated push commit queried unrelated pulls");
});
Test("recent fallback admits only bounded successful main pushes from this repository", () =>
{
    string Run(long id, string branch = "main", string source = "owner/repo", string trigger = "push",
        string status = "completed", string? conclusion = "success", string? head = null) =>
        JsonSerializer.Serialize(new
        {
            id, head_branch = branch, head_repository = new { full_name = source }, @event = trigger,
            status, conclusion, head_sha = head ?? new string('a', 40)
        });
    JsonElement Listing(params string[] runs) => Json("{\"workflow_runs\":[" + string.Join(',', runs) + "]}");
    var valid = Listing(Run(9), Run(7), Run(7));
    Require(CertifiedLibraryDonor.RecentMainRuns(valid, "owner/repo", 10).SequenceEqual([9L, 7L]),
        "Main fallback must preserve newest-first order and remove duplicates");
    foreach (var invalid in new[]
    {
        Run(1, branch: "feature"), Run(1, source: "fork/repo"), Run(1, trigger: "pull_request"),
        Run(1, status: "in_progress"), Run(1, conclusion: "failure"), Run(1, conclusion: null),
        Run(1, head: "abc123"), Run(1, head: new string('z', 40)), Run(0)
    })
        Require(!CertifiedLibraryDonor.RecentMainRuns(Listing(invalid), "owner/repo", 10).Any(),
            "Ineligible main fallback was accepted: " + invalid);
    Require(!CertifiedLibraryDonor.RecentMainRuns(Listing(Run(1, branch: "feature"), Run(2)),
        "owner/repo", 1).Any(), "Fallback exceeded its bounded candidate set");
});
Test("transient HTTP failures retry with a fixed bound, without accepting failed response bodies", () =>
{
    foreach (int status in new[] { 408, 429, 500, 502, 503, 504 })
    {
        var calls = 0;
        var delays = new List<TimeSpan>();
        var result = CertifiedLibraryDonor.Request(() => ++calls < 3
            ? (1, "untrusted body", $"gh: Server Error (HTTP {status})") : (0, "valid", ""), delays.Add);
        Require(result == "valid" && calls == 3 &&
            delays.SequenceEqual([TimeSpan.FromSeconds(1), TimeSpan.FromSeconds(2)]), "Incorrect retry policy");
    }
    foreach (var error in new[] { "gh: Server Error (HTTP 502)", "gh: Not Found (HTTP 404)",
        "gh: Forbidden (HTTP 403)", "gh: Unauthorized (HTTP 401)", "unknown failure" })
    {
        var calls = 0;
        try
        {
            CertifiedLibraryDonor.Request(() => { calls++; return (1, "untrusted body", error); }, _ => { });
            throw new Exception("Failed response accepted");
        }
        catch (InvalidOperationException rejected) { Require(rejected.Message == error, "Lost failure reason"); }
        Require(calls == (error.Contains("502") ? 3 : 1), "Permanent failures retried or transient bound exceeded");
    }
});

Test("failed candidate listings discard partial results and permit subsequent lookup", () =>
{
    IEnumerable<long> Interrupted()
    {
        yield return 1;
        throw new JsonException("incomplete listing");
    }
    var warnings = new List<string>();
    var candidates = CertifiedLibraryDonor.Available("base", Interrupted, warnings.Add)
        .Concat(CertifiedLibraryDonor.Available("recent main", () => new long[] { 2 }, warnings.Add));
    Require(candidates.SequenceEqual([2L]) && warnings.Count == 1, "Partial listing used or fallback lost");
});

Test("an unavailable run, artifact or log cannot hide the next authenticated donor", () =>
{
    foreach (var failure in new[] { "jobs", "artifact", "log", "malformed", "number", "date", "digest" })
    {
        var warnings = new List<string>();
        var firstRunCalls = 0;
        JsonElement Api(long run, string suffix)
        {
            if (run == 1) firstRunCalls++;
            if (run == 1 && failure == "malformed") return Json("{}");
            bool jobs = suffix.StartsWith("/jobs", StringComparison.Ordinal);
            if (run == 1 && failure == "number") return Json("""
                {"jobs":[{"id":99999999999999999999999,"name":"Prepare certified Lean library",
                  "run_attempt":1,"conclusion":"success"}]}
                """);
            if (run == 1 && failure == (jobs ? "jobs" : "artifact"))
                throw new InvalidOperationException("gh: Server Error (HTTP 502)");
            var response = jobs ? Json($$"""
                {"jobs":[{"id":{{run}},"name":"Prepare certified Lean library","run_attempt":1,"conclusion":"success"}]}
                """) : Json($$$"""
                {"artifacts":[{"id":{{{run * 10}}},"name":"certified-library-{{{run}}}-1","expired":false,
                  "expires_at":"2026-11-05T00:00:00Z","workflow_run":{"id":{{{run}}}}}]}
                """);
            return run == 1 && !jobs && failure == "date"
                ? Json(response.GetRawText().Replace("2026-11-05T00:00:00Z", "invalid-date")) : response;
        }
        string Log(long job)
        {
            if (job == 1 && failure == "log") throw new InvalidOperationException("missing log");
            return job == 1 && failure == "digest" ? "no digest" : CertifiedLibraryDonor.DigestLine + Digest;
        }
        var result = CertifiedLibraryDonor.Find([1, 1, 2], Api, Log, now, warnings.Add);
        Require(result == new CertifiedLibraryDonor.Selection(2, 20, Digest), "Unauthenticated donor selected");
        Require(firstRunCalls <= 2 && warnings.Count == (failure == "digest" ? 0 : 1), "Candidate was retried wholesale");
        Require(CertifiedLibraryDonor.Find([1], Api, Log, now, warnings.Add) is null,
            "Exhausted lookup must not supply partial evidence");
    }
});
Test("archive digest belongs to the same successful producer log as its manifest", () =>
{
    JsonElement Api(long run, string suffix) => suffix.StartsWith("/jobs", StringComparison.Ordinal)
        ? Json("""
            {"jobs":[{"id":9,"name":"Prepare certified Lean library","run_attempt":1,"conclusion":"success"}]}
            """)
        : Json("""
            {"artifacts":[{"id":70,"name":"certified-library-7-1","expired":false,
              "expires_at":"2026-11-05T00:00:00Z","workflow_run":{"id":7}}]}
            """);
    foreach (var archive in new[] { "", Other, Other[..63],
        Other + "\n" + CertifiedLibraryDonor.ArchiveDigestLine + Digest,
        Other + "\n" + CertifiedLibraryDonor.ArchiveDigestLine + Other[..63] })
    {
        var producerLog = CertifiedLibraryDonor.DigestLine + Digest + "\n" +
            (archive.Length == 0 ? "" : CertifiedLibraryDonor.ArchiveDigestLine + archive + "\n");
        var result = CertifiedLibraryDonor.Find([7], Api, job =>
        {
            Require(job == 9, "Digest came from another job");
            return producerLog;
        }, now, _ => { });
        Require(archive.Length == 0 ? result == new CertifiedLibraryDonor.Selection(7, 70, Digest) :
            archive == Other ? result == new CertifiedLibraryDonor.Selection(7, 70, Digest, Other) : result is null,
            "Packed or legacy donor digest mismatch");
    }
});
Console.WriteLine($"All {checks} certified library donor checks passed.");
