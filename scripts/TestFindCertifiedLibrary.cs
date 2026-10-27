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
Console.WriteLine($"All {checks} certified library donor checks passed.");
