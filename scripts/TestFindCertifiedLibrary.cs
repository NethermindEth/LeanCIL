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

Test("PR donors require the same PR, repository and an ancestor, whatever their suites concluded", () =>
{
    var head = new string('a', 40);
    var ancestor = new string('b', 40);
    string Run(int pull = 42, string repository = "owner/repo", string status = "completed",
        string conclusion = "success", string? commit = null) => JsonSerializer.Serialize(new
        {
            workflow_runs = new[] { new { id = 9, @event = "pull_request", status, conclusion,
                head_sha = commit ?? ancestor, head_repository = new { full_name = repository },
                pull_requests = new[] { new { number = pull } } } }
        });
    long[] Select(string json, bool related = true) => CertifiedLibraryDonor.PullAncestors(Json(json),
        "owner/repo", 42, head, _ => related, 10).ToArray();
    Require(Select(Run()).SequenceEqual([9L]), "Successful ancestor was omitted");
    // The prepare job decides eligibility, so failed suites or a running workflow do not hide a library.
    foreach (var pending in new[] { Run(status: "in_progress", conclusion: ""), Run(conclusion: "failure"),
        Run(conclusion: "cancelled") })
        Require(Select(pending).SequenceEqual([9L]), "Ancestor with a successful prepare job was omitted");
    foreach (var invalid in new[] { Run(pull: 43), Run(repository: "fork/repo"), Run(commit: head),
        Run(commit: "bad") })
        Require(Select(invalid).Length == 0, "Unrelated run accepted");
    Require(Select(Run(), related: false).Length == 0, "Nonancestor accepted");
});

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
Test("proof cost rows come only from the publishing job, its own artifact and its logged digest", () =>
{
    var rows = CertifiedLibraryDonor.ProofCostRows;
    // Run 7 published rows and a library; a library digest or artifact must never stand in for the rows'.
    JsonElement Api(long run, string suffix) => suffix.StartsWith("/jobs", StringComparison.Ordinal)
        ? Json("""
            {"jobs":[{"id":9,"name":"Prepare certified Lean library","run_attempt":1,"conclusion":"success"},
              {"id":10,"name":"Publish proof cost rows","run_attempt":1,"conclusion":"success"},
              {"id":11,"name":"Proof cost","run_attempt":1,"conclusion":"success"}]}
            """)
        : Json("""
            {"artifacts":[{"id":70,"name":"certified-library-7-1","expired":false,
              "expires_at":"2026-11-05T00:00:00Z","workflow_run":{"id":7}},
              {"id":71,"name":"proof-cost-rows-7-1","expired":false,
              "expires_at":"2026-11-05T00:00:00Z","workflow_run":{"id":7}}]}
            """);
    JsonElement FailedJob() => Json("""
        {"jobs":[{"id":10,"name":"Publish proof cost rows","run_attempt":1,"conclusion":"failure"}]}
        """);
    string Log(long job) =>
        job == 10 ? rows.DigestLine + Other + "\n" : CertifiedLibraryDonor.DigestLine + Digest + "\n";
    Require(CertifiedLibraryDonor.Find([7], Api, Log, now, _ => { }, rows) ==
        new CertifiedLibraryDonor.Selection(7, 71, Other), "Published rows were not found by their own job");
    Require(CertifiedLibraryDonor.ArtifactName(7, 1, rows) == "proof-cost-rows-7-1", "Rows artifact was renamed");
    Require(CertifiedLibraryDonor.Find([7], Api, _ => CertifiedLibraryDonor.DigestLine + Digest, now, _ => { },
        rows) is null, "A library digest authenticated proof cost rows");
    Require(CertifiedLibraryDonor.Find([7], (run, suffix) => suffix.StartsWith("/jobs", StringComparison.Ordinal)
        ? FailedJob() : Api(run, suffix), Log, now, _ => { }, rows) is null, "A failed publishing job donated rows");
});
JsonElement PreparedRun(long run, string conclusion) => Json($$"""
    {"jobs":[
      {"id":{{run * 100}},"name":"Prepare certified Lean library","run_attempt":1,"conclusion":"{{conclusion}}"},
      {"id":{{run * 100 + 1}},"name":"Verify (evidence)","run_attempt":1,"conclusion":"failure"}]}
    """);
JsonElement LiveArtifact(long run) => Json($$$"""
    {"artifacts":[{"id":{{{run * 10}}},"name":"certified-library-{{{run}}}-1","expired":false,
      "expires_at":"2026-11-05T00:00:00Z","workflow_run":{"id":{{{run}}}}}]}
    """);
Test("a run whose suites failed donates through its successful prepare job", () =>
{
    // Run 7's evidence suite failed after its prepare job certified and logged the library.
    var result = CertifiedLibraryDonor.Find([7, 8], (run, suffix) =>
        suffix.StartsWith("/jobs", StringComparison.Ordinal) ? PreparedRun(run, "success") : LiveArtifact(run),
        job => CertifiedLibraryDonor.DigestLine + (job == 700 ? Digest : Other), now, _ => { });
    Require(result == new CertifiedLibraryDonor.Selection(7, 70, Digest), "Failed-suite run did not donate");
});
Test("a run whose prepare job failed or was cancelled never donates", () =>
{
    foreach (var conclusion in new[] { "failure", "cancelled", "skipped" })
    {
        var logs = new List<long>();
        var result = CertifiedLibraryDonor.Find([7, 8], (run, suffix) =>
            suffix.StartsWith("/jobs", StringComparison.Ordinal)
                ? PreparedRun(run, run == 7 ? conclusion : "success") : LiveArtifact(run),
            job => { logs.Add(job); return CertifiedLibraryDonor.DigestLine + Digest; }, now, _ => { });
        Require(result == new CertifiedLibraryDonor.Selection(8, 80, Digest) && logs.SequenceEqual([800L]),
            "A " + conclusion + " prepare job donated or had its log trusted");
    }
});
Test("a same-PR ancestor is preferred over main, which is not queried once it donates", () =>
{
    const long ancestor = 5, main = 6;
    var queried = new List<string>();
    IEnumerable<long> Source(string name, params long[] runs)
    {
        queried.Add(name);
        return runs;
    }
    var candidates = CertifiedLibraryDonor.Candidates(() => Source("commit"), () => Source("ancestors", ancestor),
        () => Source("merged"), () => Source("base", main), () => Source("recent", main));
    var result = CertifiedLibraryDonor.Find(candidates, (run, suffix) =>
        suffix.StartsWith("/jobs", StringComparison.Ordinal) ? PreparedRun(run, "success") : LiveArtifact(run),
        job => CertifiedLibraryDonor.DigestLine + Digest, now, _ => { });
    Require(result == new CertifiedLibraryDonor.Selection(ancestor, 50, Digest), "Main preferred over ancestor");
    Require(queried.SequenceEqual(["commit", "ancestors"]), "Main queried before the ancestor was tried: " +
        string.Join(", ", queried));
    Require(CertifiedLibraryDonor.Candidates(() => [1], () => [2], () => [3], () => [4], () => [5])
        .SequenceEqual([1L, 2, 3, 4, 5]), "Donor sources out of order");
});
Test("only a donor that ran reviewed producer code skips replay", () =>
{
    string head = new('d', 40), mergeBase = new('b', 40), baseCommit = new('c', 40), main = new('e', 40);
    const string here = "https://api.github.com/repos/owner/repo";
    object Side(string reference, string sha, string url = here) => new { @ref = reference, sha, repo = new { url } };
    object Pull(string baseRef = "main", string baseUrl = here, string headUrl = here, string? headSha = null) =>
        new
        {
            number = 42, @base = Side(baseRef, baseCommit, baseUrl), head = Side("feature", headSha ?? head, headUrl)
        };
    JsonElement Run(string trigger = "pull_request", string branch = "feature", string repository = "owner/repo",
        string? commit = null, object[]? pulls = null) => Json(JsonSerializer.Serialize(new
        {
            @event = trigger, head_branch = branch, head_sha = commit ?? head,
            head_repository = new { full_name = repository }, pull_requests = pulls ?? [Pull()]
        }));
    // Each commit gets its own root and intermediate trees, so only the producer objects can agree.
    Func<string, JsonElement> Repository(char headWorkflow = 'e', char headScripts = 'f', bool truncated = false,
        string? knownBase = null, string headOnMain = "behind", string baseOnMain = "behind",
        string mainRef = "refs/heads/main")
    {
        var objects = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [$"compare/{baseCommit}...{head}"] = JsonSerializer.Serialize(new
            {
                merge_base_commit = new { sha = knownBase ?? mergeBase }
            }),
            ["git/ref/heads/main"] = JsonSerializer.Serialize(new { @ref = mainRef, @object = new { sha = main } }),
            [$"compare/{main}...{head}"] = JsonSerializer.Serialize(new { status = headOnMain }),
            [$"compare/{main}...{mergeBase}"] = JsonSerializer.Serialize(new { status = baseOnMain })
        };
        string Tree(params (string Name, string Type, string Sha)[] entries) => JsonSerializer.Serialize(new
        {
            truncated, tree = entries.Select(entry => new { path = entry.Name, type = entry.Type, sha = entry.Sha })
        });
        void Commit(string commit, char side, char workflow, char scripts, char sources)
        {
            string Sha(char kind) => new string(kind, 39) + side;
            objects["git/commits/" + commit] = JsonSerializer.Serialize(new { tree = new { sha = Sha('1') } });
            objects["git/trees/" + Sha('1')] = Tree((".github", "tree", Sha('2')),
                ("scripts", "tree", new string(scripts, 40)), ("CIL", "tree", new string(sources, 40)));
            objects["git/trees/" + Sha('2')] = Tree(("workflows", "tree", Sha('3')));
            objects["git/trees/" + Sha('3')] = Tree(("verification.yml", "blob", new string(workflow, 40)));
        }
        // Lean sources differ, which the library identity binds; only producer code decides replay.
        Commit(mergeBase, 'a', 'e', 'f', '7');
        Commit(head, 'b', headWorkflow, headScripts, '8');
        return path => objects.TryGetValue(path, out var json) ? Json(json)
            : throw new InvalidOperationException("gh: Not Found (HTTP 404) " + path);
    }
    bool Reviewed(JsonElement run, Func<string, JsonElement> api) =>
        CertifiedLibraryDonor.ReviewedProducer(run, "owner/repo", api, _ => { });
    void Replayed(string label, JsonElement run, Func<string, JsonElement> api) =>
        Require(!Reviewed(run, api), label + " skipped replay");
    Func<string, JsonElement> unavailable = _ => throw new InvalidOperationException("gh: Server Error (HTTP 502)");

    var push = Run(trigger: "push", branch: "main", pulls: []);
    Require(Reviewed(push, Repository()) && Reviewed(push, Repository(headOnMain: "identical")),
        "A main push donor was replayed");
    Require(Reviewed(Run(), Repository()), "A PR into main leaving producer paths unchanged was replayed");
    Console.WriteLine("PASS a main push donor and a PR into main that leaves producer paths unchanged are trusted");

    Replayed("A PR that changed scripts/", Run(), Repository(headScripts: '9'));
    Replayed("A PR that changed the workflow", Run(), Repository(headWorkflow: '9'));
    Console.WriteLine("PASS a PR donor whose head changed scripts/ or the workflow is replayed");

    Replayed("A PR into another branch", Run(pulls: [Pull(baseRef: "feature/parent")]), Repository());
    Replayed("A fork PR", Run(pulls: [Pull(headUrl: "https://api.github.com/repos/fork/repo")]), Repository());
    Replayed("A PR into another repository", Run(pulls: [Pull(baseUrl: "https://api.github.com/repos/other/repo")]),
        Repository());
    Replayed("A fork run", Run(repository: "fork/repo"), Repository());
    Replayed("An empty pull_requests array", Run(pulls: []), Repository());
    Replayed("Multiple pull_requests entries", Run(pulls: [Pull(), Pull()]), Repository());
    Replayed("A head.sha mismatch", Run(pulls: [Pull(headSha: new string('f', 40))]), Repository());
    Console.WriteLine("PASS non-main bases, forks, empty or multiple PR entries and head mismatches are replayed");

    foreach (var status in new[] { "ahead", "diverged", "" })
        Replayed("A push not reachable from main (" + status + ")", push, Repository(headOnMain: status));
    Replayed("A push to another branch", Run(trigger: "push", pulls: []), Repository());
    Replayed("A merge base not on main", Run(), Repository(baseOnMain: "ahead"));
    Replayed("An ambiguous main ref", push, Repository(mainRef: "refs/tags/main"));
    Replayed("An unresolvable main ref", push, path => path == "git/ref/heads/main"
        ? Json("""[{"ref":"refs/heads/main-old"}]""") : Repository()(path));
    Console.WriteLine("PASS a push not reachable from main, or an ambiguous or unresolved main ref, is replayed");

    foreach (var unknown in new[] { "", mergeBase[..7], new string('z', 40) })
        Replayed("An unknown merge base", Run(), Repository(knownBase: unknown));
    Replayed("An unavailable merge base", Run(), unavailable);
    Replayed("A push with unavailable metadata", push, unavailable);
    Replayed("A comparison without a merge base", Run(), path => path.StartsWith("compare/" + baseCommit,
        StringComparison.Ordinal) ? Json("{}") : Repository()(path));
    Replayed("A truncated tree listing", Run(), Repository(truncated: true));
    foreach (var untrusted in new[] { Run(trigger: "workflow_dispatch", branch: "main"), Run(commit: "abc123"),
        Json("""{"event":"push","head_branch":"main","head_repository":null}"""), Json("{}") })
        Replayed("Untrusted run metadata " + untrusted, untrusted, Repository());
    Console.WriteLine("PASS unknown merge bases, unavailable trees, other events and missing fields are replayed");
});
Console.WriteLine($"All {checks} certified library donor checks passed.");
