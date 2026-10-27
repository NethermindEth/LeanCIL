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
Console.WriteLine($"All {checks} certified library donor checks passed.");
