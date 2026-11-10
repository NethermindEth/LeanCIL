#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ProofCostReport.cs
#:include Verification.cs
#:include CertifiedLibraryDonor.cs
#:include ExportVerificationSuites.cs
#:include VerificationGroupRunner.cs
#:include VerificationSuites.cs

using System.Text.Json;
using static ProofCostReport;

static void Require(bool condition, string claim)
{
    if (!condition) throw new InvalidOperationException("Proof cost regression failed: " + claim);
    Console.WriteLine("PASS " + claim);
}

static string Source([System.Runtime.CompilerServices.CallerFilePath] string path = "") => path;

static Row Proof(string name, long heartbeats, long elapsedMs = 100, string group = "Tests.Sample") =>
    new(group, name, "theorem", new(StringComparer.Ordinal) { ["heartbeats"] = heartbeats, ["elapsedMs"] = elapsedMs });

static Row Module(long heartbeats, long oleanBytes, string group = "Tests.Sample") =>
    new(group, ModuleRow, ModuleKind,
        new(StringComparer.Ordinal) { ["heartbeats"] = heartbeats, ["oleanBytes"] = oleanBytes });

static Measurement Tree(string label, params Row[] rows) => new(Schema, label, [.. rows], []);

static Comparison Against(Row before, Row after, params Accepted[] accepted) =>
    Compare(Tree("base", before), Tree("head", after), accepted);

// A proof that costs more than the threshold and the floor allow is what the check exists to stop.
var inflated = Against(Proof("slow", 10_000_000), Proof("slow", 12_000_000));
Require(inflated.Failed && inflated.Regressions.Single() is { Name: "slow", Measure: "heartbeats" },
    "a proof whose heartbeats grow by 20% fails");
var report = Markdown(inflated);
Require(report.Contains("**Failed:** 1 regressions") && report.Contains("| 10,000,000 | 12,000,000 | +20.0% |") &&
    report.Contains("\"from\": 10000000") && report.Contains("\"to\": 12000000"),
    "the summary names the regression and the entry that would accept it");

// Reruns of one tree differ by a few heartbeats; an unchanged proof must never fail on that.
Require(!Against(Proof("same", 75_275_020), Proof("same", 75_275_026)).Failed,
    "run-to-run heartbeat jitter passes");
Require(!Against(Proof("small", 20_000), Proof("small", 60_000)).Failed,
    "a small proof that triples below the absolute floor passes");
Require(!Against(Proof("large", 100_000_000), Proof("large", 104_000_000)).Failed,
    "a large proof that grows by less than the threshold passes");
Require(Against(Proof("large", 100_000_000), Proof("large", 106_000_000)).Failed,
    "a large proof that grows by more than the threshold fails");
Require(!Against(Proof("faster", 12_000_000), Proof("faster", 10_000_000)).Failed, "a cheaper proof passes");

// Elapsed time depends on the runner's load, so it is reported and can never decide the result.
Require(!Against(Proof("timed", 1_000_000, elapsedMs: 100), Proof("timed", 1_000_000, elapsedMs: 100_000)).Failed,
    "elapsed time never fails the comparison");

// Shorter source that builds larger terms shows up as compiled size.
var larger = Against(Module(1_000_000, 1_000_000), Module(1_000_000, 1_200_000));
Require(larger.Regressions.Single().Measure == "oleanBytes", "a module whose olean grows by 20% fails");

// An accepted increase is a reviewed entry for its own values, so it cannot excuse a later regression.
var entry = new Accepted("Tests.Sample", "slow", "heartbeats", 10_000_000, 12_000_000, "stronger statement");
var accepted = Against(Proof("slow", 10_000_000), Proof("slow", 12_000_000), entry);
Require(!accepted.Failed && accepted.UnusedAccepted.Count == 0 &&
    accepted.Changes.Single(change => change.Measure == "heartbeats").Status == Status.Accepted,
    "an accepted increase passes");
// The rerun that checks an accepted entry measures a few heartbeats off the run that printed it.
Require(!Against(Proof("slow", 10_000_006), Proof("slow", 12_000_019), entry).Failed,
    "an accepted increase still passes when a rerun jitters");
Require(Against(Proof("slow", 10_000_000), Proof("slow", 13_000_000), entry).Failed,
    "growth beyond the accepted value still fails");
var stale = Against(Proof("slow", 12_000_000), Proof("slow", 14_000_000), entry);
Require(stale.Failed && stale.UnusedAccepted.Single() == entry,
    "an entry accepted against an older base does not excuse new growth");
var unrelated = Against(Proof("other", 1_000_000), Proof("other", 1_000_000), entry);
Require(!unrelated.Failed && Markdown(unrelated).Contains("matched nothing"),
    "a stale entry is reported and does not fail an unrelated change");

// A new or renamed proof has no base, and its module grows because of it; neither is a regression.
var grown = Compare(Tree("base", Proof("old", 9_000_000), Module(9_000_000, 100_000)),
    Tree("head", Proof("old", 9_000_000), Proof("added", 9_000_000), Module(18_000_000, 200_000)), []);
Require(!grown.Failed && grown.Changes.Any(change => change.Status == Status.Added),
    "a module that gained a proof is not blamed for that proof's cost");
var renamed = Compare(Tree("base", Proof("old", 9_000_000), Module(9_000_000, 100_000)),
    Tree("head", Proof("renamed", 9_000_000), Module(9_000_000, 100_000)), []);
Require(!renamed.Failed && renamed.Changes.Any(change => change.Status == Status.Removed),
    "added and removed rows are reported only");
// With the same proofs on both sides, a module that grows did so because its proofs cost more.
var heavier = Compare(Tree("base", Proof("old", 40_000), Module(9_000_000, 100_000)),
    Tree("head", Proof("old", 45_000), Module(18_000_000, 100_000)), []);
Require(heavier.Regressions.Single() is { Name: ModuleRow, Measure: "heartbeats" },
    "a module with the same proofs that costs more fails");

// A proof that stops being measurable would otherwise leave the table without anyone noticing.
var lost = Compare(Tree("base", Proof("gone", 1_000_000), Proof("kept", 1, group: "Tests.Other")),
    new Measurement(Schema, "head", [Proof("kept", 1, group: "Tests.Other")],
        [new Unmeasured("Tests.Sample", "unknown module")]), []);
Require(lost.Failed && lost.Failures.Single().Contains("unknown module"),
    "a proof measured at the base but not at the head fails");
Measurement Partial(string label) => new(Schema, label, [Proof("kept", 1)], [new Unmeasured("Lost", "reason")]);
var neverMeasured = Compare(Partial("base"), Partial("head"), []);
Require(!neverMeasured.Failed && Markdown(neverMeasured).Contains("Not measured at the head"),
    "a proof neither side can measure is listed without failing");
Require(Compare(Tree("base", Proof("twice", 1), Proof("twice", 2)), Tree("head", Proof("twice", 1)), [])
        .Failed,
    "a measurement that repeats a row fails");
Require(Compare(Tree("base"), Tree("head"), []).Failed, "a head with nothing measured fails");
// A suite the base lacks leaves nothing to compare, which must not read as a pass.
var baseless = Compare(Tree("base"), Tree("head", Proof("new", 9_000_000)), []);
Require(!baseless.Failed && Markdown(baseless).Contains("**Not compared:**") &&
    !Markdown(baseless).Contains("**Passed:**"), "a base with nothing measured is reported as not compared");
// A regression in a shared tactic reaches thousands of rows; the job summary has a size limit.
var many = Compare(Tree("base", [.. Enumerable.Range(0, 500).Select(index => Proof($"proof{index}", 1_000_000))]),
    Tree("head", [.. Enumerable.Range(0, 500).Select(index => Proof($"proof{index}", 2_000_000))]), []);
Require(many.Regressions.Count() == 500 && Markdown(many).Contains("The largest 100 are listed") &&
    Markdown(many).Length < 200_000, "a summary of many regressions stays bounded");

// Other producers add rows with their own measures; they are carried and reported and never decide.
static Row Fixture(long milliseconds) => new("stepping-scaling", "64 instructions", "fixture",
    new(StringComparer.Ordinal) { ["msPerInstruction"] = milliseconds, ["proofBytesPerInstruction"] = 4_096 });
var fixture = Compare(Tree("base", Fixture(10)), Tree("head", Fixture(1_000)), []);
Require(!fixture.Failed && Markdown(fixture).Contains("| msPerInstruction | 10 | 1,000 |"),
    "rows with measures this tool does not know are reported only");

var directory = Path.Combine(Path.GetTempPath(), "leancil-proof-cost-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(directory);
try
{
    string Save(string name, Measurement measurement)
    {
        var path = Path.Combine(directory, name);
        File.WriteAllText(path, JsonSerializer.Serialize(measurement, ProofCostReport.Json));
        return path;
    }
    var first = Save("base.json", Tree("base", Proof("slow", 10_000_000)));
    var fixtures = Save("fixtures.json", Tree("base", Fixture(10)));
    var second = Save("head.json", Tree("head", Proof("slow", 12_000_000)));
    var merged = Read([first, fixtures]);
    Require(merged.Rows.Count == 2 && merged.Rows[1].Measures["msPerInstruction"] == 10,
        "measurements from several producers merge into one");
    var markdown = Path.Combine(directory, "report.md");
    Require(ProofCostReport.Run(["compare", "--base", first, "--head", second, "--markdown", markdown]) == 1 &&
        File.ReadAllText(markdown).Contains("### Regressions"), "the command exits nonzero on a regression");
    var acceptedPath = Path.Combine(directory, "accepted.json");
    File.WriteAllText(acceptedPath, JsonSerializer.Serialize(new[] { entry }, ProofCostReport.Json));
    Require(ProofCostReport.Run(["compare", "--base", first, "--head", second, "--accepted", acceptedPath]) == 0,
        "the command exits zero once the increase is accepted");
    Require(ProofCostReport.Run(["compare", "--base", first, "--head", first]) == 0, "an unchanged tree exits zero");
}
finally { Directory.Delete(directory, true); }

// Only the tables that just name a library are test libraries; the shipped and editor libraries are not.
var libraries = TestLibraries("""
    name = "leancil"

    [[lean_lib]]
    name = "CIL"
    globs = ["CIL", "CIL.Observe"]

    # Editor-only modules.
    [[lean_lib]]
    name = "LeanCILEditor"
    srcDir = ".lake/leancil"

    [[lean_lib]]
    name = "Tests.Automation"

    [[lean_exe]]
    name = "leancil-audit"

    [[lean_lib]]
    # A comment does not make the table more than a name.
    name = "Tests.CodeAt"
    """.Replace("\n    ", "\n").Trim());
Require(libraries is ["Tests.Automation", "Tests.CodeAt"], "test libraries are the tables that only name a library");

Require(Imports("""
    /- A header comment
       over two lines. -/
    import CIL.Safety -- trailing comment
    public import Tests.Support.Frames
    import all Extracted

    -- A comment between imports.
    import ExtractedSymbols
    open CIL
    import NotAnImport
    """) is ["CIL.Safety", "Tests.Support.Frames", "Extracted", "ExtractedSymbols"],
    "imports are read up to the first command");

using var commands = JsonDocument.Parse("""
    {"module":"Tests.Sample","commands":[
      {"label":"example","kind":"example","heartbeats":10,"sourceLines":2,"elapsedMs":1},
      {"label":"example","kind":"example","heartbeats":20,"sourceLines":3,"elapsedMs":1},
      {"label":"Tests.Sample.holds","kind":"theorem","heartbeats":30,"kernelHeartbeats":5,"sourceLines":4}]}
    """);
var rows = Rows("Tests.Sample", commands.RootElement, oleanBytes: 512, sourceLines: 12);
Require(rows.Select(row => row.Name).SequenceEqual(["example", "example #2", "Tests.Sample.holds", ModuleRow]) &&
    rows[^1] is { Kind: ModuleKind } total && total.Measures["heartbeats"] == 60 &&
    total.Measures["oleanBytes"] == 512 && total.Measures["sourceLines"] == 12 &&
    total.Measures["kernelHeartbeats"] == 5,
    "repeated labels stay distinct and the module row totals its commands");

// Measuring costs a second verification of each suite, so only what the change can affect is measured.
const string selection = """
    {"include":[{"suite":"core","suites":["core"],"timeout":30},
      {"suite":"wordreader","suites":["wordreader"],"timeout":30},
      {"suite":"docs+cli","suites":["docs","cli"],"timeout":30}]}
    """;
Require(Sources(selection, ["Tests/Loops.cs"]) is ["core", "wordreader"],
    "selected proof suites are measured and other suites are not");
Require(Sources(selection, ["CIL/Safety/Stepping.lean"]) is [LibrariesSource, "core", "wordreader"] &&
    Sources(selection, ["lakefile.toml"]) is [LibrariesSource, ..],
    "a Lean or build change also measures the test libraries");
Require(Sources("""{"include":[{"suite":"docs","suites":["docs"],"timeout":30}]}""", ["docs/CI.md"]) is [],
    "a documentation change measures nothing");

// Main measures each source once. A pull request takes those rows as its base only when the file has
// the digest main's job logged and the same measurer wrote it for that commit; it never measures a base.
var scratch = Directory.CreateTempSubdirectory("proof-cost-test").FullName;
string RowsFile(string directory, string source, params Row[] rows)
{
    Directory.CreateDirectory(Path.Combine(scratch, directory));
    var path = Path.Combine(scratch, directory, source + ".json");
    File.WriteAllText(path, JsonSerializer.Serialize(Tree(source, rows), ProofCostReport.Json));
    return Path.Combine(scratch, directory);
}
RowsFile("measured", "core", Proof("slow", 10_000_000));
RowsFile("measured", "wordreader", Proof("read", 10_000_000));
RowsFile("measured", "loops");
var bundle = Path.Combine(scratch, "proof-cost-rows.json");
var published = Publish(Path.Combine(scratch, "measured"), "measurer", "base commit");
Require(published.Sources.Keys.SequenceEqual(["core", "wordreader"]),
    "a source main measured without rows is not published as a base");
File.WriteAllText(bundle, JsonSerializer.Serialize(published, ProofCostReport.Json));
var digest = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(bundle)));
var baseRows = PublishedRows(bundle, digest, "measurer", "base commit");
Require(baseRows.Keys.Order().SequenceEqual(["core", "wordreader"]) && baseRows["core"].Rows.Single().Name == "slow",
    "published rows are the base of the sources they hold");
Require(PublishedRows(null, null, "measurer", "base commit").Count == 0 &&
    PublishedRows(bundle, digest, "another measurer", "base commit").Count == 0 &&
    PublishedRows(bundle, digest, "measurer", "another commit").Count == 0,
    "no file, another measurer's rows and another commit's rows are no base");
var forged = false;
try { PublishedRows(bundle, digest[..63] + (digest[63] == '0' ? '1' : '0'), "measurer", "base commit"); }
catch (InvalidDataException) { forged = true; }
Require(forged, "rows without the digest their publisher logged are refused");

// Published rows are a base only for a run that measures its head the same way, down to the workflow
// steps that call the measurer; an edit elsewhere in the workflow keeps them.
var workflow = File.ReadAllText(Path.Combine(Path.GetDirectoryName(Source())!, "..", ".github", "workflows",
    "verification.yml")).ReplaceLineEndings("\n");
var suitesStep = WorkflowStep(workflow, MeasuringSteps[0]);
Require(MeasuringSteps.All(step => WorkflowStep(workflow, step).Contains("measure", StringComparison.Ordinal)) &&
    suitesStep.Contains("measure-suites", StringComparison.Ordinal) &&
    !suitesStep.Contains("--libraries", StringComparison.Ordinal),
    "each measuring step of the workflow is found, whole and alone");
Require(MeasurerKey(workflow) == MeasurerKey() &&
    MeasurerKey(workflow.Replace("measure-suites --tree .", "measure-suites --tree base")) != MeasurerKey(workflow) &&
    MeasurerKey(workflow.Replace("name: Build and verify", "name: Build, verify")) == MeasurerKey(workflow),
    "a change to a measuring step changes the measurer, and a change to another job does not");
// A suite's rows are the directories it declares, so a suite that shares a job is measured alone. The
// member running when a report was written must be its owner: anything else is a row that would be
// counted for the wrong suite, or for none, and stops the measurement.
Require(VerificationSuites.ProofOutputs.Keys.Order().SequenceEqual(VerificationSuites.ProofSuites.Order()),
    "every proof suite declares its output directories");
Require(Owner("ProofOutlines/control/Outlines/Choose") == "outlines-control" &&
    Owner("ConsumerSupportUnion-7c43a93156a9/Extraction0") == "core" && Owner("AddModel") == "core" &&
    Owner("StructOutlines/Narrow") == "structoutlines" && Owner("CheckedConversions/conv_ovf_i1-32") is null &&
    Owner("Additional") is null, "an output belongs to the one suite that declares its directory");
var noon = new DateTime(2026, 11, 10, 12, 0, 0, DateTimeKind.Utc);
Require(Owner("CertificateReuse-56769cb9/OtherExtraction") == "core" &&
    Misattributed([new("core", noon, 0)],
        [("CertificateReuse-56769cb9/OtherExtraction", noon.AddSeconds(30))]).Count == 0,
    "certificate reuse outputs remain owned by core so its proof cost is measured");
Require(Owner("ProofBindingFamilies/Equal32_scalar") == "core" &&
    Misattributed([new("core", noon, 0)],
        [("ProofBindingFamilies/Equal32_scalar", noon.AddSeconds(30))]).Count == 0,
    "certified binding families are included in core proof measurements");
VerificationGroupRunner.SuiteRun[] members =
[
    new("conversions", noon, 0), new("receiveroutlines", noon.AddMinutes(1), 0),
    new("exportsprotected", noon.AddMinutes(2), 0)
];
Require(Misattributed(members,
    [
        ("CheckedConversions/conv_ovf_i1-32", noon.AddSeconds(30)), ("ReceiverLoopOutlines/Drain", noon.AddSeconds(90)),
        ("ContractExport-95758c4a/Package", noon.AddMinutes(3)),
        ("suite-caches/receiveroutlines/x", noon.AddSeconds(95))
    ]).Count == 0, "a grouped job whose members wrote only their own outputs is measured");
Require(Misattributed(members, [("ReceiverLoopOutlines/Drain", noon.AddMinutes(3))]).Single() is
    { Suite: "receiveroutlines", Problem: var twice } &&
    twice.Contains("belongs to receiveroutlines and was written while exportsprotected ran"),
    "an output of a proof suite that another member wrote is attributed to two suites and fails that suite");
Require(Misattributed(members, [("Undeclared/Drain", noon.AddSeconds(90))]).Single() is
    { Suite: "receiveroutlines", Problem: var undeclared } &&
    undeclared.Contains("verified by receiveroutlines, which does not declare it"),
    "an output a proof suite wrote outside its directories cannot be attributed and fails that suite");

// One job reports every source. Without published base rows a source is not compared and cannot fail,
// which is the only way to pass uncompared: with a base, missing head rows are a failure.
RowsFile("head", "core", Proof("slow", 12_000_000));
RowsFile("head", "loops", Proof("fresh", 9_000_000));
var reports = Report(["core", "loops", "libraries", "wordreader"], baseRows, Path.Combine(scratch, "head"), [],
    DefaultThresholdPercent).ToDictionary(report => report.Source, report => report.Comparison);
Require(reports["core"] is { } core && core.Regressions.Single().Name == "slow" && Markdown(core, "core")
    .StartsWith("## Proof cost of core against the merge base", StringComparison.Ordinal),
    "each source is compared with its own base and titled by its name");
Require(reports["loops"] is null && reports["libraries"] is null,
    "a source main published no rows for is not compared, with or without head rows");
Require(reports["wordreader"] is { Failed: true } unmeasured &&
    unmeasured.Failures.Contains("nothing was measured at the head"),
    "a source with a published base and no head rows fails");
Require(Report(["core", "loops"], PublishedRows(null, null, "measurer", "base commit"),
    Path.Combine(scratch, "head"), [], DefaultThresholdPercent).All(report => report.Comparison is null),
    "a merge base main published nothing for compares no source");Directory.Delete(scratch, true);

Console.WriteLine("All proof cost checks passed.");
