#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationSelection.cs
#:include Documentation.cs
#:include ExportVerificationSuites.cs
#:include VerificationSuites.cs

using System.Diagnostics;
using System.Text.RegularExpressions;

var checks = 0;
var root = VerificationSelection.Root;
string[] All() => VerificationSelection.SuiteInputs().Keys.Order(StringComparer.Ordinal).ToArray();
void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}
void Equal(IEnumerable<string> actual, IEnumerable<string> expected)
{
    Require(actual.SequenceEqual(expected, StringComparer.Ordinal),
        $"Expected [{string.Join(", ", expected)}], got [{string.Join(", ", actual)}]");
}
void Test(string name, Action action)
{
    action();
    checks++;
    Console.WriteLine("PASS " + name);
}

Test("longest-first preserves selection", () =>
{
    var selected = VerificationSelection.Select(["Tests/Loops.cs", "Tests/UnsafeLayouts.cs", "Tests/IntegerMath.cs"]);
    Equal(VerificationSelection.Schedule(selected), ["unsafe", "loops", "math"]);
    Equal(VerificationSelection.Schedule(All()).Order(StringComparer.Ordinal), All());
    Equal(VerificationSelection.Schedule(["loops", "newlongsuite"]), ["newlongsuite", "loops"]);
    Equal(VerificationSelection.Schedule([]), []);
});
Test("measured schedule reduces estimated tail without skipping jobs", () =>
{
    var durations = VerificationSelection.ReadDurations();
    double Makespan(IEnumerable<string> order, int workers)
    {
        var available = new PriorityQueue<double, double>();
        for (var i = 0; i < workers; i++) available.Enqueue(0, 0);
        foreach (var name in order)
        {
            var end = available.Dequeue() + durations.GetValueOrDefault(name, durations.Values.Max() + 1);
            available.Enqueue(end, end);
        }
        return available.UnorderedItems.Max(item => item.Element);
    }
    Require(Makespan(VerificationSelection.Schedule(All()), 8) < Makespan(All(), 4),
        "Measured scheduling did not improve the simulated tail");
});
Test("short groups preserve selection, isolation and bounded duration", () =>
{
    var durations = VerificationSelection.ReadDurations();
    var groups = VerificationSelection.Groups(All());
    Equal(groups.SelectMany(group => group.Suites).Order(StringComparer.Ordinal), All());
    // Every job repeats setup and restores, so a full run must not go back to one job per suite.
    double Seconds(VerificationSelection.Group group) => group.Suites.Sum(suite => durations[suite]);
    var target = VerificationSelection.GroupSeconds(durations);
    var longest = durations.MaxBy(suite => suite.Value);
    Require(groups.Length <= All().Length / 3, "Suites were not packed: " + groups.Length + " jobs");
    // The target is one runner's share of a round, with the fewest rounds that fit under the longest suite.
    var rounds = durations.Values.Sum() / (VerificationSelection.Runners * target);
    Require(target <= longest.Value && Math.Abs(rounds - Math.Round(rounds)) < 1e-9 &&
        (rounds < 1.5 || durations.Values.Sum() / (VerificationSelection.Runners * (rounds - 1)) > longest.Value),
        "The target is not the fewest whole rounds under the longest suite");
    // A refreshed table moves the target; the longest suites may then swap places without unbalancing a run.
    var refreshed = new Dictionary<string, double>(durations) { ["evidence"] = longest.Value - 100 };
    Require(VerificationSelection.GroupSeconds(refreshed) <= longest.Value &&
        VerificationSelection.GroupSeconds(new Dictionary<string, double> { ["only"] = 90 }) == 90.0 / 8,
        "The target follows the measured total, not one suite");
    // The longest suite alone bounds the run; no packed job may outlast it or approach its timeout.
    Require(groups[0].Suites is [var alone] && alone == longest.Key, "The longest suite shares its job");
    foreach (var group in groups.Where(group => group.Suites.Length > 1))
        Require(group.Suites.Length <= VerificationSelection.GroupMembers && Seconds(group) <= target &&
            Seconds(group) <= group.Timeout * 60 / 2, "Unbounded group: " + group.Suite);
    // A short job at the tail would queue behind the runner cap and finish last for no reason.
    Require(groups.Zip(groups.Skip(1)).All(pair => Seconds(pair.First) >= Seconds(pair.Second)),
        "Jobs do not start longest first");
    Require(groups.Select(group => group.Suite).Distinct().Count() == groups.Length &&
        groups.All(group => group.Suite.StartsWith(group.Suites[0], StringComparison.Ordinal) &&
            Regex.IsMatch(group.Suite, @"\A[a-z+-]+(\+\d+more)?\z")), "A job name is ambiguous or not its first suite");
    // Eight runners, with the setup every job repeats: packing must cost neither wall time nor jobs.
    const double setupSeconds = 52;
    double Wall(IEnumerable<double> jobs)
    {
        var runners = new PriorityQueue<double, double>();
        for (var i = 0; i < VerificationSelection.Runners; i++) runners.Enqueue(0, 0);
        foreach (var job in jobs)
        {
            var end = runners.Dequeue() + job + setupSeconds;
            runners.Enqueue(end, end);
        }
        return runners.UnorderedItems.Max(item => item.Element);
    }
    var single = VerificationSelection.Schedule(All()).Select(suite => durations[suite]).ToArray();
    Require(Wall(groups.Select(Seconds)) <= Wall(single), "Packing lengthened the simulated run");
    Require((single.Length - groups.Length) * setupSeconds >= 30 * 60, "Packing saves under thirty job-minutes");
    // A job measures proof cost exactly when it runs a proof suite, alone or grouped with others.
    foreach (var group in groups)
        Require(group.Proof == group.Suites.Any(VerificationSuites.ProofSuites.Contains),
            "Proof cost is measured in the wrong job: " + group.Suite);
    Require(groups.Any(group => group.Proof && group.Suites.Length > 1), "No proof suite shares a job");
    // The libraries take minutes to measure; a job near its timeout would fail a suite that passed.
    Require(groups.Single(group => group.Libraries) == groups[^1] &&
        Seconds(groups[^1]) + 8 * 60 <= groups[^1].Timeout * 60,
        "The libraries are not measured in the shortest job, or leave it no time");
    Require(VerificationSelection.Groups(["unsafe"]).Single().Libraries,
        "A run of one job measures no libraries");
    Equal(VerificationSelection.Groups(["contracts", "unknown"]).SelectMany(group => group.Suites),
        ["unknown", "contracts"]);
    Require(VerificationSelection.Groups([]).Length == 0, "Empty selection gained suites");
});
Test("docs only", () =>
{
    Equal(VerificationSelection.Select(["README.md", "docs/design.md"]), ["docs"]);
    Equal(VerificationSelection.Select(["skills/leancil/SKILL.md"]), ["docs"]);
    Equal(VerificationSelection.Select(["AGENTS.md", "LICENSE"]), []);
});
Test("main and manual always full", () =>
{
    foreach (var eventName in new[] { "push", "workflow_dispatch" })
        Equal(VerificationSelection.Select(["README.md"], eventName), All());
});
Test("test entry points", () =>
{
    foreach (var path in new[] { "Tests/ProofBindingCatalog.cs", "Tests/ProofBindingFamilies.cs",
        "Tests/BindingFamilies/Bindings.json", "Tests/BindingFamilies/Negative.json",
        "Tests/BindingFamilies/Binding.lean.in", "Tests/BindingFamilies/Methods.cs",
        "Tests/BindingFamilies/Support.lean", "Tests/GatePlans.cs", "Tests/PublicProofSurface.lean" })
    {
        var selected = VerificationSelection.Select([path]);
        Require(selected.Contains("core") && selected.All(suite => suite is "core" or "docs"),
            "Binding and public-surface fixtures must select core without unrelated suites: " + path);
    }
    Equal(VerificationSelection.Select(["Tests/Loops.cs"]), ["loops"]);
    foreach (var path in new[] { "Tests/ProofCostFrontend.cs", "Tests/ProofCostDiscovery.lean" })
        Equal(VerificationSelection.Select([path]), ["core"]);
    Equal(VerificationSelection.Select(["Tests/SteppingScaling.cs"]), ["stepping"]);
    foreach (var module in new[] { "OperationFacts", "VectorLocalCalls", "SimdCarryCalls" })
        Equal(VerificationSelection.Select([$"Tests/{module}.lean"]), ["core"]);
    Equal(VerificationSelection.Select(["Tests/ProofOutlines.cs"]),
        ["outlines-buffers", "outlines-control", "outlines-objects"]);
    Equal(VerificationSelection.Select(["Tests/StructOutlines.cs"]), ["structoutlines"]);
    Equal(VerificationSelection.Select(["Tests/ReceiverLoopOutlines.cs"]), ["receiveroutlines"]);
    Equal(VerificationSelection.Select(["Tests/WordReaderOutlines.cs"]), ["wordreader"]);
    Equal(VerificationSelection.Select(["Tests/SavedWordReaderOutlines.cs"]), ["savedwordreader"]);
    Equal(VerificationSelection.Select(["Tests/WordReaderOutlineSupport.cs"]), ["savedwordreader", "wordreader"]);
    Equal(VerificationSelection.Select(["Tests/SkipInitialization.cs"]), ["unsafe"]);
    Equal(VerificationSelection.Select(["Tests/NullReferences.cs"]), ["unsafe"]);
    foreach (var name in new[] { "BatchVerification", "VerificationCache", "VerificationReuse" })
        Equal(VerificationSelection.Select([$"Tests/{name}.cs"]), ["core"]);
    Equal(VerificationSelection.Select(["Tests/StaticScalarValues.cs"]), ["evidence"]);
    Equal(VerificationSelection.Select(["Tests/MetadataDifferential.cs"]), ["evidence"]);
    Equal(VerificationSelection.Select(["Tests/GeneratedEvidence.cs"]),
        ["assemblies", "blocks", "dispatch", "enums", "evidence", "excluded", "generics", "intrinsics", "lookups",
            "scaling", "unsafe"]);
    Equal(VerificationSelection.Select(["Tests/GenericOwners.cs"]), ["generics"]);
    Equal(VerificationSelection.Select(["Tests/MultiAssemblyGenerics.cs"]), ["assemblies"]);
    Equal(VerificationSelection.Select(["Tests/MultiAssemblyFixture.cs"]), ["assemblies", "cli"]);
    Equal(VerificationSelection.Select(["Tests/GenericLayouts.cs"]), ["generics"]);
    Equal(VerificationSelection.Select(["Tests/NativeManagedDispatch.cs"]), ["dispatch"]);
    Equal(VerificationSelection.Select(["Tests/NativeMethodTables.lean"]), ["dispatch"]);
    Equal(VerificationSelection.Select(["Tests/ConstrainedEvidence.lean"]), ["dispatch"]);
    Equal(VerificationSelection.Select(["Tests/StackAllocationEvidence.lean"]), ["dispatch"]);
    Equal(VerificationSelection.Select(["Tests/ManagedPointerValues.lean"]), ["evidence"]);
    Equal(VerificationSelection.Select(["Tests/CompilerCorpusCoverage.cs"]), ["dispatch"]);
    foreach (var name in new[]
        { "AggregateSpans", "ViewAccessors", "BinarySpans", "SpanConstructors", "AggregateSpanFill", "AggregateArrays" })
        Equal(VerificationSelection.Select([$"Tests/{name}.cs"]), ["unsafe"]);
    Equal(VerificationSelection.Select(["Tests/VectorStorage.cs"]), ["unsafe"]);
    Equal(VerificationSelection.Select(["Tests/VectorStorage.lean"]), ["unsafe"]);
    // Sources compiled into the extractor change the self-admission scan, as does its baseline.
    Equal(VerificationSelection.Select(["Tests/SelfAdmissionBaseline.txt"]), ["blockers"]);
    // Suites run the built command, so a script compiled into it selects every suite; `leancil workspace`,
    // `watch`, contract export and verify reports are reached by no include edge.
    var everySuite = VerificationSelection.SuiteInputs().Keys.Order(StringComparer.Ordinal).ToArray();
    foreach (var script in new[]
        { "scripts/ContractExport.cs", "scripts/ProofWorkspace.cs", "scripts/ProofWatch.cs", "scripts/VerifyReports.cs" })
        Equal(VerificationSelection.Select([script]), everySuite);
});
Test("proof and transitive imports", () =>
{
    Equal(VerificationSelection.Select(["Examples/Proofs/Countdown.lean"]), ["cli", "contracts", "fsharp", "loops"]);
    Equal(VerificationSelection.Select(["Tests/Support.lean"]), All());
    Equal(VerificationSelection.Select(["Tests/UnsafeCallEvidence.lean"]), ["unsafe"]);
    // A proof a documented command verifies changes what that command prints.
    Require(VerificationSelection.Select(["Examples/Proofs/PastEnd.lean"]).Contains("docs"),
        "A proof the getting-started walkthrough verifies does not select the docs suite");
});
Test("dynamic proof paths", () =>
{
    bool Owns(string path, string suite) => VerificationSelection.Select([path]).Contains(suite);
    Require(Owns("Examples/Proofs/Negate64.lean", "integer"), "Missing integer proof owner");
    Require(Owns("Examples/Proofs/GenericIdentity.lean", "contracts"), "Missing generic proof owner");
    Require(Owns("Examples/Proofs/ConstructorValue.lean", "fsharp"), "Missing F# proof owner");
});
Test("shared unknown and workflow inputs", () =>
{
    foreach (var path in new[] { "CIL/Safety/Memory.lean", "Extractor/UnsafeModels.cs", "global.json",
        "Examples/Assembly/SkipInitialization.cs", "Tests/NewTest.cs", ".github/workflows/verification.yml",
        "scripts/SelectVerification.cs" })
        Equal(VerificationSelection.Select([path]), All());
});
Test("other workflows do not rerun suites", () =>
{
    Equal(VerificationSelection.Select([".github/workflows/arm64-aes.yml", ".github/workflows/runtime-profiles.yml"]),
        []);
    Equal(VerificationSelection.Select([".github/workflows/arm64-aes.yml", "Tests/Loops.cs"]), ["loops"]);
});
Test("multiple changes and deleted paths", () =>
{
    Equal(VerificationSelection.Select(["README.md", "Tests/Loops.cs", "Tests/Division.cs"]),
        ["division", "docs", "loops"]);
    Equal(VerificationSelection.Select(["Tests/Deleted.cs"]), All());
});
Test("every registered suite has its entry point", () =>
{
    Equal(VerificationSuites.Names().Order(StringComparer.Ordinal), All());
    Require(VerificationSuites.Names().Distinct(StringComparer.Ordinal).Count() == VerificationSuites.Names().Length,
        "A suite name is registered twice");
    foreach (IndependentSuite suite in VerificationSuites.Independent)
        Require(File.Exists(Path.Combine(root, suite.Script)), "No entry point: " + suite.Name);
    foreach (var (suite, inputs) in VerificationSelection.SuiteInputs())
        Require(inputs.Count > 0, "No entry point: " + suite);
});
void MustReject(Action action)
{
    try { action(); }
    catch (ArgumentException) { return; }
    catch (InvalidDataException) { return; }
    catch (InvalidOperationException) { return; }
    throw new InvalidOperationException("Invalid export routing/coverage was accepted.");
}
Test("independent export cohort map preserves 23 leaves, 49 base cases and one discovery completion", () =>
{
    Dictionary<string, (string Cohort, string[] Cases)> expected = new(StringComparer.Ordinal)
    {
        ["exports"] = ("core", ["core.unrelated", "core.definition", "core.wrapper-true", "core.publication",
            "core.caller", "core.internal", "core.instance", "core.generic", "core.virtual", "core.static-values",
            "core.initialized", "core.imports", "core.profile", "core.reference",
            "core.bundle-location", "core.framework-change", "core.interface-text", "core.duplicate",
            "core.partial-publication", "core.body-rebuild", "core.published-closure", "core.incorrect-post"]),
        ["exportsaudit"] = ("audit", ["audit.proof-source", "audit.wrapper-artifact"]),
        ["exportsprotected"] = ("protected", ["protected.publication", "protected.caller", "protected.visibility"]),
        ["exportsresolution"] = ("resolution", ["resolution.same-files", "resolution.changed-file"]),
        ["exportsfullconsumer"] =
            ("consumer", ["full.consumer-explicit", "full.consumer-repeat", "full.artifact-mode"]),
        ["exportsfullordinary"] = ("ordinary", ["full.ordinary"]),
        ["exportsfullpair"] = ("pair", ["full.pair"]),
        ["exportsfullchecks"] = ("checks", ["full.missing-bundle", "full.inventory-bytes", "full.producer-bytes",
            "full.unrecorded-olean", "full.deployed-dll", "full.stale-closure", "full.statement-digest",
            "full.extra-premise"]),
        ["exportsfulltheorems"] = ("theorems", ["full.producer-true", "full.producer-definition"]),
        ["exportsfullcomposition"] = ("composition", ["full.composition-true"]),
        ["exportsmutationordinary"] = ("ordinary-artifact", ["full.ordinary-artifact"]),
        ["exportsmutationconsumer"] = ("consumer-artifact", ["full.consumer-artifact"]),
        ["exportsmutationsource"] = ("consumer-source", ["full.consumer-source"]),
        ["exportsmutationshadow"] = ("consumer-shadow", ["full.consumer-shadow"]),
        ["exportsstatics"] = ("statics", []),
        ["exportsfullstatics"] = ("fullstatics", []),
        ["exportstransitive"] = ("transitive", []),
        ["exportstransitiveoutcomes"] = ("transitiveoutcomes", []),
        ["exportsdiscovery"] = ("discovery", ["discovery.fixture"]),
        ["exportstyped"] = ("typed", []),
        ["exportsderived"] = ("derived", []),
        ["exportsinitialized"] = ("initialized", []),
        ["exportsprofiles"] = ("profiles", [])
    };
    void ExactPlan(IEnumerable<ExportSuite> plan)
    {
        ExportSuite[] actual = plan.ToArray();
        Equal(actual.Select(entry => entry.Name).Order(StringComparer.Ordinal),
            expected.Keys.Order(StringComparer.Ordinal));
        foreach (ExportSuite entry in actual)
        {
            Require(entry.Cohort == expected[entry.Name].Cohort, "Wrong cohort: " + entry.Name);
            Equal(entry.Cases, expected[entry.Name].Cases);
            var standalone =
                entry.Cohort is "statics" or "fullstatics" or "transitive" or "transitiveoutcomes" or "typed" or
                    "derived" or "initialized" or "profiles";

            Require(entry.Standalone == standalone, "Wrong standalone fixture kind: " + entry.Name);
            Require(entry.ChildScript == (entry.Cohort == "discovery" ? "Tests/ContractDiscovery.cs" : null),
                "Wrong bootstrapped child fixture: " + entry.Name);
            string script = entry.Cohort switch
            {
                "resolution" => "Tests/FullModuleResolution.cs",
                "statics" or "fullstatics" => "Tests/ModularStaticExports.cs",
                "transitive" => "Tests/TransitiveImports.cs",
                "transitiveoutcomes" => "Tests/TransitiveOutcomes.cs",
                "typed" => "Tests/GenericLayoutImports.cs",
                "derived" => "Tests/DerivedContractExports.cs",
                "initialized" => "Tests/InitializedExports.cs",
                "profiles" => "Tests/ProfileFamilies.cs",
                _ => "Tests/ContractExport.cs"
            };
            Require(entry.Script == script,
                "Wrong fixture: " + entry.Name);
            string[] arguments = entry.Cohort switch
            {
                "fullstatics" => ["--full-composition"],
                "resolution" => [],
                _ => standalone ? [] : ["--cohort", entry.Cohort]
            };
            Equal(entry.Arguments, arguments);
        }
    }
    ExportSuite[] all = ExportVerificationSuites.Plan();
    ExactPlan(all);
    string[] baseCases = all.Where(entry => entry.Cohort != "discovery").SelectMany(entry => entry.Cases).ToArray();
    Require(baseCases.Length == 49 && baseCases.Distinct(StringComparer.Ordinal).Count() == 49,
        "Lost or duplicate base behavior");
    Require(all.SelectMany(entry => entry.Cases).Count() == 50 &&
        all.SelectMany(entry => entry.Cases).Distinct(StringComparer.Ordinal).Count() == 50,
        "Lost or duplicate discovery completion");
    Equal(ExportVerificationSuites.DiscoveryArguments("sidecar", "caller-proof", "caller-package", "producer-package",
            "producer-proof", "interface-source"),
        ["sidecar", "caller-proof", "caller-package", "producer-package", "producer-proof", "interface-source"]);
    foreach (ExportSuite omitted in all)
        MustReject(() => ExactPlan(all.Where(entry => entry.Name != omitted.Name)));
    static bool OnlyFullCases(ExportSuite entry) =>
        entry.Cases.Length != 0 && entry.Cases.All(id => id.StartsWith("full.", StringComparison.Ordinal));
    Equal(ExportVerificationSuites.FullPlan().Select(entry => entry.Name),
        all.Where(OnlyFullCases).Select(entry => entry.Name));
    Equal(ExportVerificationSuites.FullPlan().Select(entry => entry.Cohort).Order(StringComparer.Ordinal),
        new[] { "composition", "consumer", "ordinary", "pair", "checks", "theorems",
            "ordinary-artifact", "consumer-artifact", "consumer-source", "consumer-shadow" }
            .Order(StringComparer.Ordinal));
    foreach (ExportSuite entry in all)
    {
        if (!entry.Standalone && entry.Cohort != "resolution")
            Require(ExportVerificationSuites.Select(entry.Arguments) == entry.Cohort, "Wrong ContractExport dispatch");
        if (OnlyFullCases(entry))
            Require(ExportVerificationSuites.Select(["--cohort", entry.Cohort], full: true) == entry.Cohort,
                "Wrong full dispatch");
    }
});
Test("export coverage detects each omitted completion and invalid selection", () =>
{
    Require(ExportVerificationSuites.Select([]) is null && ExportVerificationSuites.Select([], full: true) is null,
        "Default standalone must aggregate leaves");
    foreach (string[] invalid in new string[][] {
        ["--cohort"], ["--cohort", "unknown"], ["--cohort", "core", "--cohort", "core"], ["core"],
        ["--cohort", "resolution"], ["--cohort", "statics"], ["--cohort", "fullstatics"], ["--cohort", "transitive"],
        ["--cohort", "transitiveoutcomes"], ["--cohort", "typed"], ["--cohort", "derived"] })
        MustReject(() => ExportVerificationSuites.Select(invalid));
    string[] nonFullCohorts =
        ["core", "audit", "protected", "resolution", "statics", "fullstatics", "transitive", "transitiveoutcomes",
            "discovery", "typed", "derived", "unknown"];

    foreach (string cohort in nonFullCohorts)
    {
        Require(!ExportVerificationSuites.IsFull(cohort),
            "Standalone or unknown cohort entered full verification: " + cohort);
        MustReject(() => ExportVerificationSuites.Select(["--cohort", cohort], full: true));
    }
    ExportSuite[] all = ExportVerificationSuites.Plan();
    MustReject(() => ExportVerificationSuites.Validate([]));
    MustReject(() => ExportVerificationSuites.Validate(all.Append(all[0])));
    MustReject(() => ExportVerificationSuites.Validate([all[0] with { Cases = [] }]));
    foreach (ExportSuite entry in all)
    {
        if (entry.Standalone)
        {
            MustReject(() => new ExportCaseLedger(entry.Cohort));
            MustReject(() => ExportVerificationSuites.Validate([entry with { Cases = ["untracked-standalone-case"] }]));
            continue;
        }
        foreach (string omitted in entry.Cases)
        {
            ExportCaseLedger incomplete = new(entry.Cohort);
            foreach (string id in entry.Cases.Where(id => id != omitted)) incomplete.CompleteCase(id);
            MustReject(incomplete.Finish);
        }
        ExportCaseLedger complete = new(entry.Cohort);
        foreach (string id in entry.Cases) complete.CompleteCase(id);
        complete.Finish();
        MustReject(() => complete.CompleteCase(entry.Cases[0]));
        MustReject(() => complete.CompleteCase("not-a-registered-case"));
    }
});
Test("export leaf selection, strict files and shared inputs", () =>
{
    string[] exports =
        ExportVerificationSuites.Plan().Select(entry => entry.Name).Order(StringComparer.Ordinal).ToArray();
    string[] bootstrap = ExportVerificationSuites.Plan()
        .Where(entry => !entry.Standalone && entry.Cohort != "resolution")
        .Select(entry => entry.Name).Order(StringComparer.Ordinal).ToArray();
    bool Selects(string path, string suite) =>
        VerificationSelection.Select([path]).Contains(suite, StringComparer.Ordinal);
    foreach (string name in exports)
        Require(All().Contains(name, StringComparer.Ordinal), "Missing selected export leaf: " + name);
    foreach (string name in bootstrap)
        Require(Selects("Tests/ContractExport.cs", name), "Bootstrap change lost " + name);
    foreach (ExportSuite entry in ExportVerificationSuites.FullPlan())
        Require(Selects("Tests/FullImportVerification.cs", entry.Name), "Full change lost " + entry.Name);
    Equal(VerificationSelection.Select(["scripts/ExportVerificationSuites.cs"]), All());
    Equal(VerificationSelection.Select(["scripts/VerificationSuites.cs"]), All());
    Equal(VerificationSelection.Select(["Tests/ModularStaticExports.cs"]).Order(StringComparer.Ordinal),
        ["exportsfullstatics", "exportsstatics"]);
    Equal(VerificationSelection.Select(["Tests/TransitiveImports.cs"]), ["exportstransitive"]);
    Equal(VerificationSelection.Select(["Tests/ContractDiscovery.cs"]), ["exportsdiscovery"]);
    Equal(VerificationSelection.Select(["Tests/GenericLayoutImports.cs"]), ["exportstyped"]);
    string[] typedFixtures =
        ["TypedImportInterface", "TypedIdentityProof", "TypedCopyProof", "TypedIdentityCaller", "TypedCopyCaller",
            "TypedChainCaller"];
    foreach (string name in typedFixtures)
        Equal(VerificationSelection.Select(["Tests/ContractImports/" + name + ".lean"]), ["exportstyped"]);
    Equal(VerificationSelection.Select(["Tests/DerivedContractExports.cs"]), ["exportsderived"]);
    Equal(VerificationSelection.Select(["Tests/InitializedExports.cs"]), ["exportsinitialized"]);
    Equal(VerificationSelection.Select(["Tests/ProfileFamilies.cs"]), ["exportsprofiles"]);
    foreach (var name in new[] { "ProfileFamilyContract", "ProfileFamilyProof", "ProfileFamilyCaller" })
        Equal(VerificationSelection.Select(["Tests/ContractImports/" + name + ".lean"]), ["exportsprofiles"]);
    string[] derivedFixtures =
        ["DerivedInterface", "DerivedPercentProof", "DerivedAddProof", "DerivedShiftCaller", "DerivedSumCaller"];
    foreach (string name in derivedFixtures)
        Equal(VerificationSelection.Select(["Tests/ContractImports/" + name + ".lean"]),
            name is "DerivedInterface" or "DerivedPercentProof"
                ? ["exportsderived", "exportstransitiveoutcomes"] : ["exportsderived"]);
    Equal(VerificationSelection.Select(["Tests/TransitiveOutcomes.cs"]), ["exportstransitiveoutcomes"]);
    Equal(VerificationSelection.Select(["Tests/StagedBundleMutation.cs"]), ["exportstransitive"]);
    Require(VerificationSelection.Select(["Tests/ImportedLayouts.lean"]).Contains("evidence", StringComparer.Ordinal),
        "Imported-layout model evidence lost its existing suite owner");
    Equal(VerificationSelection.Schedule(exports).Order(StringComparer.Ordinal), exports);
    string runner = File.ReadAllText(Path.Combine(root, "scripts/Test.cs"));
    Require(runner.Contains("FixtureCommand(script, arguments, preparedFixtures.Contains(script))",
            StringComparison.Ordinal),
        "Runner lost fixture argument forwarding; command behavior is covered by Tests/BuildReuse.cs");
    Require(runner.Contains("ExportVerificationSuites.Plan()", StringComparison.Ordinal) &&
        runner.Contains("projects.Distinct(StringComparer.Ordinal)", StringComparison.Ordinal),
        "Runner lost export leaf registration or build deduplication");
    Require(!runner.Contains("if (name == \"exports\")", StringComparison.Ordinal) &&
        !runner.Contains("projects.Add(\"Tests/ModularStaticExports.cs\")", StringComparison.Ordinal),
        "Old nested static suite remains");
    string standalone = File.ReadAllText(Path.Combine(root, "Tests/ContractExport.cs"));
    bool Has(string text) => standalone.Contains(text, StringComparison.Ordinal);
    Require(Has("foreach (ExportSuite entry in ExportVerificationSuites.Plan())") && Has(".. entry.Arguments"),
        "Standalone lost exact leaf dispatch");
    Require(!Has("\"Tests/TransitiveImports.cs\""), "Old nested transitive suite remains");
    Require(!Has("\"Tests/GenericLayoutImports.cs\""), "Old nested typed suite remains");
    Require(!Has("\"Tests/ContractDiscovery.cs\"") &&
        Has("if (cohort == \"discovery\")") &&
        Has("ExportVerificationSuites.DiscoveryArguments(") &&
        Has("sidecar, callerProof, callerPackage, package, proof, contractSource)"),
        "Discovery lost its selected six-argument child dispatch");
});
Test("a missing registered export fixture fails selection", () =>
{
    string isolated = Path.Combine(root, "artifacts", "MissingExportFixture-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(Path.Combine(isolated, "Tests"));
    try
    {
        File.WriteAllText(Path.Combine(isolated, "Tests/ContractExport.cs"), "");
        // Each fixture in registration order must be reported missing before the next one is checked.
        (string Fixture, string Kind)[] fixtures =
        [
            ("Tests/FullModuleResolution.cs", "resolution"),
            ("Tests/ModularStaticExports.cs", "standalone static"),
            ("Tests/TransitiveImports.cs", "standalone transitive"),
            ("Tests/TransitiveOutcomes.cs", "standalone transitive outcomes"),
            ("Tests/ContractDiscovery.cs", "discovery child"),
            ("Tests/GenericLayoutImports.cs", "standalone typed"),
            ("Tests/DerivedContractExports.cs", "standalone derived"),
            ("Tests/InitializedExports.cs", "standalone initialized")
        ];
        foreach ((string fixture, string kind) in fixtures)
        {
            string? rejection = null;
            try { VerificationSelection.SuiteInputs(isolated); }
            catch (InvalidDataException error) { rejection = error.Message; }
            Require(rejection == "Missing registered export fixture: " + fixture,
                "A missing " + kind + " fixture was silently skipped: " + rejection);
            File.WriteAllText(Path.Combine(isolated, fixture), "");
        }
    }
    finally { Directory.Delete(isolated, recursive: true); }
});
Test("required gate, all 192 actual Bash status combinations", () =>
{
    var bash = OperatingSystem.IsWindows() ? "C:/Program Files/Git/bin/bash.exe" :
        (Environment.GetEnvironmentVariable("PATH") ?? "").Split(Path.PathSeparator)
            .Select(directory => Path.Combine(directory, "bash")).FirstOrDefault(File.Exists);
    if (bash is null || !File.Exists(bash))
        throw new InvalidOperationException("Bash is required to test the actual workflow gate");
    var workflow = File.ReadAllText(Path.Combine(root, ".github/workflows/verification.yml")).ReplaceLineEndings("\n");
    const string marker = "        run: |\n";
    var start = workflow.LastIndexOf(marker, StringComparison.Ordinal);
    Require(start >= 0, "Missing workflow gate");
    var gate = Regex.Replace(workflow[(start + marker.Length)..], @"(?m)^ {10}", "");
    string[] statuses = ["success", "failure", "cancelled", "skipped"];
    foreach (var planned in statuses)
    foreach (var selected in new[] { "true", "false", "" })
    foreach (var prepared in statuses)
    foreach (var tools in statuses)
    foreach (var result in statuses)
    {
        var command = new ProcessStartInfo(bash)
        {
            UseShellExecute = false, CreateNoWindow = true,
            RedirectStandardOutput = true, RedirectStandardError = true
        };
        foreach (var arg in new[] { "-e", "-c", gate }) command.ArgumentList.Add(arg);
        command.Environment["SELECT_RESULT"] = planned;
        command.Environment["HAS_SUITES"] = selected;
        command.Environment["PREPARE_RESULT"] = prepared;
        command.Environment["TOOLS_RESULT"] = tools;
        command.Environment["SUITES_RESULT"] = result;
        using var process = Process.Start(command) ?? throw new InvalidOperationException("Could not start Bash");
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        var expected = planned == "success" && ((selected, prepared, tools, result) is
            ("true", "success", "success", "success") or ("false", "skipped", "skipped", "skipped"));
        string transcript = stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult();
        Require((process.ExitCode == 0) == expected,
            $"Unexpected gate result: {planned}/{selected}/{prepared}/{tools}/{result}\n{transcript}");
    }
});
Test("certified library binding, main republication and observability", () =>
{
    string workflow = File.ReadAllText(Path.Combine(root, ".github/workflows/verification.yml"));
    const string dollar = "$";
    foreach (string text in new[] {
        "needs: [select, prepare, tools]", "needs: [select, prepare, tools, suites]",
        "artifact-ids: " + dollar + "{{ needs.tools.outputs.artifact-id }}", "LEANCIL_PREBUILT_TOOLS: true",
        "LEANCIL_CERTIFIED_LIBRARY_SHA256: " + dollar + "{{ needs.prepare.outputs.manifest-sha256 }}",
        "artifact-ids: " + dollar + "{{ needs.prepare.outputs.artifact-id }}",
        "toolchain-artifact-id: " + dollar + "{{ steps.toolchain-artifact.outputs.artifact-id }}",
        "toolchain-sha256: " + dollar + "{{ steps.pack-toolchain.outputs.sha256 }}",
        "toolchain-pin-sha256: " + dollar + "{{ steps.pack-toolchain.outputs.pin-sha256 }}",
        "artifact-ids: " + dollar + "{{ needs.prepare.outputs.toolchain-artifact-id }}",
        "TOOLCHAIN_SHA256: " + dollar + "{{ needs.prepare.outputs.toolchain-sha256 }}",
        "TOOLCHAIN_PIN_SHA256: " + dollar + "{{ needs.prepare.outputs.toolchain-pin-sha256 }}",
        "run-id: " + dollar + "{{ needs.prepare.outputs.artifact-run-id }}",
        "artifact-id: " + dollar + "{{ steps.library-artifact.outputs.artifact-id || " +
            "steps.donor.outputs.artifact-id }}",
        "artifact-run-id: " + dollar + "{{ steps.library-artifact.outputs.artifact-id && github.run_id || " +
            "steps.donor.outputs.run-id }}",
        "if: steps.certify.outputs.reused != 'true' || " +
            "(github.event_name == 'push' && github.ref == 'refs/heads/main')",
        "--reuse \"" + dollar + "DONATED_SHA256\" \"" + dollar + "{producer[@]}\"",
        "REVIEWED_PRODUCER: " + dollar + "{{ steps.donor.outputs.reviewed-producer }}",
        "if [ \"" + dollar + "REVIEWED_PRODUCER\" = true ]; then producer=(--producer-replayed); fi",
        "name: verification-results-" + dollar + "{{ matrix.suite }}-" + dollar + "{{ github.run_attempt }}",
        // A job measures its own proof suites by the group runner's record of when each started.
        "if: " + dollar + "{{ !cancelled() && matrix.proof }}",
        "dotnet artifacts/verification-fixtures/ProofCost/ProofCost.dll measure-suites",
        "--runs artifacts/verification-suites.json",
        "name: proof-cost-head-rows-" + dollar + "{{ matrix.suite }}-" + dollar + "{{ github.run_attempt }}",
        "pattern: proof-cost-head-rows-*",
        // A pull request compares with the rows main published for its merge base, bound to that commit.
        "--merge-base \"" + dollar + "(git rev-parse \"" + dollar + "BASE\")\"",
        "published=(--published \"" + dollar + "RUNNER_TEMP/published-rows/proof-cost-rows.json\" --sha256 \"" +
            dollar + "PUBLISHED_SHA256\")",
        "--commit \"" + dollar + "GITHUB_SHA\"",
        // Later runs find main's rows by this job and artifact name and by the digest the job logs.
        "    name: Proof cost\n", "needs: [select, suites]",
        "name: proof-cost-rows-" + dollar + "{{ github.run_id }}-" + dollar + "{{ github.run_attempt }}",
        "--proof-cost-rows \"" + dollar + "(git rev-parse \"" + dollar + "BASE\")\"",
        "archive-sha256: " + dollar + "{{ steps.pack-library.outputs.archive-sha256 || " +
            "steps.donor.outputs.archive-sha256 }}",
        "ARCHIVE_SHA256: " + dollar + "{{ needs.prepare.outputs.archive-sha256 }}",
        "ARCHIVE_SHA256: " + dollar + "{{ steps.donor.outputs.archive-sha256 }}",
        "DONATED_SHA256: " + dollar + "{{ steps.restored.outcome == 'success' && " +
            "steps.donor.outputs.manifest-sha256 || '' }}",
        "path: artifacts/library-download", "path: artifacts/certified-library.tar.zst",
        "dotnet run --file scripts/TestLibraryArchive.cs",
        "max-parallel: " + VerificationSelection.Runners, "artifacts/verification-traces/",
        "artifacts/verification-suites.json",
        "timeout-minutes: " + dollar + "{{ matrix.timeout }}",
        "VERIFICATION_SUITES: " + dollar + "{{ toJSON(matrix.suites) }}",
        "dotnet artifacts/verification-fixtures/LibraryArchive/LibraryArchive.dll restore" })
        Require(workflow.Contains(text, StringComparison.Ordinal), "Missing workflow binding: " + text);
    // A run measures only its own tree: checking out and verifying a merge base cost a shared runner
    // most of an hour.
    Require(!workflow.Contains("git worktree", StringComparison.Ordinal), "A job checks out a second tree");
    string name = "name: certified-library-" + dollar + "{{ github.run_id }}-" + dollar + "{{ github.run_attempt }}";
    Require(workflow.Split(name, StringSplitOptions.None).Length == 2,
        "Producer artifact name must appear exactly once");
    var suites = workflow[workflow.IndexOf("  suites:", StringComparison.Ordinal)..];
    Require(!suites.Contains("uses: leanprover/lean-action@", StringComparison.Ordinal),
        "Suite jobs must restore the producer toolchain without another installation");
    var installer = workflow[workflow.IndexOf("      - name: Install pinned elan", StringComparison.Ordinal)..
        workflow.IndexOf("      - name: Install Lean toolchain", StringComparison.Ordinal)];
    Require(installer.Contains("/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz",
            StringComparison.Ordinal) &&
        installer.Contains("42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63",
            StringComparison.Ordinal), "Elan must bind an exact release archive and digest");
    var authenticated = installer.IndexOf("sha256sum --check --status", StringComparison.Ordinal);
    Require(authenticated >= 0 && authenticated < installer.IndexOf("tar -xzf", StringComparison.Ordinal),
        "Authenticate the elan archive before extracting or executing it");
    Require(!workflow.Contains("uses: leanprover/lean-action@", StringComparison.Ordinal) &&
        !installer.Contains("/latest/", StringComparison.Ordinal) &&
        !installer.Contains("/master/", StringComparison.Ordinal),
        "Toolchain preparation must not run a moving elan installer or release");
    Require(workflow.ReplaceLineEndings("\n").Split("timeout-minutes: 3\n", StringSplitOptions.None).Length == 3,
        "Both toolchain installation attempts must have bounded timeouts");
});
Test("CI and suite scripts reach no repository, package source or path outside this one", () =>
{
    var found = ExternalSources.Scan(root, ExternalSources.CiFiles(root));
    Require(found.Count == 0, "Reaches outside this repository:\n" + string.Join("\n", found));
    Require(!File.Exists(Path.Combine(root, ".gitmodules")), "A submodule pulls in another repository");
    Require(!Directory.GetFiles(root).Any(path =>
            Path.GetFileName(path).Equals("nuget.config", StringComparison.OrdinalIgnoreCase)),
        "A NuGet configuration can name a package source outside this repository");
});
Test("each way to reach another repository is found in a scratch copy of a workflow or script", () =>
{
    string scratch = Path.Combine(Path.GetTempPath(), "leancil-external-" + Guid.NewGuid().ToString("N"));
    string workflowDirectory = Path.Combine(scratch, ".github", "workflows");
    Directory.CreateDirectory(workflowDirectory);
    Directory.CreateDirectory(Path.Combine(scratch, "scripts"));
    try
    {
        string original = File.ReadAllText(Path.Combine(root, ".github/workflows/verification.yml"));
        string copy = Path.Combine(workflowDirectory, "verification.yml");
        File.WriteAllText(copy, original);
        Require(ExternalSources.Scan(scratch, [copy]).Count == 0, "An unchanged copy must pass");
        // Strings are split so that this file does not match its own rules.
        string checkoutStep = Regex.Match(original, @"(?m)^( *)- uses: actions/checkout@.*$").Value;
        Require(checkoutStep.Length > 0, "The workflow has no checkout step to mutate");
        string indent = checkoutStep[..checkoutStep.IndexOf('-')];
        int stepStart = original.IndexOf(checkoutStep, StringComparison.Ordinal);
        File.WriteAllText(copy, original[..stepStart] + checkoutStep + "\n" + indent + "  with:\n" +
            indent + "    repo" + "sitory: other/owner" + original[(stepStart + checkoutStep.Length)..]);
        int stepLine = original[..stepStart].Count(character => character == '\n') + 3;
        Equal(ExternalSources.Scan(scratch, [copy]),
            [$".github/workflows/verification.yml:{stepLine}: checkout-repository"]);
        var cases = new (string Rule, string File, string Text)[]
        {
            ("fetch-repository", ".github/workflows/mutant.yml",
                "      - run: git cl" + "one https://example.test/a/b.git"),
            ("fetch-repository", ".github/workflows/mutant.yml",
                "      - run: git sub" + "module add https://example.test/a/b"),
            ("fetch-repository", ".github/workflows/mutant.yml", "      - run: gh repo cl" + "one other/owner"),
            ("fetch-repository", "scripts/Mutant.cs", "Run([\"git\", \"cl" + "one\", \"other\"]);"),
            ("package-source", ".github/workflows/mutant.yml",
                "      - run: dotnet restore --sou" + "rce https://feed.test"),
            ("package-source", ".github/workflows/mutant.yml",
                "      - run: dotnet nuget add sou" + "rce https://feed.test"),
            ("nuget-host", "scripts/Mutant.cs", "var feed = \"https://api.nu" + "get.org/v3/index.json\";"),
            ("other-url", ".github/workflows/mutant.yml",
                "      - run: curl https://git" + "hub.com/other/owner/archive/main.tar.gz"),
            ("other-url", "scripts/Mutant.cs", "var api = \"https://api.git" + "hub.com/repos/other/owner\";"),
            ("escape", ".github/workflows/mutant.yml", "          working-directory: ../other"),
            ("escape", ".github/workflows/mutant.yml", "          path: /tmp/other"),
            ("escape", ".github/workflows/mutant.yml", "      - run: cd .. && ls"),
            ("directive", "scripts/Mutant.cs", "#:include ../../other/Shared.cs"),
            ("directive", "scripts/Mutant.cs", "#:project ../../other/Other.csproj"),
            ("directive", "scripts/Mutant.cs", "#:package Other.Package@1.0.0"),
        };
        foreach (var (rule, relative, text) in cases)
        {
            string path = Path.Combine(scratch, relative);
            File.WriteAllText(path, text + "\n");
            Require(ExternalSources.Scan(scratch, [path])
                    .Any(finding => finding.EndsWith(": " + rule, StringComparison.Ordinal)),
                "Not found as " + rule + ": " + text);
        }
    }
    finally { Directory.Delete(scratch, recursive: true); }
});
Console.WriteLine($"All {checks} selection checks passed.");

/// <summary>Finds where workflows and suite scripts reach code or packages outside this repository.</summary>
static partial class ExternalSources
{
    /// <summary>Packages a script may reference; every other package is a source outside this repository.</summary>
    static readonly string[] AllowedPackages = ["Mono.Cecil"];

    /// <summary>Accepted findings by file and rule, with why each cannot reach another repository.</summary>
    static readonly Dictionary<(string File, string Rule), string> Exempt = new()
    {
        [("scripts/ConsumerVerification.cs", "fetch-repository")] =
            "clones the dependency directories of the repository under verification into a scratch workspace",
        [("scripts/CertifiedLibraryDonor.cs", "other-url")] =
            "compares a pull request side with this repository by the API URL that run metadata gives",
        [("scripts/TestFindCertifiedLibrary.cs", "other-url")] =
            "uses other and forked repositories as fixtures that donor selection must reject",
        [("Tests/CompilerCoverage.cs", "nuget-host")] =
            "the advisory latest run reads the compiler package index and builds no repository",
        [("Tests/ContractDiscovery.cs", "package-source")] =
            "restores from a feed directory the test creates in its own scratch folder",
    };

    [GeneratedRegex(@"^\s*(-\s+)?repository\s*:")]
    private static partial Regex CheckoutRepository();

    [GeneratedRegex(@"\bgit\s+(clone|submodule|remote\s+add)\b|\bgh\s+repo\s+clone\b|""(clone|submodule)""")]
    private static partial Regex FetchRepository();

    [GeneratedRegex(@"--sourc[e]\b|\bnuget\s+add\s+sourc[e]\b|<add\s+key=", RegexOptions.IgnoreCase)]
    private static partial Regex PackageSource();

    [GeneratedRegex(@"nuget\.org", RegexOptions.IgnoreCase)]
    private static partial Regex NugetHost();

    [GeneratedRegex(@"github\.com/(?!NethermindEth/LeanCIL[/""]|leanprover/elan/releases/download/v4\.2\.4/)")]
    private static partial Regex OtherRepositoryUrl();

    [GeneratedRegex(@"(path|working-directory)\s*:\s*['""]?(\.\.|/|~|[A-Za-z]:)|\bcd\s+\.\.")]
    private static partial Regex WorkflowEscape();

    [GeneratedRegex(@"^#:(include|project)\s+(\S+)")]
    private static partial Regex PathDirective();

    [GeneratedRegex(@"^#:package\s+([^@\s]+)")]
    private static partial Regex PackageDirective();

    /// <summary>Every workflow and every script or test source that a suite runs.</summary>
    internal static IEnumerable<string> CiFiles(string root) =>
        new[] { ".github/workflows/*.yml", ".github/workflows/*.yaml", "scripts/*.cs", "Tests/*.cs" }
            .SelectMany(pattern => Directory.GetFiles(Path.Combine(root, Path.GetDirectoryName(pattern)!),
                Path.GetFileName(pattern)));

    /// <summary>One finding per rule broken on a line, as file:line: rule. Cost is linear in total lines.</summary>
    internal static List<string> Scan(string root, IEnumerable<string> files)
    {
        var found = new List<string>();
        foreach (string file in files)
        {
            string relative = Path.GetRelativePath(root, file).Replace('\\', '/');
            bool workflow = relative.StartsWith(".github/workflows/", StringComparison.Ordinal);
            string[] lines = File.ReadAllLines(file);
            for (int index = 0; index < lines.Length; index++)
                foreach (string rule in Broken(root, file, workflow, lines[index]))
                    if (!Exempt.ContainsKey((relative, rule))) found.Add($"{relative}:{index + 1}: {rule}");
        }
        return found;
    }

    private static IEnumerable<string> Broken(string root, string file, bool workflow, string line)
    {
        if (workflow && CheckoutRepository().IsMatch(line)) yield return "checkout-repository";
        if (workflow && WorkflowEscape().IsMatch(line)) yield return "escape";
        if (FetchRepository().IsMatch(line)) yield return "fetch-repository";
        if (PackageSource().IsMatch(line)) yield return "package-source";
        if (NugetHost().IsMatch(line)) yield return "nuget-host";
        if (OtherRepositoryUrl().IsMatch(line)) yield return "other-url";
        var path = PathDirective().Match(line);
        string? target = path.Success
            ? Path.GetFullPath(Path.Combine(Path.GetDirectoryName(file)!, path.Groups[2].Value)) : null;
        if (target is not null && !Within(root, target)) yield return "directive";
        var package = PackageDirective().Match(line);
        if (package.Success && !AllowedPackages.Contains(package.Groups[1].Value)) yield return "directive";
    }

    private static bool Within(string root, string path) =>
        path.StartsWith(Path.GetFullPath(root).TrimEnd(Path.DirectorySeparatorChar) + Path.DirectorySeparatorChar,
            StringComparison.Ordinal);
}
