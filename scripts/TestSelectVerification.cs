#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationSelection.cs
#:include ExportVerificationSuites.cs

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
    Equal(VerificationSelection.Schedule(selected), ["unsafe", "math", "loops"]);
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
Test("docs only", () => Equal(VerificationSelection.Select(["README.md", "docs/design.md"]), []));
Test("main and manual always full", () =>
{
    foreach (var eventName in new[] { "push", "workflow_dispatch" })
        Equal(VerificationSelection.Select(["README.md"], eventName), All());
});
Test("test entry points", () =>
{
    Equal(VerificationSelection.Select(["Tests/Loops.cs"]), ["loops"]);
    Equal(VerificationSelection.Select(["Tests/SkipInitialization.cs"]), ["unsafe"]);
    Equal(VerificationSelection.Select(["Tests/NullReferences.cs"]), ["unsafe"]);
    foreach (var name in new[] { "BatchVerification", "VerificationCache", "VerificationReuse" })
        Equal(VerificationSelection.Select([$"Tests/{name}.cs"]), ["core"]);
});
Test("proof and transitive imports", () =>
{
    Equal(VerificationSelection.Select(["Examples/Proofs/Countdown.lean"]), ["contracts", "fsharp", "loops"]);
    Equal(VerificationSelection.Select(["Examples/Support.lean"]), All());
    Equal(VerificationSelection.Select(["Tests/UnsafeCallEvidence.lean"]), ["unsafe"]);
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
    Equal(VerificationSelection.Select([".github/workflows/consumer.yml", ".github/workflows/runtime-profiles.yml"]),
        []);
    Equal(VerificationSelection.Select([".github/workflows/consumer.yml", "Tests/Loops.cs"]), ["loops"]);
});
Test("multiple changes and deleted paths", () =>
{
    Equal(VerificationSelection.Select(["README.md", "Tests/Loops.cs", "Tests/Division.cs"]), ["division", "loops"]);
    Equal(VerificationSelection.Select(["Tests/Deleted.cs"]), All());
});
Test("every registered suite has its entry point", () =>
{
    string runner = File.ReadAllText(Path.Combine(root, "scripts/Test.cs"));
    string accepted = Regex.Match(runner, """\["--suite", (.*?)\] =>""").Groups[1].Value;
    IEnumerable<string> names = Regex.Matches(accepted, @"""([a-z]+)""").Select(match => match.Groups[1].Value)
        .Where(name => name != "all").Concat(ExportVerificationSuites.Plan().Select(entry => entry.Name))
        .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal);
    Equal(names, All());
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
Test("independent export cohort map preserves 18 leaves, 46 base cases and one discovery completion", () =>
{
    Dictionary<string, (string Cohort, string[] Cases)> expected = new(StringComparer.Ordinal)
    {
        ["exports"] = ("core", ["core.unrelated", "core.definition", "core.wrapper-true", "core.publication",
            "core.caller", "core.internal", "core.instance", "core.generic", "core.virtual", "core.static-values",
            "core.initialized", "core.imports", "core.profile", "core.reference",
            "core.bundle-location", "core.framework-change", "core.interface-text", "core.duplicate",
            "core.partial-publication", "core.body-rebuild", "core.published-closure", "core.incorrect-post"]),
        ["exportsaudit"] = ("audit", ["audit.proof-source", "audit.wrapper-artifact"]),
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
        ["exportsdiscovery"] = ("discovery", ["discovery.fixture"]),
        ["exportstyped"] = ("typed", [])
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
            bool standalone = entry.Cohort is "statics" or "fullstatics" or "transitive" or "typed";
            Require(entry.Standalone == standalone, "Wrong standalone fixture kind: " + entry.Name);
            Require(entry.ChildScript == (entry.Cohort == "discovery" ? "Tests/ContractDiscovery.cs" : null),
                "Wrong bootstrapped child fixture: " + entry.Name);
            string script = entry.Cohort switch
            {
                "resolution" => "Tests/FullModuleResolution.cs",
                "statics" or "fullstatics" => "Tests/ModularStaticExports.cs",
                "transitive" => "Tests/TransitiveImports.cs",
                "typed" => "Tests/GenericLayoutImports.cs",
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
    Require(baseCases.Length == 46 && baseCases.Distinct(StringComparer.Ordinal).Count() == 46,
        "Lost or duplicate base behavior");
    Require(all.SelectMany(entry => entry.Cases).Count() == 47 &&
        all.SelectMany(entry => entry.Cases).Distinct(StringComparer.Ordinal).Count() == 47,
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
        ["--cohort", "typed"] })
        MustReject(() => ExportVerificationSuites.Select(invalid));
    string[] nonFullCohorts =
        ["core", "audit", "resolution", "statics", "fullstatics", "transitive", "discovery", "typed", "unknown"];
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
    Equal(VerificationSelection.Select(["Tests/ModularStaticExports.cs"]).Order(StringComparer.Ordinal),
        ["exportsfullstatics", "exportsstatics"]);
    Equal(VerificationSelection.Select(["Tests/TransitiveImports.cs"]), ["exportstransitive"]);
    Equal(VerificationSelection.Select(["Tests/ContractDiscovery.cs"]), ["exportsdiscovery"]);
    Equal(VerificationSelection.Select(["Tests/GenericLayoutImports.cs"]), ["exportstyped"]);
    string[] typedFixtures =
        ["TypedImportInterface", "TypedIdentityProof", "TypedCopyProof", "TypedIdentityCaller", "TypedCopyCaller"];
    foreach (string name in typedFixtures)
        Equal(VerificationSelection.Select(["Tests/ContractImports/" + name + ".lean"]), ["exportstyped"]);
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
    Directory.CreateDirectory(Path.Combine(isolated, "scripts"));
    Directory.CreateDirectory(Path.Combine(isolated, "Tests"));
    try
    {
        File.Copy(Path.Combine(root, "scripts/Test.cs"), Path.Combine(isolated, "scripts/Test.cs"));
        File.WriteAllText(Path.Combine(isolated, "Tests/ContractExport.cs"), "");
        // Each fixture in registration order must be reported missing before the next one is checked.
        (string Fixture, string Kind)[] fixtures =
        [
            ("Tests/FullModuleResolution.cs", "resolution"),
            ("Tests/ModularStaticExports.cs", "standalone static"),
            ("Tests/TransitiveImports.cs", "standalone transitive"),
            ("Tests/ContractDiscovery.cs", "discovery child"),
            ("Tests/GenericLayoutImports.cs", "standalone typed")
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
        command.Environment["SUITES_RESULT"] = result;
        using var process = Process.Start(command) ?? throw new InvalidOperationException("Could not start Bash");
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        var expected = planned == "success" && ((selected, prepared, result) is
            ("true", "success", "success") or ("false", "skipped", "skipped"));
        string transcript = stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult();
        Require((process.ExitCode == 0) == expected,
            $"Unexpected gate result: {planned}/{selected}/{prepared}/{result}\n{transcript}");
    }
});
Test("same-run certified library binding and observability", () =>
{
    string workflow = File.ReadAllText(Path.Combine(root, ".github/workflows/verification.yml"));
    const string dollar = "$";
    foreach (string text in new[] {
        "needs: [select, prepare]", "needs: [select, prepare, suites]",
        "LEANCIL_CERTIFIED_LIBRARY_SHA256: " + dollar + "{{ needs.prepare.outputs.manifest-sha256 }}",
        "artifact-ids: " + dollar + "{{ needs.prepare.outputs.artifact-id }}",
        "artifact-id: " + dollar + "{{ steps.library-artifact.outputs.artifact-id }}",
        "name: verification-results-" + dollar + "{{ matrix.suite }}-" + dollar + "{{ github.run_attempt }}",
        "include-hidden-files: true", "max-parallel: 8", "artifacts/verification-traces/",
        "matrix.suite == 'imports' && 90", "startsWith(matrix.suite, 'exports') && 120 || 30" })
        Require(workflow.Contains(text, StringComparison.Ordinal), "Missing workflow binding: " + text);
    string name = "name: certified-library-" + dollar + "{{ github.run_id }}-" + dollar + "{{ github.run_attempt }}";
    Require(workflow.Split(name, StringSplitOptions.None).Length == 2,
        "Producer artifact name must appear exactly once");
});
Console.WriteLine($"All {checks} selection checks passed.");
