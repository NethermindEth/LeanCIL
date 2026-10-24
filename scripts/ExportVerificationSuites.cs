internal sealed record ExportSuite(string Name, string Cohort, string Script, string[] Arguments,
    string Description, string[] Cases, string[] Inputs, bool Standalone = false, string? ChildScript = null);

internal static class ExportVerificationSuites
{
    internal static readonly ExportSuite[] Entries =
    [
        Entry("exports", "core", "contract production, restrictions and caller reuse",
            ["core.unrelated", "core.definition", "core.wrapper-true", "core.publication", "core.caller",
             "core.internal", "core.instance", "core.generic", "core.virtual", "core.static-values",
             "core.initialized", "core.imports", "core.profile", "core.reference",
             "core.bundle-location", "core.framework-change", "core.interface-text", "core.duplicate",
             "core.partial-publication", "core.body-rebuild", "core.published-closure", "core.incorrect-post"]),
        Entry("exportsaudit", "audit", "post-callback export integrity",
            ["audit.proof-source", "audit.wrapper-artifact"]),
        new("exportsresolution", "resolution", "Tests/FullModuleResolution.cs", [], "full module resolution",
            ["resolution.same-files", "resolution.changed-file"], ["Tests/FullModuleResolution.cs"]),
        Entry("exportsfullcomposition", "composition", "transferred composition statement integrity", ["full.composition-true"]),
        Entry("exportsfullconsumer", "consumer", "fresh and repeated full consumer verification",
            ["full.consumer-explicit", "full.consumer-repeat", "full.artifact-mode"]),
        Entry("exportsfullordinary", "ordinary", "ordinary full caller verification", ["full.ordinary"]),
        Entry("exportsfullpair", "pair", "two imported slots from one bundle", ["full.pair"]),
        Entry("exportsfullchecks", "checks", "full input and caller rejection",
            ["full.missing-bundle", "full.inventory-bytes", "full.producer-bytes",
             "full.unrecorded-olean", "full.deployed-dll", "full.stale-closure", "full.statement-digest", "full.extra-premise"]),
        Entry("exportsfulltheorems", "theorems", "producer theorem kind and statement rejection",
            ["full.producer-true", "full.producer-definition"]),
        Entry("exportsmutationordinary", "ordinary-artifact", "ordinary caller artifact mutation", ["full.ordinary-artifact"]),
        Entry("exportsmutationconsumer", "consumer-artifact", "consumer caller artifact mutation", ["full.consumer-artifact"]),
        Entry("exportsmutationsource", "consumer-source", "consumer caller source mutation", ["full.consumer-source"]),
        Entry("exportsmutationshadow", "consumer-shadow", "original caller root shadow mutation", ["full.consumer-shadow"]),
        new("exportsstatics", "statics", "Tests/ModularStaticExports.cs", [], "independent modular static exports",
            [], ["Tests/ModularStaticExports.cs"], Standalone: true),
        new("exportstransitive", "transitive", "Tests/TransitiveImports.cs", [], "independent transitive contract imports",
            [], ["Tests/TransitiveImports.cs"], Standalone: true),
        new("exportsdiscovery", "discovery", "Tests/ContractExport.cs", ["--cohort", "discovery"], "contract discovery with real export bootstrap",
            ["discovery.fixture"], ["Tests/ContractExport.cs", "Tests/ContractDiscovery.cs"], ChildScript: "Tests/ContractDiscovery.cs")
    ];

    static ExportSuite Entry(string name, string cohort, string description, string[] cases) =>
        new(name, cohort, "Tests/ContractExport.cs", ["--cohort", cohort], description, cases,
            cohort is "core" or "audit" ? ["Tests/ContractExport.cs"] : ["Tests/ContractExport.cs", "Tests/FullImportVerification.cs"]);

    internal static ExportSuite[] Plan()
    {
        Validate(Entries);
        return Entries.ToArray();
    }

    internal static ExportSuite[] FullPlan() => Plan().Where(entry => IsFull(entry.Cohort)).ToArray();
    internal static bool IsFull(string cohort) => cohort is "composition" or "consumer" or "ordinary" or "pair" or
        "checks" or "theorems" or "ordinary-artifact" or "consumer-artifact" or "consumer-source" or "consumer-shadow";

    internal static string[] DiscoveryArguments(string sidecar, string callerProof, string callerPackage,
        string producerPackage, string producerProof, string contractSource) =>
        [sidecar, callerProof, callerPackage, producerPackage, producerProof, contractSource];

    internal static string? Select(string[] args, bool full = false)
    {
        if (args.Length == 0) return null;
        if (args is not ["--cohort", string cohort] ||
            !Plan().Any(entry => entry.Cohort == cohort && !entry.Standalone && (full ? IsFull(cohort) : cohort != "resolution")))
            throw new ArgumentException("Expected --cohort with one registered " + (full ? "full " : "") + "export cohort.");
        return cohort;
    }

    internal static void Validate(IEnumerable<ExportSuite> entries)
    {
        HashSet<string> names = new(StringComparer.Ordinal);
        HashSet<string> cohorts = new(StringComparer.Ordinal);
        HashSet<string> cases = new(StringComparer.Ordinal);
        foreach (ExportSuite entry in entries)
        {
            if (!names.Add(entry.Name) || !cohorts.Add(entry.Cohort) ||
                (entry.Standalone ? entry.Cases.Length != 0 || IsFull(entry.Cohort) : entry.Cases.Length == 0) ||
                (entry.ChildScript is not null && (entry.Standalone || IsFull(entry.Cohort) ||
                    string.IsNullOrWhiteSpace(entry.ChildScript) || !entry.Inputs.Contains(entry.ChildScript, StringComparer.Ordinal))) ||
                entry.Cases.Any(id => string.IsNullOrWhiteSpace(id) || !cases.Add(id)))
                throw new InvalidDataException("Invalid or duplicate export suite/case: " + entry.Name);
        }
        if (names.Count == 0) throw new InvalidDataException("No export suites registered.");
    }
}

internal sealed class ExportCaseLedger
{
    readonly HashSet<string> expected;
    readonly HashSet<string> completed = new(StringComparer.Ordinal);

    internal ExportCaseLedger(string cohort)
    {
        ExportSuite entry = ExportVerificationSuites.Plan().Single(item => item.Cohort == cohort);
        if (entry.Standalone) throw new InvalidOperationException("Standalone fixture has its own assertions: " + cohort);
        expected = new(entry.Cases, StringComparer.Ordinal);
    }

    internal void CompleteCase(string id)
    {
        if (!expected.Contains(id) || !completed.Add(id))
            throw new InvalidOperationException("Unexpected or repeated export case: " + id);
    }

    internal void Finish()
    {
        if (!expected.SetEquals(completed))
            throw new InvalidOperationException("Export cases did not finish: " + string.Join(", ", expected.Except(completed).Order(StringComparer.Ordinal)));
    }
}
