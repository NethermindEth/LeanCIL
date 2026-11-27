internal sealed record ExportSuite(string Name, string Cohort, string Script, string[] Arguments,
    string Description, string[] Cases, string[] Inputs, bool Standalone = false, string? ChildScript = null);

internal static class ExportVerificationSuites
{
    internal static readonly ExportSuite[] Entries =
    [
        new("exports", "core", "Tests/ContractExport.cs", ["--cohort", "core"],
            "contract production, post-callback audit, discovery, restrictions and caller reuse",
            ["core.unrelated", "core.definition", "core.wrapper-true", "core.publication", "core.caller",
             "audit.proof-source", "audit.wrapper-artifact", "discovery.fixture",
             "core.internal", "core.instance", "core.generic", "core.virtual", "core.static-values",
             "core.initialized", "core.imports", "core.profile", "core.reference",
             "core.bundle-location", "core.framework-change", "core.interface-text", "core.duplicate",
             "core.partial-publication", "core.body-rebuild", "core.published-closure", "core.incorrect-post",
             "core.revised-contract"],
            ["Tests/ContractExport.cs", "Tests/ContractDiscovery.cs"], ChildScript: "Tests/ContractDiscovery.cs"),
        Entry("exportsprotected", "protected", "protected static export and separately compiled derived caller",
            ["protected.publication", "protected.caller", "protected.visibility"]),
        new("exportsresolution", "resolution", "Tests/FullModuleResolution.cs", [], "full module resolution",
            ["resolution.same-files", "resolution.changed-file", "resolution.rewritten-artifact"],
            ["Tests/FullModuleResolution.cs"]),
        Entry("exportsfull", "full",
            "independent full caller verification, pair bundle sharing, rejection checks, producer theorem checks and composition integrity",
            ["full.consumer-explicit", "full.consumer-repeat", "full.artifact-mode",
             "full.ordinary", "full.pair",
             "full.missing-bundle", "full.inventory-bytes", "full.producer-bytes",
             "full.unrecorded-olean", "full.deployed-dll", "full.stale-closure", "full.statement-digest",
             "full.extra-premise", "full.producer-true", "full.producer-definition", "full.composition-true"]),
        Entry("exportsmutations", "mutations",
            "ordinary and consumer caller artifact, source and shadow mutations during full verification",
            ["full.ordinary-artifact", "full.consumer-artifact", "full.consumer-source", "full.consumer-shadow"]),
        new("exportsstatics", "statics", "Tests/ModularStaticExports.cs", [], "independent modular static exports",
            [], ["Tests/ModularStaticExports.cs"], Standalone: true),
        new("exportsfullstatics", "fullstatics", "Tests/ModularStaticExports.cs", ["--full-composition"],
            "independent full composition of shared and changed static tables", [], ["Tests/ModularStaticExports.cs"],
            Standalone: true),
        new("exportstransitive", "transitive", "Tests/TransitiveImports.cs", [], "independent transitive contract imports",
            [], ["Tests/TransitiveImports.cs"],
            Standalone: true),
        new("exportstransitiveoutcomes", "transitiveoutcomes", "Tests/TransitiveOutcomes.cs", [],
            "independent deep transitive named outcome contracts",
            [], ["Tests/TransitiveOutcomes.cs", "Tests/ContractImports/DerivedInterface.lean",
                "Tests/ContractImports/DerivedPercentProof.lean"],
            Standalone: true),
        new("exportstyped", "typed", "Tests/GenericLayoutImports.cs", [], "independent typed generic and layout imports", [],
            ["Tests/GenericLayoutImports.cs", "Tests/GenericImportIdentities.cs",
             "Tests/ContractImports/TypedImportInterface.lean",
             "Tests/ContractImports/TypedIdentityProof.lean", "Tests/ContractImports/TypedCopyProof.lean",
             "Tests/ContractImports/TypedIdentityCaller.lean", "Tests/ContractImports/TypedCopyCaller.lean",
             "Tests/ContractImports/TypedChainCaller.lean"],
            Standalone: true),
        new("exportsderived", "derived", "Tests/DerivedContractExports.cs", [],
            "derived public contracts through DLL export and import", [],
            ["Tests/DerivedContractExports.cs", "Tests/ContractImports/DerivedInterface.lean",
             "Tests/ContractImports/DerivedPercentProof.lean", "Tests/ContractImports/DerivedAddProof.lean",
             "Tests/ContractImports/DerivedShiftCaller.lean", "Tests/ContractImports/DerivedSumCaller.lean"],
            Standalone: true),
        new("exportsinitialized", "initialized", "Tests/InitializedExports.cs", [],
            "scoped initialization assumptions in exported and imported contracts", [],
            ["Tests/InitializedExports.cs", "Tests/TransitiveImports/Conditional.lean"], Standalone: true),
        new("exportsprofiles", "profiles", "Tests/ProfileFamilies.cs", [],
            "one contract family across independently checked profile extractions", [],
            ["Tests/ProfileFamilies.cs", "Tests/ContractImports/ProfileFamilyContract.lean",
             "Tests/ContractImports/ProfileFamilyProof.lean", "Tests/ContractImports/ProfileFamilyCaller.lean"],
            Standalone: true)
    ];

    static ExportSuite Entry(string name, string cohort, string description, string[] cases) =>
        new(name, cohort, "Tests/ContractExport.cs", ["--cohort", cohort], description, cases,
            cohort is "core" or "protected" ? ["Tests/ContractExport.cs"] :
                ["Tests/ContractExport.cs", "Tests/FullImportVerification.cs"]);

    internal static ExportSuite[] Plan()
    {
        Validate(Entries);
        return Entries.ToArray();
    }

    internal static ExportSuite[] FullPlan() => Plan().Where(entry => IsFull(entry.Cohort)).ToArray();
    internal static bool IsFull(string cohort) => cohort is "full" or "mutations";

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
