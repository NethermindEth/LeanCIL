using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;
using LeanCIL;
using Mono.Cecil;
using Nethermind.LeanCIL;

partial class Program
{
    sealed record GateProject(string path, string assembly, Dictionary<string, string>? properties = null);
    sealed record GateBuild(string project, Dictionary<string, string>? properties = null);
    sealed record GateTemplate(string path, Dictionary<string, string>? values = null);
    sealed record GateTemplateUse(string template, Dictionary<string, string>? values = null);
    sealed record GateRefutation(string theorem, string? proof = null, string? template = null,
        Dictionary<string, string>? values = null);
    sealed record GateVariant(string name, string expect, string? assembly = null, GateBuild? build = null,
        string[]? profiles = null, JsonElement? proof = null, string? theorem = null,
        string[]? initializedTypes = null, string? program = null, string? programOf = null,
        GateRefutation? refutation = null, string? statement = null);
    sealed record ProofGateEntry(string name, string method, string[] profiles, string proof, string theorem,
        string? assembly = null, GateBuild? build = null, GateVariant[]? variants = null,
        string[]? initializedTypes = null, string[]? typeArguments = null);
    sealed record GateManifest(int schema, string proofRoot, string outputRoot, ProofGateEntry[] gates,
        Dictionary<string, GateProject>? projects = null, string? generatedRoot = null,
        Dictionary<string, GateTemplate>? templates = null, Dictionary<string, string>? profiles = null);

    static readonly JsonSerializerOptions GateManifestJson =
        new() { UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow };

    /// <summary>One project build: the project, its merged properties and its private output tree.</summary>
    sealed record GateBuildPlan(string Project, string AssemblyName, SortedDictionary<string, string> Properties,
        string Directory);

    /// <summary>
    /// A proof the tool writes to `Path` from `Template` and its `Values` before anything reads the consumer
    /// sources; a template that cannot be instantiated fails its row at `Stage`.
    /// </summary>
    sealed record GateGenerated(string Template, Dictionary<string, string> Values, string Path, string Stage);

    /// <summary>The outcome of the refutation a `rejected` variant gives, checked against its extraction.</summary>
    sealed record GateRefutationResult(string proof, string theorem, string status, string stage, string? error,
        string[]? axioms);

    /// <summary>
    /// One variant under one profile. `status` is the variant's verdict; the fields from `proof` to
    /// `elapsedSeconds` describe its proof, or the stage that failed before its proof was checked.
    /// </summary>
    sealed record GateResult(string output, string proof, string theorem, string expect, string status, string stage,
        string? error, string[]? axioms, string? libraryBuild, FailureReports.Report? failure,
        double elapsedSeconds, string gate, string profile, string variant, string? build, string? extraction,
        string? program, GateRefutationResult? refutation, GateStatement? statement);

    /// <summary>
    /// How a variant's verified statement relates to production's `T`, both as the theorem audits print them:
    /// `same` when the kernel accepts the variant's theorem at `T`, or its refutation at `¬ T`; `different` when it
    /// does not; `unavailable` when there was nothing to compare; `independent` when the manifest says so.
    /// </summary>
    sealed record GateStatement(string status, string? production, string? variant);

    const string StatementIdentityStage = "statement identity";

    /// <summary>One variant of a gate under one profile, and the first stage at which it failed.</summary>
    sealed class GateRow
    {
        internal required string Gate, Profile, Variant, Expect, Output, Proof, Theorem;
        internal required string? Assembly, ExpectedProgram, ProgramOf, RefutationProof, RefutationTheorem, Statement;
        internal required GateBuildPlan? Build;
        internal required GateGenerated[] Generated;
        internal required string[]? InitializedTypes, TypeArguments;
        internal required string Method, ExtractionProfile;
        internal GateRow? ProgramBase;
        internal GeneratedExtraction? Extraction;
        internal string? BuildStatus, ExtractionStatus, ProgramStatus, Stage, Error;
        internal bool Failed => Error is not null;
        internal string Name => $"{Gate}/{Profile}/{Variant}";

        /// <summary>Whether the statement this row verifies must be production's, or its negation.</summary>
        internal bool ComparesStatement => Variant != "production" && Expect != "unchanged" && Statement is null;

        internal void Fail(string stage, string error)
        {
            if (Error is not null) return;
            (Stage, Error) = (stage, error);
        }
    }

    const string GatesUsage = "Usage: leancil gates manifest.json [--method name] [--profile name] " +
        "[--changed path]... [--check] [--fresh] [--rebuild-library] [--trace] [--parallel count] " +
        "[--results results.json] [--format text|json]";

    // Build settings the tool owns, so a manifest cannot point two builds at one output.
    static readonly HashSet<string> ReservedBuildProperties = new(StringComparer.OrdinalIgnoreCase)
    {
        "BaseOutputPath", "BaseIntermediateOutputPath", "MSBuildProjectExtensionsPath", "OutputPath",
        "IntermediateOutputPath", "OutDir"
    };

    /// <summary>
    /// Builds, extracts and verifies an explicit catalog of gates and their variants. A `rejected` variant
    /// passes only when its refutation verifies at the negation of production's statement and its proof fails
    /// at proof checking; a certifying variant's theorem must verify at production's statement.
    /// </summary>
    internal static int RunGates(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException(GatesUsage);
        var manifestPath = Path.GetFullPath(args[0]);
        var directory = Path.GetDirectoryName(manifestPath)!;
        var manifest = JsonSerializer.Deserialize<GateManifest>(File.ReadAllText(manifestPath), GateManifestJson)
            ?? throw new InvalidDataException("Missing gate manifest.");
        if (manifest.schema != 1 || string.IsNullOrWhiteSpace(manifest.proofRoot) ||
            string.IsNullOrWhiteSpace(manifest.outputRoot) || manifest.gates is not { Length: > 0 })
            throw new InvalidDataException("Expected schema 1, proofRoot, outputRoot and nonempty gates.");
        string? methodFilter = null;
        string? profileFilter = null;
        var pathComparer = OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;
        var changed = new HashSet<string>(pathComparer);
        var verification = new List<string>();
        for (var index = 1; index < args.Length; index++)
        {
            var option = args[index];
            if (option is "--check" or "--fresh" or "--rebuild-library" or "--trace")
            {
                verification.Add(option);
                continue;
            }
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException("Missing value for " + option);
            switch (option)
            {
                case "--method" when methodFilter is null: methodFilter = args[index]; break;
                case "--profile" when profileFilter is null: profileFilter = args[index]; break;
                case "--changed": changed.Add(Path.GetFullPath(args[index])); break;
                case "--parallel" or "--results" or "--format":
                    verification.AddRange([option, args[index]]);
                    break;
                default: throw new ArgumentException("Unknown or duplicate option: " + option);
            }
        }
        var options = ParseBatchOptions([.. verification]);
        var proofRoot = Path.TrimEndingDirectorySeparator(Path.GetFullPath(manifest.proofRoot, directory));
        var outputRoot = Path.GetFullPath(manifest.outputRoot, directory);
        var rows = GateRows(manifest, directory, proofRoot, outputRoot, methodFilter, profileFilter);
        if (rows.Count == 0) throw new ArgumentException("No gates match the requested selection.");

        // Generated proofs exist before any selection or request reads or hashes the consumer sources.
        foreach (var row in rows)
            foreach (var generated in row.Generated) InstantiateGenerated(row, generated, proofRoot);

        var affectedProofs = new Dictionary<string, bool>(pathComparer);
        bool ProofAffected(string proof)
        {
            if (!affectedProofs.TryGetValue(proof, out var affected))
                affectedProofs[proof] = affected = ProofSources(proofRoot, proof).Keys
                    .Any(path => changed.Contains(Path.GetFullPath(path, proofRoot)));
            return affected;
        }
        var templates = rows.SelectMany(row => row.Generated).Select(generated => generated.Template)
            .ToHashSet(pathComparer);
        bool InputAffected(GateRow row) => changed.Contains(manifestPath) ||
            row.Generated.Any(generated => changed.Contains(generated.Template)) ||
            (row.ExtractionProfile.StartsWith('@') && changed.Contains(row.ExtractionProfile[1..])) ||
            (row.Expect != "unchanged" && ProofAffected(row.Proof)) ||
            (row.RefutationProof is not null && ProofAffected(row.RefutationProof));
        var selected = rows;
        // Changes to proofs, templates and the manifest select without building or extracting anything else.
        if (changed.Count > 0 && changed.All(path =>
            Path.GetExtension(path) == ".lean" || templates.Contains(path) || pathComparer.Equals(path, manifestPath)))
            selected = [.. rows.Where(InputAffected)];
        if (selected.Count == 0) throw new ArgumentException("No gates depend on the changed paths.");
        var production = rows.Where(row => row.Variant == "production").ToDictionary(row => (row.Gate, row.Profile));
        // Program and statement comparisons need the rows they compare with, even when those are not selected.
        GateRow?[] Compared(GateRow row) =>
            [row.ProgramBase, row.ComparesStatement ? production[(row.Gate, row.Profile)] : null];
        var needed = selected.SelectMany(Compared).OfType<GateRow>().ToHashSet();
        var prepared = rows.Where(row => selected.Contains(row) || needed.Contains(row)).ToList();
        BuildGateProjects(prepared);
        ExtractGateRows(prepared);
        if (changed.Count > 0)
            selected = [.. selected.Where(row => row.Failed || InputAffected(row) ||
                (row.Build is { } build && changed.Any(path => Under(path, Path.GetDirectoryName(build.Project)!))) ||
                GateMethodAffected(row.Extraction!, changed))];
        if (selected.Count == 0) throw new ArgumentException("No gates depend on the changed paths.");
        if (options.CheckOnly && selected.Any(row => row.Expect == "rejected"))
            throw new ArgumentException("--check cannot evaluate mutation rejection expectations.");
        foreach (var row in selected.Where(row => row.ProgramBase is not null && !row.Failed))
            CompareGateProgram(row, row.ProgramBase!);

        foreach (var row in selected.Where(row => row.Failed))
        {
            // A variant that failed before verification keeps no certificate from an earlier run.
            if (Directory.Exists(row.Output)) File.Delete(Path.Combine(row.Output, "verified.json"));
            if (options.Json) continue;
            Console.WriteLine($"FAIL {row.Name} (stage: {row.Stage})");
            CliDiagnostics.Write(new CliFailure(row.Stage!, new InvalidOperationException(row.Error)), row.Stage!,
                invalid: true);
        }
        foreach (var row in selected.Where(row => row.Expect == "unchanged" && !row.Failed && !options.Json))
            Console.WriteLine($"PASS unchanged {row.Name} (program {row.ExpectedProgram})");

        // Production verifies first and reports its statement; variants compared with it verify in a second batch.
        // Compile-only runs audit no statement, so they compare none.
        var compared = options.CheckOnly ? [] : selected.Where(row => row.ComparesStatement && !row.Failed).ToList();
        var origins = compared.Select(row => production[(row.Gate, row.Profile)]).Where(row => !selected.Contains(row));
        var requests = new List<BatchRequest>();
        var requestIndex = new Dictionary<GateRow, (int? Refutation, int Proof)>();
        // A refutation precedes the proof it accompanies, so the proof's request owns the output.
        void Request(GateRow row)
        {
            int? refutation = null;
            if (row.RefutationProof is not null)
            {
                refutation = requests.Count;
                requests.Add(new(row.Output, row.RefutationProof, row.RefutationTheorem!, "verified"));
            }
            requestIndex[row] = (refutation, requests.Count);
            requests.Add(new(row.Output, row.Proof, row.Theorem, row.Expect));
        }
        foreach (var row in selected.Except(compared).Concat(origins.Distinct())
            .Where(row => !row.Failed && row.Expect != "unchanged"))
            Request(row);
        var firstCount = requests.Count;
        foreach (var row in compared) Request(row);
        Directory.CreateDirectory(outputRoot);
        File.WriteAllText(Path.Combine(outputRoot, "requests.json"),
            JsonSerializer.Serialize(new BatchManifest(1, proofRoot, [.. requests]), Json) + "\n");
        var statements = new StatementRequest?[requests.Count];
        foreach (var (row, index) in requestIndex.Where(pair => pair.Key.Variant == "production" && !options.CheckOnly))
            statements[index.Proof] = new(Term: true);
        var first = Run(0, firstCount);
        foreach (var row in compared)
        {
            var origin = requestIndex.TryGetValue(production[(row.Gate, row.Profile)], out var at)
                ? first.Verified[at.Proof]?.statementIdentity?.term : null;
            var index = requestIndex[row];
            // Without production's statement the variant still verifies, and its statement is unavailable.
            if (origin is { } term)
                statements[row.Expect == "rejected" ? index.Refutation!.Value : index.Proof] =
                    new(false, term.GetRawText(), row.Expect == "rejected");
        }
        var second = Run(firstCount, requests.Count);
        var run = new BatchRun([.. first.Results, .. second.Results],
            [.. first.Reports.Concat(second.Reports).Select(node => node?.DeepClone())],
            [.. first.Verified, .. second.Verified]);

        BatchRun Run(int start, int end) => start == end ? new([], [], [])
            : RunBatch(new BatchManifest(1, proofRoot, [.. requests.Skip(start).Take(end - start)]), outputRoot,
                options, [.. statements.Skip(start).Take(end - start)]);
        Report? Verified(int? index) => index is { } at ? run.Verified[at] : null;
        (GateStatement?, string?) Statement(GateRow row)
        {
            if (options.CheckOnly || row.Variant == "production" || !requestIndex.TryGetValue(row, out var index))
                return (null, null);
            var own = Verified(row.Expect == "rejected" ? index.Refutation : index.Proof);
            if (row.Statement == "independent")
                return (new("independent", null, own is null ? null : StatementOf(own)), null);
            var origin = production[(row.Gate, row.Profile)];
            var verified = requestIndex.TryGetValue(origin, out var at);
            return CompareGateStatement(row, origin, origin.Stage ?? (verified ? run.Results[at.Proof].stage : "build"),
                verified ? Verified(at.Proof) : null, own);
        }
        var results = selected.Select(row => GateOutcome(row, options.CheckOnly,
            requestIndex.TryGetValue(row, out var index) ? index : null, run.Results, Statement(row))).ToArray();
        var failed = results.Count(result => result.status == "failed");
        foreach (var (row, result) in selected.Zip(results).Where(pair => pair.Second.stage == StatementIdentityStage))
        {
            // A certifying variant whose statement differs from production's keeps no certificate.
            if (row.Expect == "verified") File.Delete(Path.Combine(row.Output, "verified.json"));
            if (options.Json) continue;
            Console.WriteLine($"FAIL {row.Name} (stage: {StatementIdentityStage})");
            CliDiagnostics.Write(new CliFailure(StatementIdentityStage, new InvalidOperationException(result.error)),
                StatementIdentityStage, invalid: true);
        }
        foreach (var result in results.Where(result => result.status == "failed" && result.error is null))
            if (!options.Json)
                Console.WriteLine($"FAIL {result.gate}/{result.profile}/{result.variant} (refutation " +
                    $"{result.refutation!.theorem}, stage: {result.refutation.stage})");
        if (options.ResultsPath is not null)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(options.ResultsPath)!);
            File.WriteAllText(options.ResultsPath, JsonSerializer.Serialize(results, Json) + "\n");
        }
        if (options.Json)
            Console.Write(VerifyReports.Serialize(new JsonObject
            {
                ["schema"] = VerifyReports.BatchSchema,
                ["passed"] = results.Length - failed,
                ["failed"] = failed,
                ["variants"] = JsonSerializer.SerializeToNode(results, Json),
                ["requests"] = run.Reports,
            }));
        else Console.WriteLine($"Gates: {results.Length - failed} passed, {failed} failed of {results.Length} " +
            "variant profiles." + (options.CheckOnly ? " No verification certificate." : ""));
        return failed == 0 ? 0 : 1;
    }

    /// <summary>
    /// The production row and variant rows of every gate the filters select, in manifest order, after
    /// checking the whole manifest. Paths are resolved; nothing is built, written or extracted.
    /// </summary>
    static List<GateRow> GateRows(GateManifest manifest, string directory, string proofRoot, string outputRoot,
        string? methodFilter, string? profileFilter)
    {
        var projects = new Dictionary<string, GateProject>(StringComparer.Ordinal);
        foreach (var (name, project) in manifest.projects ?? [])
        {
            if (!SafeGateName(name) || project is null || string.IsNullOrWhiteSpace(project.path) ||
                string.IsNullOrWhiteSpace(project.assembly) ||
                Path.GetFileName(project.assembly) != project.assembly ||
                project.assembly.IndexOfAny(Path.GetInvalidFileNameChars()) >= 0)
                throw new InvalidDataException("Invalid project " + name +
                    ": expected path and an assembly file name.");
            CheckBuildProperties(name, project.properties);
            projects[name] = project;
        }
        string[]? generatedRoot = manifest.generatedRoot?.Split('/');
        if (generatedRoot is not null && (generatedRoot.Any(part => part is "" or "." or ".." ||
                part.IndexOfAny(Path.GetInvalidFileNameChars()) >= 0) ||
            Path.IsPathRooted(manifest.generatedRoot) || manifest.generatedRoot!.Contains(':')))
            throw new InvalidDataException("generatedRoot must be a relative path of `/`-separated names.");
        var templates = new Dictionary<string, GateTemplate>(StringComparer.Ordinal);
        foreach (var (name, template) in manifest.templates ?? [])
        {
            if (!SafeGateName(name) || template is null || string.IsNullOrWhiteSpace(template.path) ||
                template.values?.Values.Any(value => value is null) == true)
                throw new InvalidDataException("Invalid template " + name + ": expected a path and string values.");
            templates[name] = template;
        }
        // Results, generated paths and --profile use a named profile's name; extraction reads its file.
        var profileFiles = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var (name, file) in manifest.profiles ?? [])
        {
            if (!SafeGateName(name) || file is not ['@', _, ..])
                throw new InvalidDataException("Invalid profile " + name + ": expected a name and an @file.");
            if (BuiltInProfile(name))
                throw new InvalidDataException("Profile " + name + " has the name of a built-in profile.");
            profileFiles[name] = "@" + Path.GetFullPath(file[1..], directory);
        }

        GateBuildPlan? Plan(string owner, GateBuild? build)
        {
            if (build is null) return null;
            if (build.project is null || !projects.TryGetValue(build.project, out var project))
                throw new InvalidDataException(owner + " builds an undeclared project: " + build.project);
            CheckBuildProperties(owner, build.properties);
            var merged = new Dictionary<string, string>(project.properties ?? [], StringComparer.OrdinalIgnoreCase);
            foreach (var (name, value) in build.properties ?? []) merged[name] = value;
            var properties = new SortedDictionary<string, string>(merged, StringComparer.OrdinalIgnoreCase);
            var path = Path.GetFullPath(project.path, directory);
            var key = ContentKey(path + "\n" +
                string.Join("\n", properties.Select(pair => pair.Key + "=" + pair.Value)));
            return new(path, project.assembly, properties, Path.Combine(outputRoot, "builds", key[..16]));
        }

        // A template is a key of `templates` or a file path; values given at the use override the entry's.
        (string Path, Dictionary<string, string> Values)? Template(string owner, string? template,
            Dictionary<string, string>? values)
        {
            if (template is null)
                return values is null ? null
                    : throw new InvalidDataException(owner + " gives values without a template.");
            if (generatedRoot is null) throw new InvalidDataException("Templates need generatedRoot: " + owner);
            var merged = new Dictionary<string, string>(StringComparer.Ordinal);
            var path = template;
            if (templates.TryGetValue(template, out var entry))
            {
                path = entry.path;
                foreach (var (name, value) in entry.values ?? []) merged[name] = value;
            }
            foreach (var (name, value) in values ?? [])
                merged[name] = value ?? throw new InvalidDataException(owner + " gives a null value for " + name);
            return (Within(proofRoot, path), merged);
        }

        var rows = new List<GateRow>();
        var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var gate in manifest.gates)
        {
            if (gate is null || !SafeGateName(gate.name) || !names.Add(gate.name) ||
                (gate.assembly is null) == (gate.build is null) || string.IsNullOrWhiteSpace(gate.method) ||
                string.IsNullOrWhiteSpace(gate.proof) || string.IsNullOrWhiteSpace(gate.theorem) ||
                gate.profiles is not { Length: > 0 } || gate.profiles.Any(string.IsNullOrWhiteSpace) ||
                gate.profiles.Distinct(StringComparer.Ordinal).Count() != gate.profiles.Length)
                throw new InvalidDataException(
                    "Invalid or duplicate gate entry; a gate gives one of assembly or build.");
            var gatePlan = Plan(gate.name, gate.build);
            var gateRows = new List<GateRow>();
            foreach (var profile in gate.profiles)
                gateRows.Add(Row("production", "verified", gate.assembly, gatePlan, profile, gate.proof, null,
                    gate.theorem, gate.initializedTypes, null, null, null, null, null));
            var variants = new Dictionary<string, GateVariant>(StringComparer.OrdinalIgnoreCase);
            foreach (var variant in gate.variants ?? [])
            {
                var owner = gate.name + "/" + variant?.name;
                if (variant is null || !SafeGateName(variant.name) || variant.name.Equals("production",
                        StringComparison.OrdinalIgnoreCase) || !variants.TryAdd(variant.name, variant) ||
                    (variant.assembly is null) == (variant.build is null) ||
                    variant.expect is not ("certifies" or "rejected" or "unchanged") ||
                    variant.program is not (null or "same" or "different" or "renamed") ||
                    (variant.proof is null) != (variant.theorem is null) ||
                    (variant.refutation is null) == (variant.expect == "rejected") ||
                    variant.statement is not (null or "independent") ||
                    (variant.statement is not null && variant.expect != "certifies") ||
                    (variant.expect == "unchanged" && (variant.program is null || variant.proof is not null)) ||
                    (variant.programOf is not null && variant.program is null))
                    throw new InvalidDataException("Invalid or duplicate variant " + owner + ": it gives one of " +
                        "assembly or build, proof and theorem together, a refutation exactly when it expects " +
                        "rejection, a statement only when it certifies, and a program when it expects unchanged or " +
                        "names programOf; an unchanged variant gives no proof.");
                var profiles = variant.profiles ?? gate.profiles;
                if (profiles.Length == 0 || profiles.Distinct(StringComparer.Ordinal).Count() != profiles.Length ||
                    profiles.Any(profile => !gate.profiles.Contains(profile, StringComparer.Ordinal)))
                    throw new InvalidDataException("Variant " + owner +
                        " lists a profile its gate does not, or none.");
                var refutation = variant.refutation;
                if (refutation is not null && (string.IsNullOrWhiteSpace(refutation.theorem) ||
                    (refutation.proof is null) == (refutation.template is null)))
                    throw new InvalidDataException("Refutation of " + owner + " gives a theorem and either a proof " +
                        "or a template.");
                var refutationTemplate = Template("Refutation of " + owner, refutation?.template, refutation?.values);
                string? proofPath = null;
                (string, Dictionary<string, string>)? proofTemplate = null;
                if (variant.proof is { } proof)
                {
                    if (proof.ValueKind == JsonValueKind.String) proofPath = proof.GetString();
                    else if (proof.ValueKind == JsonValueKind.Object &&
                        proof.Deserialize<GateTemplateUse>(GateManifestJson) is { } use)
                        proofTemplate = Template("Proof of " + owner, use.template, use.values ?? []);
                    if (string.IsNullOrWhiteSpace(proofPath) && proofTemplate is null)
                        throw new InvalidDataException("Proof of " + owner + " gives a path or a template.");
                }
                var plan = Plan(owner, variant.build);
                foreach (var profile in profiles)
                    gateRows.Add(Row(variant.name, variant.expect == "certifies" ? "verified" : variant.expect,
                        variant.assembly, plan, profile, proofPath ?? gate.proof, proofTemplate,
                        variant.theorem ?? gate.theorem, variant.initializedTypes ?? gate.initializedTypes,
                        variant.program, variant.programOf, refutation, refutationTemplate, variant.statement));
            }
            foreach (var (name, variant) in variants.Where(pair => pair.Value.programOf is not null))
            {
                // Following programOf from any variant must end at production.
                var seen = new HashSet<string>(StringComparer.OrdinalIgnoreCase) { name };
                for (var next = variant.programOf; next is not null and not "production";
                    next = variants[next].programOf)
                    if (!variants.ContainsKey(next) || !seen.Add(next))
                        throw new InvalidDataException("Variant " + gate.name + "/" + name + " compares its program " +
                            "with an unknown variant or through a cycle: " + next);
            }
            foreach (var row in gateRows.Where(row => row.ExpectedProgram is not null))
                row.ProgramBase = gateRows.SingleOrDefault(other => other.Profile == row.Profile &&
                    other.Variant.Equals(row.ProgramOf ?? "production", StringComparison.OrdinalIgnoreCase)) ??
                    throw new InvalidDataException("Variant " + row.Name + " compares its program with " +
                        row.ProgramOf + ", which does not run under profile " + row.Profile + ".");
            if (methodFilter is not null && !gate.method.Contains(methodFilter, StringComparison.Ordinal)) continue;
            rows.AddRange(gateRows.Where(row => profileFilter is null || row.Profile == profileFilter));

            GateRow Row(string variant, string expect, string? assembly, GateBuildPlan? plan, string profile,
                string proof, (string Path, Dictionary<string, string> Values)? proofTemplate, string theorem,
                string[]? initializedTypes, string? program, string? programOf, GateRefutation? refutation,
                (string Path, Dictionary<string, string> Values)? refutationTemplate, string? statement)
            {
                var generated = new List<GateGenerated>();
                string Generate(string kind, (string Path, Dictionary<string, string> Values) template)
                {
                    // Built-in and named profiles are path segments; a profile file is named by its content key.
                    string[] directories = [.. generatedRoot!, gate.name,
                        SafeGateName(profile) ? profile : ContentKey(profile)[..12], variant];
                    if (directories.Any(ExcludedConsumerDirectory))
                        throw new InvalidDataException("Generated proofs of " + gate.name + "/" + variant +
                            " would lie in a directory verification skips: " + string.Join('/', directories));
                    var relative = string.Join('/', directories) + "/" + kind + ".lean";
                    ProofBindingCatalog.CheckPath(relative);
                    var path = Within(proofRoot, relative);
                    generated.Add(new(template.Path, template.Values, path, kind.ToLowerInvariant() + " template"));
                    return path;
                }
                var proofPath = proofTemplate is { } own ? Generate("Proof", own) : Within(proofRoot, proof);
                var refutationProof = refutationTemplate is { } negation ? Generate("Refutation", negation)
                    : refutation?.proof is { } given ? Within(proofRoot, given) : null;
                return new()
                {
                    Gate = gate.name, Profile = profile, Variant = variant, Expect = expect,
                    Output = Path.Combine(outputRoot, gate.name, ContentKey(profile)[..12], variant),
                    Proof = proofPath, Theorem = theorem,
                    Assembly = assembly is null ? null : Path.GetFullPath(assembly, directory), Build = plan,
                    ExpectedProgram = program, ProgramOf = programOf, RefutationProof = refutationProof,
                    RefutationTheorem = refutation?.theorem, Statement = statement, Generated = [.. generated],
                    InitializedTypes = initializedTypes, TypeArguments = gate.typeArguments, Method = gate.method,
                    ExtractionProfile = profileFiles.TryGetValue(profile, out var file) ? file
                        : profile.StartsWith('@') ? "@" + Path.GetFullPath(profile[1..], directory) : profile
                };
            }
        }
        return rows;
    }

    /// <summary>Whether `name` selects a built-in execution profile, including a retired one.</summary>
    static bool BuiltInProfile(string name)
    {
        try
        {
            FeatureProfile.Select(name);
            return true;
        }
        catch (ArgumentException error) when (error.Message.StartsWith("Unknown execution profile",
            StringComparison.Ordinal))
        {
            return false;
        }
        catch (ArgumentException) { return true; }
    }

    /// <summary>Rejects build properties that are not plain MSBuild names and values, or that the tool owns.</summary>
    static void CheckBuildProperties(string owner, Dictionary<string, string>? properties)
    {
        foreach (var (name, value) in properties ?? [])
            if (!Regex.IsMatch(name, @"\A[A-Za-z_][A-Za-z0-9_]*\z") || ReservedBuildProperties.Contains(name) ||
                value is null || value.IndexOfAny([';', ',', '%', '"', '\r', '\n']) >= 0)
                throw new InvalidDataException($"Invalid build property {name} of {owner}: names are MSBuild " +
                    "identifiers other than the output paths the tool sets, and values hold no ; , % or quote.");
    }

    /// <summary>
    /// Writes `generated` from its template, or removes the stale file and fails the row when the template is
    /// missing or its placeholders and values differ.
    /// </summary>
    static void InstantiateGenerated(GateRow row, GateGenerated generated, string proofRoot)
    {
        ProofBindingCatalog.CheckLinks(proofRoot, generated.Path);
        try
        {
            if (!File.Exists(generated.Template))
                throw new FileNotFoundException("Template not found: " + CliPaths.Display(generated.Template));
            var bytes = new UTF8Encoding(false).GetBytes(
                Instantiate(File.ReadAllText(generated.Template), generated.Values));
            if (File.Exists(generated.Path) && File.ReadAllBytes(generated.Path).AsSpan().SequenceEqual(bytes)) return;
            Directory.CreateDirectory(Path.GetDirectoryName(generated.Path)!);
            File.WriteAllBytes(generated.Path, bytes);
        }
        catch (Exception error) when (error is IOException or InvalidDataException)
        {
            // A variant's directory may not exist yet; a stale file from an earlier run must not be checked.
            if (File.Exists(generated.Path)) File.Delete(generated.Path);
            row.Fail(generated.Stage, error.Message);
        }
    }

    /// <summary>
    /// `template` with each `@NAME@` replaced by `values[NAME]` and LF line endings; nothing else changes.
    /// A placeholder without a value, or a value no placeholder uses, is an error.
    /// </summary>
    static string Instantiate(string template, IReadOnlyDictionary<string, string> values)
    {
        var used = new HashSet<string>(StringComparer.Ordinal);
        var missing = new SortedSet<string>(StringComparer.Ordinal);
        var text = TemplatePlaceholder().Replace(template, match =>
        {
            var name = match.Groups[1].Value;
            if (!values.TryGetValue(name, out var value))
            {
                missing.Add(name);
                return match.Value;
            }
            used.Add(name);
            return value;
        });
        if (missing.Count > 0)
            throw new InvalidDataException("Template placeholders without a value: " + string.Join(", ", missing));
        var unused = values.Keys.Where(name => !used.Contains(name)).Order(StringComparer.Ordinal).ToArray();
        if (unused.Length > 0)
            throw new InvalidDataException("Template values no placeholder uses: " + string.Join(", ", unused));
        return text.ReplaceLineEndings("\n");
    }

    [GeneratedRegex(@"@([A-Za-z_][A-Za-z0-9_]*)@")]
    private static partial Regex TemplatePlaceholder();

    /// <summary>
    /// Builds each distinct project and property set the rows use once, and gives each row its assembly. A
    /// failed build fails every row that uses it.
    /// </summary>
    static void BuildGateProjects(IEnumerable<GateRow> rows)
    {
        foreach (var group in rows.Where(row => row.Build is not null && !row.Failed)
            .GroupBy(row => row.Build!.Directory))
        {
            var plan = group.First().Build!;
            string? assembly = null, error = null;
            try { assembly = BuildGateProject(plan); }
            catch (Exception failure) when (failure is InvalidOperationException or IOException)
            {
                error = failure.Message;
            }
            foreach (var row in group)
            {
                row.BuildStatus = error is null ? "built" : "failed";
                if (error is null) row.Assembly = assembly;
                else row.Fail("build", error);
            }
        }
    }

    /// <summary>
    /// Builds `plan` with `dotnet build` into its own output, intermediate and project-extension directories,
    /// and returns the assembly of the project's name in its output directory.
    /// </summary>
    static string BuildGateProject(GateBuildPlan plan)
    {
        var output = Path.Combine(plan.Directory, "bin") + Path.DirectorySeparatorChar;
        var intermediate = Path.Combine(plan.Directory, "obj") + Path.DirectorySeparatorChar;
        if (!File.Exists(plan.Project))
            throw new InvalidDataException("Project not found: " + CliPaths.Display(plan.Project));
        var assembly = Path.Combine(output, plan.AssemblyName);
        // A stale assembly from an earlier build of this key must not pass for this build's output.
        if (Directory.Exists(output)) File.Delete(assembly);
        // Global properties override a project's own, so a Directory.Build.props cannot redirect the outputs.
        Run(["dotnet", "build", plan.Project, "-nologo", "-v:q", "-p:BaseOutputPath=" + output,
            "-p:OutputPath=" + output, "-p:OutDir=" + output, "-p:BaseIntermediateOutputPath=" + intermediate,
            "-p:IntermediateOutputPath=" + Path.Combine(intermediate, "build") + Path.DirectorySeparatorChar,
            "-p:MSBuildProjectExtensionsPath=" + intermediate,
            .. plan.Properties.Select(pair => $"-p:{pair.Key}={pair.Value}")], Path.GetDirectoryName(plan.Project),
            progress: "Building " + Path.GetFileName(plan.Project) + " " +
                string.Join(' ', plan.Properties.Select(pair => pair.Key + "=" + pair.Value)));
        return File.Exists(assembly) ? assembly : throw new InvalidDataException(
            $"The build wrote no {plan.AssemblyName} to {CliPaths.Display(output)}.");
    }

    /// <summary>Extracts every row that has an assembly; a failed extraction fails only its own row.</summary>
    static void ExtractGateRows(IEnumerable<GateRow> rows)
    {
        var ready = rows.Where(row => !row.Failed).ToArray();
        foreach (var row in ready)
            row.Extraction = new(row.Assembly!, row.Method, row.Output, row.ExtractionProfile, row.InitializedTypes,
                row.TypeArguments);
        Extract(ready);

        // One extraction process stops at its first failure, so a failed batch is retried per row.
        static void Extract(GateRow[] batch)
        {
            if (batch.Length == 0) return;
            try
            {
                ExtractBatch("extract", null, batch.Select(row => row.Extraction!));
                foreach (var row in batch) row.ExtractionStatus = "extracted";
            }
            catch (InvalidOperationException) when (batch.Length > 1)
            {
                foreach (var row in batch) Extract([row]);
            }
            catch (InvalidOperationException error)
            {
                batch[0].ExtractionStatus = "failed";
                batch[0].Fail("extraction", error.Message);
            }
        }
    }

    /// <summary>Fails `row` unless its program relates to its base row's as the manifest says.</summary>
    static void CompareGateProgram(GateRow row, GateRow origin)
    {
        try
        {
            if (origin.Failed)
                throw new InvalidDataException($"The extraction of {origin.Name} is unavailable: {origin.Stage} " +
                    "failed.");
            var relation = ProgramRelation(origin.Output, row.Output);
            if (relation != row.ExpectedProgram)
                throw new InvalidDataException($"Expected the program to be {row.ExpectedProgram} with respect " +
                    $"to {origin.Variant}, but it is {relation}.");
            row.ProgramStatus = "passed";
        }
        catch (Exception error) when (error is IOException or InvalidDataException)
        {
            row.ProgramStatus = "failed";
            row.Fail("program comparison", error.Message);
        }
    }

    /// <summary>
    /// How the program extracted into `variant` relates to the one in `production`: `same` when the method
    /// bodies (each `def methodN : Method`, in order) and method signatures are equal, `renamed` when only the
    /// signatures differ, otherwise `different`. Everything else in Extracted.lean is ignored, including the
    /// assembly identity, digests, paths and metadata tokens.
    /// </summary>
    static string ProgramRelation(string production, string variant)
    {
        static (string[] Bodies, string[] Signatures) Methods(string output)
        {
            var text = File.ReadAllText(Path.Combine(output, "Extracted.lean")).ReplaceLineEndings("\n");
            string[] bodies = [.. MethodBody().Matches(text).Select(match => match.Value)];
            if (bodies.Length == 0)
                throw new InvalidDataException("No method bodies in " + CliPaths.Display(output));
            return (bodies, [.. MethodSignature().Matches(text).Select(match => match.Value)]);
        }
        var (bodies, signatures) = Methods(production);
        var (variantBodies, variantSignatures) = Methods(variant);
        return !bodies.SequenceEqual(variantBodies) ? "different"
            : signatures.SequenceEqual(variantSignatures) ? "same" : "renamed";
    }

    [GeneratedRegex(@"^def method\d+ : Method := .*?(?=^\S)", RegexOptions.Multiline | RegexOptions.Singleline)]
    private static partial Regex MethodBody();

    [GeneratedRegex(@"^def method\d+Signature : String := .*$", RegexOptions.Multiline)]
    private static partial Regex MethodSignature();

    /// <summary>
    /// The result of `row`: its verdict, its proof's outcome, its refutation's when it has one, and how its
    /// statement relates to production's. A statement that fails to match fails a variant whose legs all passed,
    /// at its own stage. An `unchanged` variant passes on its program comparison alone.
    /// </summary>
    static GateResult GateOutcome(GateRow row, bool checkOnly, (int? Refutation, int Proof)? index,
        BatchResult[] results, (GateStatement? Statement, string? Error) statement)
    {
        if (index is not { } requested)
        {
            var unchanged = row.Expect == "unchanged" && !row.Failed;
            return new(row.Output, row.Proof, row.Theorem, checkOnly && !unchanged ? "checked" : row.Expect,
                unchanged ? "unchanged" : "failed", unchanged ? "program comparison" : row.Stage!, row.Error, null,
                null, null, 0, row.Gate, row.Profile, row.Variant, row.BuildStatus, row.ExtractionStatus,
                row.ProgramStatus, null, null);
        }
        var proof = results[requested.Proof];
        var refutation = requested.Refutation is { } at ? results[at] : null;
        var passed = proof.status != "failed" && refutation?.status is null or "verified";
        var mismatch = passed && statement.Error is not null;
        return new(proof.output, proof.proof, proof.theorem, proof.expect,
            passed && !mismatch ? proof.status : "failed", mismatch ? StatementIdentityStage : proof.stage,
            mismatch ? statement.Error : proof.error, proof.axioms, proof.libraryBuild, proof.failure,
            proof.elapsedSeconds, row.Gate, row.Profile, row.Variant, row.BuildStatus, row.ExtractionStatus,
            row.ProgramStatus, refutation is null ? null : new(refutation.proof, refutation.theorem, refutation.status,
                refutation.stage, refutation.error, refutation.axioms), statement.Statement);
    }

    /// <summary>
    /// How the statement `row` verified relates to production's statement `T`: the kernel must accept a `rejected`
    /// variant's refutation at `¬ T` and any other variant's theorem at `T`, in the variant's own environment. No
    /// statement is compared when the variant's own leg did not verify; that leg reports why.
    /// </summary>
    static (GateStatement?, string?) CompareGateStatement(GateRow row, GateRow production, string productionStage,
        Report? productionReport, Report? variantReport)
    {
        if (variantReport is null) return (null, null);
        var refutes = row.Expect == "rejected";
        var shown = StatementOf(variantReport);
        var expected = productionReport?.statementIdentity;
        var identity = variantReport.statementIdentity;
        var reason = productionReport is null
            ? $"Production {production.Name} did not verify (stage: {productionStage}), so the statement of " +
                $"{row.Name} has nothing to match."
            : expected?.term is null
            ? $"Production {production.Name} has no statement to compare: {expected?.termError ?? "none reported"}"
            : identity?.matches is null ? $"{variantReport.theorem} was not compared with production's statement."
            : identity.matches == true ? null
            : (refutes ? $"Refutation {variantReport.theorem} does not state the negation of production's statement"
                : $"{variantReport.theorem} does not state production's statement") + ": " + identity.mismatch;
        var productionText = productionReport is null ? null : StatementOf(productionReport);
        var status = reason is null ? "same" : identity?.matches == false ? "different" : "unavailable";
        return (new(status, productionText, shown), reason is null ? null : reason + "\n  Production: " +
            (productionText ?? "unavailable") + "\n  " + (refutes ? "Refutation: " : "Variant: ") + shown);
    }

    static bool SafeGateName(string? name) => name is not (null or "" or "." or "..") &&
        Regex.IsMatch(name, @"\A[A-Za-z0-9_.-]+\z");

    /// <summary>Whether `path` is `directory` or lies under it.</summary>
    static bool Under(string path, string directory)
    {
        var relative = Path.GetRelativePath(directory, path);
        return !Path.IsPathRooted(relative) && relative != ".." &&
            !relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal);
    }

    // PDBs only select work. Missing source information conservatively selects the method.
    static bool GateMethodAffected(GeneratedExtraction extraction, HashSet<string> changed)
    {
        if (changed.Contains(extraction.Assembly)) return true;
        if (changed.Any(path => Path.GetExtension(path) is ".csproj" or ".props" or ".targets")) return true;
        if (!changed.Any(path => Path.GetExtension(path) == ".cs")) return false;
        using var module = ModuleDefinition.ReadModule(extraction.Assembly);
        if (Symbols.Read(module, extraction.Assembly, out _) is null) return true;
        var identityPath = Path.Combine(extraction.Output, "identity.json");
        using var identity = JsonDocument.Parse(File.ReadAllText(identityPath));
        if (identity.RootElement.GetProperty("references").GetArrayLength() > 0) return true;
        foreach (var method in identity.RootElement.GetProperty("methods").EnumerateArray())
        {
            if (module.LookupToken(method.GetProperty("token").GetInt32()) is not MethodDefinition definition ||
                !definition.DebugInformation.HasSequencePoints) return true;
            if (definition.DebugInformation.SequencePoints.Where(point => !point.IsHidden).Any(point =>
                changed.Contains(Path.GetFullPath(point.Document.Url)))) return true;
        }
        return false;
    }
}
