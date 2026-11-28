using System.Runtime.CompilerServices;
using System.Text.Json;
using System.Text.RegularExpressions;

// Conservative suite ownership: unknown/shared inputs select every suite.
internal static class VerificationSelection
{
    internal static string Root { get; } = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(Source())!, ".."));
    static string Source([CallerFilePath] string path = "") => path;
    static IEnumerable<string> Matches(string text, string pattern, RegexOptions options = RegexOptions.None) =>
        Regex.Matches(text, pattern, options).Select(match => match.Groups[1].Value);
    static string Relative(string root, string path) => Path.GetRelativePath(root, path).Replace('\\', '/');

    internal sealed record RunDurations(string WorkflowRun, Dictionary<string, double> Suites,
        int SetupSeconds, int LibrarySeconds);

    internal static RunDurations ReadDurations(string? root = null)
    {
        using var data = JsonDocument.Parse(File.ReadAllText(Path.Combine(root ?? Root, "scripts/verification-durations.json")));
        var durations = new Dictionary<string, double>(StringComparer.Ordinal);
        foreach (var property in data.RootElement.GetProperty("seconds").EnumerateObject())
        {
            if (property.Value.ValueKind != JsonValueKind.Number || !property.Value.TryGetDouble(out var seconds) ||
                !double.IsFinite(seconds) || seconds <= 0)
                throw new InvalidDataException("Suite durations must be positive numbers");
            durations[property.Name] = seconds;
        }
        if (durations.Count == 0) throw new InvalidDataException("Suite durations must be positive numbers");
        var setup = data.RootElement.GetProperty("setupSeconds").GetInt32();
        var library = data.RootElement.GetProperty("librarySeconds").GetInt32();
        if (setup <= 0 || library <= 0) throw new InvalidDataException("Job and library durations must be positive");
        return new(data.RootElement.GetProperty("workflowRun").GetString()!, durations, setup, library);
    }

    internal static string[] Schedule(IEnumerable<string> suites, string? root = null)
    {
        var durations = ReadDurations(root).Suites;
        // Unknown suites start first rather than leaving a potentially long job at the tail.
        var unknown = durations.Values.Max() + 1;
        return suites.OrderByDescending(name => durations.GetValueOrDefault(name, unknown))
            .ThenBy(name => name, StringComparer.Ordinal).ToArray();
    }

    // Proof marks a job that runs a proof suite, whose outputs the job then measures for proof cost.
    // Libraries marks the one job that also measures the test libraries when a run compares them.
    internal sealed record Group(string Suite, string[] Suites, int Timeout, bool Proof, bool Libraries);

    // The suite jobs that run at once, which the workflow's `max-parallel` sets.
    internal const int Runners = 8;

    // More members than this make a job's summary long and its name useless for finding a failure.
    internal const int GroupMembers = 12;

    // Cap each group at one runner's share of the active automatic suites (with a small packing
    // margin), or 110% of the longest single suite when one suite dominates the run.
    const double LongestSuiteAllowance = 1.10;
    const double PackingAllowance = 1.05;
    internal static double GroupSeconds(IReadOnlyDictionary<string, double> durations,
        double librarySeconds = 0)
    {
        var manual = new HashSet<string>(VerificationSuites.ManualSuites, StringComparer.Ordinal);
        var active = durations.Where(pair => !manual.Contains(pair.Key))
            .Select(pair => pair.Value).ToArray();
        var values = active.Length > 0 ? active : durations.Values.ToArray();
        return Math.Max(values.Max() * LongestSuiteAllowance,
            (values.Sum() + librarySeconds) / Runners * PackingAllowance);
    }

    // A job's suites when few enough to read, else its longest suite and how many more it runs.
    static string Name(List<string> group) => group.Count <= 3 ? string.Join("+", group)
        : $"{group[0]}+{group.Count - 1}more";

    // Give the next suite to the runner with the least work, including each job's setup.
    // Short selections share a job. Unknown suites start first and run alone.
    internal static Group[] Groups(IEnumerable<string> suites, string? root = null, bool planLibraries = true,
        bool planProofs = true)
    {
        var run = ReadDurations(root);
        var durations = run.Suites;
        var selected = suites.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        if (selected.Length == 0) return [];
        var target = GroupSeconds(durations, planLibraries ? run.LibrarySeconds : 0);
        double Seconds(string suite) => durations.GetValueOrDefault(suite, double.PositiveInfinity);
        var carrier = selected.MinBy(Seconds)!;
        double Work(string suite) =>
            Seconds(suite) + (planLibraries && suite == carrier ? run.LibrarySeconds : 0);
        var measured = selected.Where(durations.ContainsKey).OrderByDescending(Work).ToArray();
        var workers = (int)Math.Clamp(Math.Ceiling(measured.Sum(Work) / target), 1, Runners);
        var loads = new double[workers];
        var assigned = Enumerable.Range(0, workers).Select(_ => new List<List<string>>()).ToArray();
        var groups = selected.Where(suite => !durations.ContainsKey(suite))
            .Select(suite => new List<string> { suite }).ToList();
        foreach (var suite in measured)
        {
            bool Fits(List<string> group) => group.Count < GroupMembers &&
                group.Sum(Work) + Work(suite) <= target;
            var available = Enumerable.Range(0, workers)
                .Where(i => assigned[i].Count == 0 || assigned[i].Any(Fits)).ToArray();
            var worker = available.Length > 0
                ? available.MinBy(i => loads[i] + (assigned[i].Count == 0 ? run.SetupSeconds : 0))
                : Enumerable.Range(0, workers).MinBy(i => loads[i] + run.SetupSeconds);
            var group = assigned[worker].LastOrDefault(Fits);
            if (group is null)
            {
                group = [];
                assigned[worker].Add(group);
                groups.Add(group);
                loads[worker] += run.SetupSeconds;
            }
            group.Add(suite);
            loads[worker] += Work(suite);
        }
        return groups.OrderByDescending(group => group.Sum(Work))
            .Select(group => group.OrderByDescending(Seconds).ToList()).Select(group =>
            {
                var libraries = group.Contains(carrier);
                var budget = group.Sum(Seconds) + (libraries ? run.LibrarySeconds : 0);
                return new Group(Name(group), group.ToArray(), Timeout(group, budget),
                    planProofs && group.Any(VerificationSuites.ProofSuites.Contains), libraries);
            }).ToArray();
    }

    const int TimeoutStepMinutes = 10;

    // A job is stopped at the largest limit of its members and no sooner than twice its measured
    // time, in whole steps: a suite that slows by half still finishes, and a hung one is stopped.
    static int Timeout(List<string> group, double seconds)
    {
        var named = group.Max(name => name == "imports" ? 90 :
            name.StartsWith("exports", StringComparison.Ordinal) ? 120 : 30);
        if (!double.IsFinite(seconds)) return named;
        var measured = (int)Math.Ceiling(seconds * 2 / (TimeoutStepMinutes * 60)) * TimeoutStepMinutes;
        return Math.Max(named, measured);
    }

    internal static Dictionary<string, HashSet<string>> SuiteInputs(string? root = null)
    {
        root ??= Root;
        var inputs = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
        foreach (IndependentSuite suite in VerificationSuites.Independent)
            inputs.Add(suite.Name, new(StringComparer.Ordinal) { suite.Script });
        foreach (ExportSuite entry in ExportVerificationSuites.Plan())
        {
            if (!File.Exists(Path.Combine(root, entry.Script)))
                throw new InvalidDataException("Missing registered export fixture: " + entry.Script);
            if (entry.ChildScript is string child && !File.Exists(Path.Combine(root, child)))
                throw new InvalidDataException("Missing registered export fixture: " + child);
            inputs.Add(entry.Name, new(entry.Inputs.Append(entry.Script), StringComparer.Ordinal));
        }
        inputs["core"] = new(StringComparer.Ordinal)
        {
            "Examples/Verify.cs", "Examples/Hardware/Hardware.cs", "scripts/Verify.cs",
            "Tests/LibraryCache.cs", "Tests/InitializedTypes.cs", "Tests/ConsumerVerification.cs",
            "Tests/ProofBindingCatalog.cs", "Tests/ProofBindingFamilies.cs", "Tests/BindingFamilies/Support.lean",
            "Tests/BindingFamilies/Binding.lean.in", "Tests/BindingFamilies/Bindings.json",
            "Tests/BindingFamilies/Negative.json", "Tests/GatePlans.cs", "Tests/PublicProofSurface.lean",
            "Tests/ProofCostFrontend.cs", "Tests/ConsumerSupportCandidates.cs",
            "Tests/MethodSelectors.cs", "Tests/MetadataMutator.cs", "Tests/Semantics.lean",
            "Tests/Automation.lean", "Tests/MethodBinding.lean", "Tests/MethodIdentity.lean",
            "Tests/StructuralLabels.lean", "Tests/DebugNames.lean", "Tests/MethodContract.lean",
            "Tests/ConstructContract.lean", "Tests/OutcomeContract.lean", "Tests/Imports.lean",
            "Tests/LoopOutcome.lean", "Tests/OutcomeEmbedding.lean", "Tests/MethodEmbedding.lean",
            "Tests/ConfinedFootprints.lean", "Tests/LocalSnapshots.lean", "Tests/ContractConsequence.lean",
            "Tests/InvocationCertificates.lean", "Tests/ValidCallTransport.lean",
            "Tests/BufferContents.lean", "Tests/Linking.lean", "Tests/StepFlow.lean", "Tests/RegionRun.lean",
            "Tests/StoreFacts.lean", "Tests/BatchVerification.cs", "Tests/VerificationCache.cs",
            "Tests/VerificationReuse.cs", "Tests/SupportExtractionCache.cs", "Tests/SummaryCalls.cs",
            "Tests/AllocationImports.cs", "Tests/JointReplay.cs", "Tests/BuildReuse.cs",
            "Tests/EnvironmentLimit.cs", "Tests/ExtractionBatch.cs", "Tests/InstructionIndexes.cs",
            "Tests/TemplateIndexes.cs", "Tests/OutlineStops.cs", "Tests/ImportIndexes.cs",
            "Tests/StaticValueIndexes.cs", "Tests/DecodedOpcodes.cs",
            "Tests/RuntimeExceptions.lean", "Tests/ProfileContract.lean",
            "Tests/InstructionEquations.lean", "Tests/CodeAt.lean", "Tests/SimdLanes.lean",
            "Tests/SegmentContract.lean",
            "Tests/OperationFacts.lean", "Tests/VectorLocalCalls.lean", "Tests/SimdCarryCalls.lean",
            "Tests/OperationFactAdapters.lean", "Tests/AggregateMemorySteps.lean", "Tests/BodyDecoding.lean",
            "Tests/Identity.lean", "Tests/MetadataDecoding.lean",
            "Tests/MetadataBinding.lean", "Tests/MetadataBuilder.lean", "Tests/ResolutionFacts.lean",
            "Tests/ValueDecoding.lean", "Tests/DecodedMethod.lean", "Tests/DecodedSummary.lean",
            "Tests/DecodedSegment.lean", "Tests/LoopSummary.lean",
            "Tests/ReplayDiagnostics.lean", "Tests/BodyLiteral.lean", "Tests/ReturnOpcode.lean",
            "Tests/ReturnMetadataBinding.lean", "Tests/ReferenceArrays.lean", "Tests/ArrayFields.lean",
            "Tests/RetainedNumericLocals.lean", "Tests/ProfileEmbedding.lean", "Tests/FullTransfer.lean",
            "Tests/Crypto.lean", "Tests/MetadataAssemblies.lean", "Tests/PinnedIndexScaling.lean",
            "Tests/PinnedIndexScaling/Construction.lean",
            "Tests/FieldRef.lean", "Tests/FieldShape.lean", "Tests/RuntimeModels.lean",
            "Tests/PlatformDefinitions.lean", "Tests/BitModels.lean", "Tests/SpanHomes.lean"
        };
        inputs["core"].UnionWith(new[] { "Add", "AddModel", "DecodedAdd", "Choose", "Calls", "CallsSummary",
            "CountCallsSummary", "IdentitySummary", "RepeatedSummary", "VectorSummary", "Alias", "Struct",
            "StructCopy", "LargeStruct", "PastEnd", "WrongAdd", "Escape", "Hardware", "StaticData" }
            .Select(name => $"Examples/Proofs/{name}.lean"));
        inputs["core"].Add("Tests/ModularStatics.lean");
        inputs["docs"].UnionWith(WalkthroughInputs(root));
        inputs["evidence"].UnionWith(new[] { "LayoutEvidence", "ParameterEvidence", "GenericEvidence", "FeatureEvidence", "TypeTests",
            "Throws", "SpanTables", "StaticValues", "StaticScalarValues", "TranslationAudit", "MetadataDifferential",
            "Guards", "CallSiteAgreement" }
            .Select(name => $"Tests/{name}.cs"));
        inputs["evidence"].Add("Examples/Proofs/Percent.lean");
        inputs["evidence"].UnionWith(new[] { "ExtractionLayout", "ExtractionParameters", "FeatureEvidence", "ScalarEvidence", "TypeTestEvidence",
            "ThrowEvidence", "SpanEvidence", "StaticValueEvidence", "LayoutCoverage", "ImportEvidence", "ImportedLayouts", "AssemblyPins",
            "BodyEncoding", "CallDecoding", "PercentRuntime", "PercentRuntime/Source",
            "PercentRuntime/Startup", "PercentRuntime/Program", "CompiledPercent/Proof", "ExceptionConstructor/Proof" }
            .Select(name => $"Tests/{name}.lean"));
        inputs["imports"].UnionWith(["Tests/ContractClosure.lean", "Tests/ContractImports/Lib.leancil.contracts", "Tests/ContractImports/ImportFixture.lean", "Tests/ContractImports/Caller.lean",
            "Tests/ContractImports/Lib/Lib.csproj", "Tests/ContractImports/Lib/Library.cs", "Tests/ContractImports/App/App.csproj", "Tests/ContractImports/App/Application.cs"]);
        inputs["closures"].UnionWith(["Tests/ProgramClosures/Proof.lean",
            "Tests/ProgramClosures/Assembly/ProgramClosures.csproj", "Tests/ProgramClosures/Assembly/Closure.cs"]);
        inputs["unsafe"].UnionWith(["Tests/SkipInitialization.cs", "Tests/NullReferences.cs"]);
        inputs["intrinsics"].UnionWith(["Tests/ExactIntrinsics.lean", "Tests/ExactIntrinsics/WordContracts.lean"]);
        // Generated outlines emit `import CIL.Safety.LoopScaffold` at runtime.
        inputs["outlines"].Add("CIL/Safety/LoopScaffold.lean");
        inputs["outlines-components"].Add("CIL/Safety/LoopScaffold.lean");
        inputs["stepping"].Add("scripts/ProofCost.lean");
        // Self-admission scans the extractor itself, so every source compiled into it can change the result.
        inputs["blockers"].UnionWith(["Tests/SelfAdmissionBaseline.txt", "Tests/ExampleAdmissionBaseline.txt"]);
        inputs["blockers"].UnionWith(["Tests/HoleCorpus.cs", "Tests/HoleCorpusBaseline.txt"]);
        inputs["blockers"].UnionWith(Matches(File.ReadAllText(Path.Combine(root, "Extractor/Extractor.csproj")),
            @"<Compile Include=""\.\./([^""]+\.cs)""").Select(path => path.Replace('\\', '/')));

        // Each suite owns its transitive inputs. Shared files have the same direct references in this checkout.
        var referencesByPath = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
        foreach (var paths in inputs.Values)
        {
            var pending = new Stack<string>(paths);
            while (pending.TryPop(out var path))
            {
                if (!referencesByPath.TryGetValue(path, out var references))
                {
                    references = DirectReferences(root, path);
                    referencesByPath.Add(path, references);
                }
                foreach (var reference in references)
                    if (paths.Add(reference)) pending.Push(reference);
            }
        }
        return inputs;
    }

    static HashSet<string> DirectReferences(string root, string path)
    {
        // Registries name every fixture; including their types does not execute those fixtures.
        if (path is "scripts/ExportVerificationSuites.cs" or "scripts/VerificationSuites.cs") return [];
        var source = Path.Combine(root, path);
        if (!File.Exists(source)) return [];
        var text = File.ReadAllText(source);
        var references = new HashSet<string>(
            Matches(text, @"""((?:Tests|Examples)/[^""{}\n]+\.(?:cs|lean(?:\.in)?))"""), StringComparer.Ordinal);
        foreach (var pattern in Matches(text, @"""(Examples/Proofs/[^""\n]*\{[^""\n]+\.lean)"""))
        {
            var glob = Regex.Replace(pattern, @"\{[^}]+\}", "*");
            var matcher = new Regex(@"\A" + Regex.Escape(glob).Replace(@"\*", "[^/]*") + @"\z");
            foreach (var file in Directory.EnumerateFiles(Path.Combine(root, "Examples/Proofs"), "*.lean", SearchOption.AllDirectories))
            {
                var relative = Relative(root, file);
                if (matcher.IsMatch(relative)) references.Add(relative);
            }
        }
        references.UnionWith(Matches(text, @"^import\s+([\w.]+)", RegexOptions.Multiline)
            .Select(name => name.Replace('.', '/') + ".lean"));
        if (path.EndsWith(".cs", StringComparison.Ordinal) &&
            (path.StartsWith("Tests/", StringComparison.Ordinal) ||
                path.StartsWith("Examples/", StringComparison.Ordinal)))
        {
            references.UnionWith(Matches(text, @"^\s*import\s+((?:CIL|StrictBinding)(?:\.[\w]+)*)",
                    RegexOptions.Multiline)
                .Select(name => name.Replace('.', '/') + ".lean"));
        }
        references.UnionWith(Matches(text, @"""(Tests\.[\w.]+)""")
            .Select(name => name.Replace('.', '/') + ".lean"));
        foreach (var include in Matches(text, @"^#:include\s+(\S+)", RegexOptions.Multiline))
        {
            var relative = Relative(root, Path.GetFullPath(include, Path.GetDirectoryName(source)!));
            if (Path.IsPathRooted(relative) || relative == ".." || relative.StartsWith("../", StringComparison.Ordinal))
                throw new InvalidDataException("Source include escapes the repository: " + include);
            references.Add(relative);
        }
        return references;
    }

    // The docs suite runs the commands its documents mark `sh run`, so the example files they name are its inputs.
    static IEnumerable<string> WalkthroughInputs(string root) =>
        Documentation.Documents(root).SelectMany(path => Documentation.Read(root, path).Walkthrough)
            .Where(block => block.Kind is WalkthroughKind.Run or WalkthroughKind.RunFails)
            .SelectMany(block => Documentation.CommandLines(block))
            .SelectMany(entry => Matches(entry.Command, @"(Examples/[\w./-]+\.(?:lean|cs))"));

    // Modules reachable from the default `CIL` import, extracted files, the auditor or observation hooks.
    // Any other existing `.lean` module under `CIL/` is opt-in and only reaches suites that import it.
    static readonly string[] AmbientCilRoots =
    [
        "CIL.lean",
        "CIL/OleanAudit.lean", "CIL/Replay.lean",
        "CIL/Observe.lean", "CIL/Safety/FailureRecords.lean",
        "CIL/Crypto/Sha1.lean", "CIL/Crypto/Words.lean",
        "CIL/Runtime/ProgramEntry.lean", "CIL/Extraction/DecodedDefinition.lean",
        "CIL/SymbolicExecution.lean", "CIL/InstructionEquations.lean",
        "CIL/Safety/Execution.lean", "CIL/Safety/ResolutionFacts.lean", "CIL/Safety/ObjectFields.lean"
    ];

    static readonly HashSet<string> SimdIsaLeafModules = new(StringComparer.Ordinal)
    {
        "CIL/SIMD/AES.lean", "CIL/SIMD/AVX.lean", "CIL/SIMD/AVX2.lean", "CIL/SIMD/AVX512.lean",
        "CIL/SIMD/AVX512DQ.lean", "CIL/SIMD/AdvSimd.lean", "CIL/SIMD/ArmBase.lean",
        "CIL/SIMD/BMI1.lean", "CIL/SIMD/BMI2.lean", "CIL/SIMD/SSE.lean", "CIL/SIMD/X86Base.lean"
    };

    static readonly string[] SimdIsaSuites =
    [
        "core", "dispatch", "divrem", "docs", "evidence", "exportsprofiles",
        "gates", "intrinsics", "templates", "unsafe"
    ];

    static readonly string[] StrictBindingBaseSuites =
        ["assemblies", "audit", "cli", "core", "docs", "imports", "workspace"];

    // Isolated Extractor subsystems whose runtime behavior is scoped to specific suites. Every entry
    // includes `blockers` (self-admission scans every file compiled into Extractor) and `docs`.
    static readonly Dictionary<string, string[]> IsolatedExtractorSuites = new(StringComparer.Ordinal)
    {
        ["Extractor/ProofOutline.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ProofOutlineArrays.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ProofOutlineGenerate.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ProofOutlineLoops.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ProofOutlineObjects.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ProofOutlineScalar.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ProofOutlineSpanStores.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ProofOutlineStructLoops.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ProofOutlineStructs.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/OutlineInstructions.cs"] = ["blockers", "cli", "core", "docs", "loops", "outlines", "outlines-components"],
        ["Extractor/ExceptionLint.cs"] = ["blockers", "cli", "docs"],
        ["Extractor/Blockers.cs"] = ["blockers", "cli", "docs"],
        ["Extractor/TemplateEmitter.cs"] = ["blockers", "cli", "core", "docs", "gates", "pool", "templates"],
        ["Extractor/TemplateVectorFrames.cs"] = ["blockers", "cli", "core", "docs", "gates", "pool", "templates"],
        ["Extractor/ProofGates.cs"] = ["blockers", "cli", "core", "docs", "gates"],
        ["Extractor/ProofBindingCatalog.cs"] = ["blockers", "cli", "core", "docs", "gates"]
    };

    static readonly HashSet<string> IsolatedContractExportFiles = new(StringComparer.Ordinal)
    {
        "Extractor/ContractDependencyGraph.cs", "Extractor/ContractExportManifest.cs",
        "Extractor/ContractMethodMetadata.cs", "Extractor/ContractSourceBundle.cs",
        "Extractor/ExportInitialization.cs", "Extractor/ImportedLayoutMetadata.cs",
        "Extractor/ProfileContractExport.cs"
    };

    static HashSet<string> AmbientCilModules(string root)
    {
        var reachable = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Stack<string>();
        foreach (var entry in AmbientCilRoots)
            if (File.Exists(Path.Combine(root, entry)) && reachable.Add(entry)) pending.Push(entry);
        while (pending.TryPop(out var path))
        {
            var text = File.ReadAllText(Path.Combine(root, path));
            foreach (var module in Matches(text, @"^import\s+([\w.]+)", RegexOptions.Multiline))
            {
                var target = module.Replace('.', '/') + ".lean";
                if ((target == "CIL.lean" || target.StartsWith("CIL/", StringComparison.Ordinal)) &&
                    File.Exists(Path.Combine(root, target)) && reachable.Add(target))
                    pending.Push(target);
            }
        }
        return reachable;
    }

    static bool TrySelectScopedSubsystem(string root, string path,
        IReadOnlyDictionary<string, HashSet<string>> inputs, HashSet<string> manual,
        Lazy<HashSet<string>> ambientCil, Lazy<string[]> exportSuites, out string[] scoped)
    {
        if (SimdIsaLeafModules.Contains(path))
        {
            scoped = SimdIsaSuites;
            return true;
        }
        if (path.StartsWith("CIL/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal) &&
            File.Exists(Path.Combine(root, path)) && !ambientCil.Value.Contains(path))
        {
            var owners = inputs.Where(pair => !manual.Contains(pair.Key) && pair.Value.Contains(path))
                .Select(pair => pair.Key).ToArray();
            if (owners.Length == 0)
            {
                scoped = [];
                return false;
            }
            scoped = [.. owners, "docs"];
            return true;
        }
        if (path == "StrictBinding.lean" || path.StartsWith("StrictBinding/", StringComparison.Ordinal))
        {
            var owners = inputs.Where(pair => !manual.Contains(pair.Key) && pair.Value.Contains(path))
                .Select(pair => pair.Key);
            scoped = [.. StrictBindingBaseSuites, .. exportSuites.Value, .. owners];
            return true;
        }
        if (IsolatedExtractorSuites.TryGetValue(path, out var extractorSuites))
        {
            scoped = extractorSuites;
            return true;
        }
        if (IsolatedContractExportFiles.Contains(path))
        {
            scoped = ["blockers", "cli", "core", "docs", "evidence", "imports", .. exportSuites.Value];
            return true;
        }
        scoped = [];
        return false;
    }

    internal static string[] Select(IReadOnlyDictionary<string, HashSet<string>> inputs,
        IEnumerable<string> paths, string eventName = "pull_request", string? root = null)
    {
        root ??= Root;
        var manual = new HashSet<string>(VerificationSuites.ManualSuites, StringComparer.Ordinal);
        var all = inputs.Keys.Where(name => !manual.Contains(name)).Order(StringComparer.Ordinal).ToArray();
        if (eventName != "pull_request") return all;
        var ambientCil = new Lazy<HashSet<string>>(() => AmbientCilModules(root));
        var exportSuites = new Lazy<string[]>(() =>
            ExportVerificationSuites.Plan().Select(entry => entry.Name).ToArray());
        var selected = new HashSet<string>(StringComparer.Ordinal);
        foreach (var path in paths)
        {
            // Markdown that users read carries Lean snippets and library names that the docs suite checks.
            if (path.EndsWith(".md", StringComparison.Ordinal))
            {
                if (path == "README.md" || path.StartsWith("docs/", StringComparison.Ordinal) ||
                    path.StartsWith("skills/", StringComparison.Ordinal))
                    selected.Add("docs");
                continue;
            }
            if (path == "LICENSE") continue;
            // Other workflows run in their own jobs; only this workflow's definition feeds the suites.
            if (path.StartsWith(".github/workflows/", StringComparison.Ordinal) && path != ".github/workflows/verification.yml") continue;
            if (path is "scripts/ExportVerificationSuites.cs" or "scripts/VerificationSuites.cs") return all;
            if (TrySelectScopedSubsystem(root, path, inputs, manual, ambientCil, exportSuites, out var scoped))
            {
                selected.UnionWith(scoped.Where(name => inputs.ContainsKey(name) && !manual.Contains(name)));
                continue;
            }
            // A script compiled into the CLI reaches every suite through the built command, include edge or not.
            if (new[] { "CIL/", "Extractor/", "Examples/Assembly/", "Examples/FSharp/" }
                    .Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal)) ||
                path is "CIL.lean" or "Tests/Support.lean" ||
                path.StartsWith("scripts/", StringComparison.Ordinal) && inputs["blockers"].Contains(path))
                return all;
            var owners = inputs.Where(pair => pair.Value.Contains(path)).Select(pair => pair.Key).ToArray();
            if (owners.Length == 0) return all;
            selected.UnionWith(owners.Where(name => !manual.Contains(name)));
        }
        return selected.Order(StringComparer.Ordinal).ToArray();
    }
}
