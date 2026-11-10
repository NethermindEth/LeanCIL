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

    internal static Dictionary<string, double> ReadDurations(string? root = null)
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
        return durations;
    }

    internal static string[] Schedule(IEnumerable<string> suites, string? root = null)
    {
        var durations = ReadDurations(root);
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
    internal const int GroupMembers = 8;

    // A job is filled to the share of all measured time that one runner takes in one round, with the
    // fewest rounds that keep a job no longer than the longest suite. That suite then stays the
    // longest job, and every runner finishes its last job at about the same time.
    internal static double GroupSeconds(IReadOnlyDictionary<string, double> durations)
    {
        var rounds = 1;
        while (durations.Values.Sum() / (Runners * rounds) > durations.Values.Max()) rounds++;
        return durations.Values.Sum() / (Runners * rounds);
    }

    // A job's suites when few enough to read, else its longest suite and how many more it runs.
    static string Name(List<string> group) => group.Count <= 3 ? string.Join("+", group)
        : $"{group[0]}+{group.Count - 1}more";

    // Each job costs setup and restores before its first suite, so suites are packed into as few jobs
    // as the target allows, longest first into the fullest job that still has room. A suite without
    // a measured time runs alone.
    internal static Group[] Groups(IEnumerable<string> suites, string? root = null)
    {
        var durations = ReadDurations(root);
        var target = GroupSeconds(durations);
        double Seconds(List<string> group) =>
            group.Sum(name => durations.GetValueOrDefault(name, double.PositiveInfinity));
        var groups = new List<List<string>>();
        foreach (var suite in Schedule(suites.Distinct(StringComparer.Ordinal), root))
        {
            var seconds = durations.GetValueOrDefault(suite, double.PositiveInfinity);
            var group = groups.Where(group => group.Count < GroupMembers && Seconds(group) + seconds <= target)
                .OrderByDescending(Seconds).FirstOrDefault();
            if (group is null) groups.Add([suite]);
            else group.Add(suite);
        }
        var ordered = groups.OrderByDescending(Seconds).ToArray();
        // The shortest job carries the libraries: it starts last and has the most room before the
        // other jobs of its round finish.
        var carrier = ordered.LastOrDefault();
        return ordered.Select(group => new Group(Name(group), group.ToArray(),
                group.Max(name => name == "imports" ? 90 :
                    name.StartsWith("exports", StringComparison.Ordinal) ? 120 : 30),
                group.Any(VerificationSuites.ProofSuites.Contains), group == carrier)).ToArray();
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
            "Tests/MethodSelectors.cs", "Tests/MetadataMutator.cs", "Tests/Semantics.lean",
            "Tests/Automation.lean", "Tests/MethodBinding.lean", "Tests/MethodIdentity.lean",
            "Tests/StructuralLabels.lean", "Tests/DebugNames.lean", "Tests/MethodContract.lean",
            "Tests/ConstructContract.lean", "Tests/OutcomeContract.lean", "Tests/Imports.lean",
            "Tests/LoopOutcome.lean", "Tests/OutcomeEmbedding.lean", "Tests/MethodEmbedding.lean",
            "Tests/ConfinedFootprints.lean", "Tests/LocalSnapshots.lean", "Tests/ContractConsequence.lean",
            "Tests/InvocationCertificates.lean", "Tests/ValidCallTransport.lean",
            "Tests/BufferContents.lean", "Tests/Linking.lean", "Tests/StepFlow.lean", "Tests/RegionRun.lean",
            "Tests/StoreFacts.lean", "Tests/BatchVerification.cs", "Tests/VerificationCache.cs",
            "Tests/VerificationReuse.cs", "Tests/RuntimeExceptions.lean", "Tests/ProfileContract.lean",
            "Tests/InstructionEquations.lean", "Tests/CodeAt.lean", "Tests/SimdLanes.lean",
            "Tests/OperationFacts.lean", "Tests/VectorLocalCalls.lean", "Tests/SimdCarryCalls.lean",
            "Tests/OperationFactAdapters.lean", "Tests/AggregateMemorySteps.lean"
        };
        inputs["core"].UnionWith(new[] { "Add", "AddModel", "Choose", "Calls", "Alias", "Struct", "StructCopy",
            "LargeStruct", "PastEnd", "WrongAdd", "Escape", "Hardware", "StaticData" }.Select(name => $"Examples/Proofs/{name}.lean"));
        inputs["core"].Add("Tests/ModularStatics.lean");
        inputs["docs"].UnionWith(WalkthroughInputs(root));
        inputs["evidence"].UnionWith(new[] { "LayoutEvidence", "ParameterEvidence", "GenericEvidence", "FeatureEvidence", "TypeTests",
            "Throws", "SpanTables", "StaticValues", "StaticScalarValues", "TranslationAudit" }
            .Select(name => $"Tests/{name}.cs"));
        inputs["evidence"].UnionWith(new[] { "ExtractionLayout", "ExtractionParameters", "FeatureEvidence", "ScalarEvidence", "TypeTestEvidence",
            "ThrowEvidence", "SpanEvidence", "StaticValueEvidence", "LayoutCoverage", "ImportEvidence", "ImportedLayouts", "AssemblyPins" }.Select(name => $"Tests/{name}.lean"));
        inputs["imports"].UnionWith(["Tests/ContractClosure.lean", "Tests/ContractImports/Lib.leancil.contracts", "Tests/ContractImports/ImportFixture.lean", "Tests/ContractImports/Caller.lean",
            "Tests/ContractImports/Lib/Lib.csproj", "Tests/ContractImports/Lib/Library.cs", "Tests/ContractImports/App/App.csproj", "Tests/ContractImports/App/Application.cs"]);
        inputs["unsafe"].UnionWith(["Tests/SkipInitialization.cs", "Tests/NullReferences.cs"]);
        inputs["stepping"].Add("scripts/ProofCost.lean");
        // Self-admission scans the extractor itself, so every source compiled into it can change the result.
        inputs["blockers"].Add("Tests/SelfAdmissionBaseline.txt");
        inputs["blockers"].UnionWith(Matches(File.ReadAllText(Path.Combine(root, "Extractor/Extractor.csproj")),
            @"<Compile Include=""\.\./([^""]+\.cs)""").Select(path => path.Replace('\\', '/')));

        // Follow literal source paths, file-based includes and Lean imports.
        // Dynamic/new paths absent from this graph still fall back to the full matrix.
        foreach (var paths in inputs.Values)
        {
            var pending = new Stack<string>(paths);
            while (pending.TryPop(out var path))
            {
                if (path == "scripts/ExportVerificationSuites.cs") continue;
                var source = Path.Combine(root, path);
                if (!File.Exists(source)) continue;
                var text = File.ReadAllText(source);
                var references = new HashSet<string>(
                    Matches(text, @"""((?:Tests|Examples)/[^""{}\n]+\.(?:cs|lean))"""), StringComparer.Ordinal);
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
                references.UnionWith(Matches(text, @"""(Tests\.[\w.]+)""")
                    .Select(name => name.Replace('.', '/') + ".lean"));
                foreach (var include in Matches(text, @"^#:include\s+(\S+)", RegexOptions.Multiline))
                {
                    var relative = Relative(root, Path.GetFullPath(include, Path.GetDirectoryName(source)!));
                    if (Path.IsPathRooted(relative) || relative == ".." || relative.StartsWith("../", StringComparison.Ordinal))
                        throw new InvalidDataException("Source include escapes the repository: " + include);
                    references.Add(relative);
                }
                foreach (var reference in references)
                    if (paths.Add(reference)) pending.Push(reference);
            }
        }
        return inputs;
    }

    // The docs suite runs the commands its documents mark `sh run`, so the example files they name are its inputs.
    static IEnumerable<string> WalkthroughInputs(string root) =>
        Documentation.Documents(root).SelectMany(path => Documentation.Read(root, path).Walkthrough)
            .Where(block => block.Kind is WalkthroughKind.Run or WalkthroughKind.RunFails)
            .SelectMany(block => Documentation.CommandLines(block))
            .SelectMany(entry => Matches(entry.Command, @"(Examples/[\w./-]+\.(?:lean|cs))"));

    internal static string[] Select(IEnumerable<string> paths, string eventName = "pull_request", string? root = null)
    {
        var inputs = SuiteInputs(root);
        var all = inputs.Keys.Order(StringComparer.Ordinal).ToArray();
        if (eventName != "pull_request") return all;
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
            if (path == "scripts/ExportVerificationSuites.cs") return all;
            // A script compiled into the CLI reaches every suite through the built command, include edge or not.
            if (new[] { "CIL/", "Extractor/", "Examples/Assembly/", "Examples/FSharp/" }
                    .Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal)) || path == "Tests/Support.lean" ||
                path.StartsWith("scripts/", StringComparison.Ordinal) && inputs["blockers"].Contains(path))
                return all;
            var owners = inputs.Where(pair => pair.Value.Contains(path)).Select(pair => pair.Key).ToArray();
            if (owners.Length == 0) return all;
            selected.UnionWith(owners);
        }
        return selected.Order(StringComparer.Ordinal).ToArray();
    }
}
