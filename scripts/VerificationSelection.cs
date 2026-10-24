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

    internal static Dictionary<string, HashSet<string>> SuiteInputs(string? root = null)
    {
        root ??= Root;
        var runner = File.ReadAllText(Path.Combine(root, "scripts/Test.cs"));
        var inputs = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
        foreach (Match match in Regex.Matches(runner, @"\[""([a-z]+)""\] = \(""(Tests/[^""\n]+\.cs)"""))
            inputs[match.Groups[1].Value] = new(StringComparer.Ordinal) { match.Groups[2].Value };
        if (!inputs.ContainsKey("unsafe")) throw new InvalidDataException("Could not read verification suite registry");
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
            "Tests/Automation.lean", "Tests/MethodBinding.lean", "Tests/MethodIdentity.lean", "Tests/StructuralLabels.lean", "Tests/DebugNames.lean", "Tests/MethodContract.lean", "Tests/ConstructContract.lean", "Tests/OutcomeContract.lean", "Tests/Imports.lean", "Tests/LoopOutcome.lean", "Tests/OutcomeEmbedding.lean", "Tests/MethodEmbedding.lean", "Tests/ConfinedFootprints.lean", "Tests/LocalSnapshots.lean", "Tests/ContractConsequence.lean", "Tests/BufferContents.lean", "Tests/Linking.lean", "Tests/StepFlow.lean", "Tests/RegionRun.lean", "Tests/StoreFacts.lean", "Tests/BatchVerification.cs", "Tests/VerificationCache.cs",
            "Tests/VerificationReuse.cs", "Tests/RuntimeExceptions.lean"
        };
        inputs["core"].UnionWith(new[] { "Add", "Choose", "Calls", "Alias", "Struct", "StructCopy", "LargeStruct",
            "PastEnd", "WrongAdd", "Escape", "Hardware", "StaticData" }.Select(name => $"Examples/Proofs/{name}.lean"));
        inputs["core"].Add("Tests/ModularStatics.lean");
        inputs["evidence"].UnionWith(new[] { "LayoutEvidence", "ParameterEvidence", "GenericEvidence", "FeatureEvidence", "TypeTests",
            "Throws", "SpanTables", "StaticValues", "TranslationAudit" }.Select(name => $"Tests/{name}.cs"));
        inputs["evidence"].UnionWith(new[] { "ExtractionLayout", "ExtractionParameters", "FeatureEvidence", "ScalarEvidence", "TypeTestEvidence",
            "ThrowEvidence", "SpanEvidence", "StaticValueEvidence", "LayoutCoverage", "ImportEvidence", "ImportedLayouts" }.Select(name => $"Tests/{name}.lean"));
        inputs["imports"].UnionWith(["Tests/ContractClosure.lean", "Tests/ContractImports/Lib.leancil.contracts", "Tests/ContractImports/ImportFixture.lean", "Tests/ContractImports/Caller.lean",
            "Tests/ContractImports/Lib/Lib.csproj", "Tests/ContractImports/Lib/Library.cs", "Tests/ContractImports/App/App.csproj", "Tests/ContractImports/App/Application.cs"]);
        inputs["unsafe"].UnionWith(["Tests/SkipInitialization.cs", "Tests/NullReferences.cs"]);

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

    internal static string[] Select(IEnumerable<string> paths, string eventName = "pull_request", string? root = null)
    {
        var inputs = SuiteInputs(root);
        var all = inputs.Keys.Order(StringComparer.Ordinal).ToArray();
        if (eventName != "pull_request") return all;
        var selected = new HashSet<string>(StringComparer.Ordinal);
        foreach (var path in paths)
        {
            if (path.EndsWith(".md", StringComparison.Ordinal) || path == "LICENSE") continue;
            // Other workflows run in their own jobs; only this workflow's definition feeds the suites.
            if (path.StartsWith(".github/workflows/", StringComparison.Ordinal) && path != ".github/workflows/verification.yml") continue;
            if (path == "scripts/ExportVerificationSuites.cs") return all;
            if (new[] { "CIL/", "Extractor/", "Examples/Assembly/", "Examples/FSharp/" }
                    .Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal)) || path == "Examples/Support.lean")
                return all;
            var owners = inputs.Where(pair => pair.Value.Contains(path)).Select(pair => pair.Key).ToArray();
            if (owners.Length == 0) return all;
            selected.UnionWith(owners);
        }
        return selected.Order(StringComparer.Ordinal).ToArray();
    }
}
