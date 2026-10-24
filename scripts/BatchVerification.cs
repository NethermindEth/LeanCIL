using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

partial class Program
{
    // Only generated, namespace-relative fixtures belong here. Arbitrary consumer
    // proofs keep their original module environment through Verify.
    // Assembly overrides the batch assembly for fixtures generated from a modified copy.
    sealed record GeneratedVerification(string Entry, string Proof, string Output,
        string Theorem = "ExampleProof.correctness", string? Assembly = null);

    // Per-fixture checks are dominated by Lean startup; passes are reported only after the whole batch is certified.
    sealed class GeneratedQueue(Program verification, string assembly, string identity = "Examples")
    {
        readonly List<(GeneratedVerification Request, Action Passed)> pending = [];

        public void Add(GeneratedVerification request, Action passed) => pending.Add((request, passed));

        public void Flush()
        {
            if (pending.Count == 0) return;
            verification.VerifyGeneratedBatch(assembly, identity, pending.Select(item => item.Request).ToArray());
            foreach (var (_, passed) in pending) passed();
            pending.Clear();
        }
    }

    void VerifyGeneratedBatch(string assembly, string identity, IReadOnlyList<GeneratedVerification> requests,
        string profile = "scalar")
    {
        if (requests.Count == 0) return;
        assembly = Path.GetFullPath(assembly);
        requests = requests.Select(r => r with { Proof = Path.GetFullPath(r.Proof), Output = Path.GetFullPath(r.Output),
            Assembly = Path.GetFullPath(r.Assembly ?? assembly) }).ToArray();
        if (requests.Select(r => Path.GetFullPath(r.Output)).Distinct(StringComparer.OrdinalIgnoreCase).Count() != requests.Count)
            throw new ArgumentException("Batch outputs must be distinct");
        foreach (var request in requests)
        {
            if (!Regex.IsMatch(request.Theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
                throw new ArgumentException("Invalid theorem name");
            Directory.CreateDirectory(request.Output);
            File.Delete(Path.Combine(request.Output, "verified.json"));
        }
        if (!extractorBuilt)
        {
            Run(["dotnet", "build", "Extractor", "-c", "Release",
                "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
            extractorBuilt = true;
        }
        var commonBefore = CommonInputs();
        var before = requests.Select(r => Inputs(commonBefore, r.Proof)).ToArray();
        var session = Library(before[0]);
        var imports = new SortedSet<string>(StringComparer.Ordinal);
        string Body(string source)
        {
            return Regex.Replace(source, @"^import[ \t]+([A-Za-z_][A-Za-z0-9_.]*)[ \t]*\r?$", match =>
            {
                var module = match.Groups[1].Value;
                if (module is not ("Extracted" or "ExtractedSymbols")) imports.Add(module);
                return "";
            }, RegexOptions.Multiline);
        }
        var bodies = new StringBuilder();
        var hashes = new string[requests.Count];
        for (var i = 0; i < requests.Count; i++)
        {
            var request = requests[i];
            Run(Extract("extract", request.Assembly!, identity, request.Entry, request.Output, profile));
            if (HasContractImports(ExtractionIdentity.Read(request.Output)))
                throw new InvalidDataException("Generated batch verification does not support contract imports.");
            hashes[i] = Sha(Path.Combine(request.Output, "identity.json"));
            bodies.AppendLine($"namespace BatchCase{i}");
            bodies.AppendLine(Body(File.ReadAllText(Path.Combine(request.Output, "Extracted.lean"))));
            var proofSource = File.ReadAllText(request.Proof);
            if (ImportsSymbols(proofSource)) bodies.AppendLine(File.ReadAllText(SymbolsFor(request.Output)));
            bodies.AppendLine(Body(proofSource));
            bodies.AppendLine($"end BatchCase{i}");
        }
        var support = imports.Where(n => n.Split('.')[0] is not ("Init" or "Lean" or "Std")).ToArray();
        if (support.Length > 0)
            Run(["lake", "build", .. support], session, progress: "Building generated batch dependencies");
        var currentModules = ModuleArtifacts(session);
        var certified = certifiedModules!;
        var altered = certified.Any(pair => !currentModules.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
        var changed = (altered ? currentModules.Keys : currentModules.Keys.Where(name => !certified.ContainsKey(name)))
            .Select(ModuleName).Distinct().ToArray();
        var checker = Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
        var fresh = Path.Combine(Path.GetTempPath(), "leancil-batch-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(fresh);
        try
        {
            var leanPath = fresh + Path.PathSeparator + Path.Combine(session, ".lake/build/lib/lean");
            if (changed.Length > 0)
            {
                Run([checker, .. changed], leanPath: leanPath, progress: "Kernel replay of generated batch dependencies");
                certifiedModules = currentModules;
            }
            var batchSource = string.Join("\n", imports.Select(n => "import " + n)) + "\n" + bodies;
            var source = Path.Combine(fresh, "Batch.lean");
            File.WriteAllText(source, batchSource);
            // Building the batch runs its proofs' code; the library must survive it unchanged.
            var bound = OleanHashes(fresh, session);
            Run(["lean", "--root=" + fresh, "-o", Path.Combine(fresh, "Batch.olean"), source],
                leanPath: leanPath, progress: $"Checking {requests.Count} generated fixtures");
            var built = OleanHashes(fresh, session);
            RequireOnlyAdded(bound, built, "Batch");
            Run([checker, "Batch"], leanPath: leanPath, progress: $"Kernel replay of {requests.Count} generated fixtures");
            var audited = AuditOleans(leanPath, ["Batch"], [.. Enumerable.Range(0, requests.Count).SelectMany(i => new[] {
                ProofTheorem($"BatchCase{i}.{requests[i].Theorem}"),
                ExtractionCertificate($"BatchCase{i}.Extracted.translation_valid", $"BatchCase{i}.") })]);
            if (!Same(built, OleanHashes(fresh, session)))
                throw new InvalidOperationException("Compiled artifacts changed during verification");
            RequireAuditedModule(audited, "Batch", Path.Combine(fresh, "Batch.olean"));
            foreach (var request in requests)
                Run(Extract("check", request.Assembly!, identity, request.Entry, request.Output, profile));
            // Every input is checked after the last subprocess, including inputs for earlier fixtures.
            var commonAfter = CommonInputs();
            var reports = new Report[requests.Count];
            for (var i = 0; i < requests.Count; i++)
            {
                var request = requests[i];
                var theorem = $"BatchCase{i}.{request.Theorem}";
                var axioms = AuditedAxioms(audited.theorems[2 * i]);
                AuditedAxioms(audited.theorems[2 * i + 1]);
                if (!Same(before[i], Inputs(commonAfter, request.Proof)) ||
                    hashes[i] != Sha(Path.Combine(request.Output, "identity.json")))
                    throw new InvalidOperationException("Batch inputs changed during verification");
                var extraction = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(request.Output, "identity.json")));
                var initializedTypes = extraction.TryGetProperty("initializedTypes", out var assumptions)
                    ? assumptions.Deserialize<string[]>() : [];
                reports[i] = new Report(4, Sha(request.Assembly!), hashes[i], request.Theorem, axioms, AuditText(audited.theorems[2 * i]), before[i],
                    libraryKey, libraryBuild, AuditText(audited.theorems[2 * i + 1]), initializedTypes, Sha(source), theorem,
                    staticValues: StaticValueAssumptions(extraction), imports: PublishedImports(extraction),
                    contractDependencies: DeploymentDependencies(extraction));
            }
            // Nothing is published until every fixture, certificate and replay passes.
            for (var i = 0; i < requests.Count; i++)
            {
                File.Copy(source, Path.Combine(requests[i].Output, "Batch.lean"), overwrite: true);
                File.WriteAllText(Path.Combine(requests[i].Output, "verified.json"), JsonSerializer.Serialize(reports[i], Json) + "\n");
            }
        }
        finally
        {
            Directory.Delete(fresh, recursive: true);
        }
    }
}
