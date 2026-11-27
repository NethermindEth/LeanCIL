#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/ProofCostReport.cs
#:include ../scripts/CertifiedLibraryDonor.cs
#:include ../scripts/ExportVerificationSuites.cs
#:include ../scripts/VerificationGroupRunner.cs
#:include ../scripts/VerificationSuites.cs

using System.Text.Json;

// Failed imports and earlier commands must not publish a successful measurement.
var directory = At("artifacts/ProofCostFrontend");
Directory.CreateDirectory(directory);
var tooling = Path.Combine(directory, "scripts");
Directory.CreateDirectory(tooling);
var compile = Execute(["lake", "env", "lean", "-o", Path.Combine(tooling, "ProofCost.olean"),
    At("scripts/ProofCost.lean")]);
if (compile.Code != 0) throw new InvalidOperationException(compile.Output);
var discovery = Execute(["lake", "env", "lean", At("Tests/ProofCostDiscovery.lean")], leanPath: directory);
if (discovery.Code != 0) throw new InvalidOperationException(discovery.Output);
Console.WriteLine(discovery.Output);
var fixtures = new (string Name, string? Error, string Source)[]
{
    ("ValidCostImport", null, """
        import Lean

        theorem measured : True := True.intro
        #print axioms measured

        theorem auxiliary (value : Nat) : value = value := by
          as_aux_lemma => rfl
        #print axioms auxiliary

        theorem subsequent : True := True.intro
        #print axioms subsequent

        private theorem hidden : True := True.intro
        #print axioms hidden

        example : True := True.intro

        structure MeasuredPair where
          left : Nat
          right : Nat

        /-- error: expected cost diagnostic -/
        #guard_msgs in
        run_cmd Lean.logError "expected cost diagnostic"
        """),
    ("MissingCostImport", "ProofCostMissingImport", """
        import Lean
        import ProofCostMissingImport

        #guard_msgs in
        example : True := by trivial
        """),
    ("RejectedCostProof", "Type mismatch", """
        import Lean

        theorem rejected : False := by
          as_aux_lemma => exact True.intro

        theorem subsequent : True := True.intro
        #print axioms subsequent
        """),
    ("MalformedCostProof", "unexpected token", """
        import Lean

        theorem malformed : True := by
          exact )

        theorem subsequent : True := True.intro
        #print axioms subsequent
        """),
    ("TimedOutCostProof", "maximum number of heartbeats", """
        import Lean

        set_option maxHeartbeats 1 in
        theorem timedOut (value : Nat) : value = value := by
          as_aux_lemma => rfl

        theorem subsequent : True := True.intro
        #print axioms subsequent
        """)
};
foreach (var (name, error, contents) in fixtures)
{
    var source = Path.Combine(directory, name + ".lean");
    var report = Path.Combine(directory, name + ".json");
    var compiled = Path.Combine(directory, name + ".olean");
    File.WriteAllText(source, contents);
    File.Delete(report);
    File.Delete(compiled);
    var result = Execute(["lake", "env", "lean", "--run", At("scripts/ProofCost.lean"),
        name, source, report, compiled]);
    if (error is not null)
    {
        if (result.Code == 0 || !result.Output.Contains(error, StringComparison.Ordinal) ||
            File.Exists(report) || File.Exists(compiled))
            throw new InvalidOperationException(name + " produced a measurement:\n" + result.Output);
    }
    else
    {
        if (result.Code != 0 || !File.Exists(compiled))
            throw new InvalidOperationException("A valid proof was not measured:\n" + result.Output);
        using var measured = JsonDocument.Parse(File.ReadAllText(report));
        var commands = measured.RootElement.GetProperty("commands").EnumerateArray().ToArray();
        foreach (var (label, constants) in new[]
                 { ("measured", 1), ("auxiliary", 2), ("subsequent", 1), ("hidden", 1) })
        {
            var command = commands.Single(command => command.GetProperty("label").GetString() == label);
            if (command.GetProperty("constants").GetInt32() != constants ||
                command.GetProperty("proofObjects").GetInt64() <= 0 ||
                command.GetProperty("kernelHeartbeats").GetInt64() <= 0)
                throw new InvalidOperationException("Missing theorem measurement: " + label);
        }
        if (commands.Count(command => command.GetProperty("kind").GetString() == "example") != 1 ||
            commands.Single(command => command.GetProperty("label").GetString() == "MeasuredPair")
                .GetProperty("constants").GetInt32() < 3)
            throw new InvalidOperationException("Examples or generated structure declarations were lost.");
        if (commands.Where(command => command.GetProperty("kind").GetString() == "command")
            .Any(command => command.GetProperty("constants").GetInt32() != 0))
            throw new InvalidOperationException("A diagnostic command counted declarations again.");
    }
}
Console.WriteLine("PASS cost measurement includes auxiliary proofs and rejects failed imports and commands");

// Eight importers must await the compiled dependency and publish exactly one row per module.
var tree = Path.Combine(directory, "Scheduling");
var library = Path.Combine(tree, "library");
Directory.CreateDirectory(library);
File.WriteAllText(Path.Combine(library, "CIL.olean"), "unused library marker");
File.WriteAllText(Path.Combine(tree, "Shared.lean"), """
    import Lean
    theorem shared : True := True.intro
    #print axioms shared
    """);
var modules = Enumerable.Range(0, 8).Select(index => "Importer" + index).ToArray();
foreach (var module in modules)
    File.WriteAllText(Path.Combine(tree, module + ".lean"), $$"""
        import Shared
        theorem {{module}} : True := shared
        #print axioms {{module}}
        """);
ProofCostReport.Measurement? serial = null;
foreach (var jobs in new[] { 1, 8, 8 })
{
    var measurement = ProofCostReport.Measure(tree, library, Path.Combine(tree, "work" + jobs),
        false, [], modules, jobs, "shared imports");
    if (measurement.Unmeasured.Count != 0)
        throw new InvalidOperationException(string.Join(Environment.NewLine, measurement.Unmeasured));
    var measured = measurement.Rows.Where(row => row.Kind == ProofCostReport.ModuleKind).ToArray();
    if (measured.Length != modules.Length + 1 ||
        measured.Select(row => row.Group).Distinct().Count() != measured.Length)
        throw new InvalidOperationException("Shared imports produced duplicate or missing modules.");
    serial ??= measurement;
    if (serial.Rows.Count != measurement.Rows.Count || serial.Rows.Zip(measurement.Rows).Any(pair =>
        pair.First.Group != pair.Second.Group || pair.First.Name != pair.Second.Name ||
        pair.First.Measures.Any(metric => metric.Key switch
        {
            "elapsedMs" or "kernelMs" => false,
            "heartbeats" => Math.Abs(metric.Value - pair.Second.Measures[metric.Key]) > 1_000,
            _ => metric.Value != pair.Second.Measures[metric.Key]
        })))
        throw new InvalidOperationException("Parallel measurement changed the measured costs.");
    Console.WriteLine($"PASS {jobs} jobs measured each of {measured.Length} modules once with matching costs");
}
File.WriteAllText(Path.Combine(tree, "Left.lean"), "import Right");
File.WriteAllText(Path.Combine(tree, "Right.lean"), "import Left");
var cycle = ProofCostReport.Measure(tree, library, Path.Combine(tree, "cycle"),
    false, [], ["Left", "Right"], 8, "cyclic imports");
if (cycle.Rows.Count != 0 || cycle.Unmeasured.Count != 2 ||
    cycle.Unmeasured.Any(row => !row.Reason.Contains("import cycle", StringComparison.Ordinal)))
    throw new InvalidOperationException("Cyclic imports did not produce a bounded failure.");
Console.WriteLine("PASS cyclic imports are rejected before measurement");

// A stale digest discards only its consumer proof. Other proofs and extractions remain measurable.
var receipts = Path.GetFullPath(Path.Combine(tree, "CertifiedProofs"));
foreach (string group in new[] { "Valid", "ChangedSettings", "ChangedConfig" })
{
    var output = Path.Combine(receipts, group);
    Directory.CreateDirectory(output);
    File.WriteAllText(Path.Combine(output, "Extracted.lean"), "def value := true\n");
    var proof = Path.Combine(output, "ConsumerProof.lean");
    File.WriteAllText(proof, "import Extracted\ntheorem verified : value = true := rfl\n#print axioms verified\n");
    var settings = Path.Combine(output, "verification.json");
    var config = Path.Combine(output, "lakefile.toml");
    File.WriteAllText(settings, """{"proofRoot":"."}""");
    File.WriteAllText(config, "name = \"proof_cost_fixture\"\n");
    var inputs = new SortedDictionary<string, string>(StringComparer.Ordinal)
    {
        ["proof:" + proof] = Sha(proof),
        ["settings:" + settings] = Sha(settings),
        ["consumer:" + config] = Sha(config)
    };
    var certificate = new Report(CertificateSchema, "assembly", "identity", "verified",
        [], "audit", inputs, BindingSection.Default);
    File.WriteAllText(Path.Combine(output, "verified.json"), JsonSerializer.Serialize(certificate));
    if (group == "ChangedSettings") File.AppendAllText(settings, "\n");
    if (group == "ChangedConfig") File.AppendAllText(config, "\n");
}
var mixed = ProofCostReport.Measure(tree, library, Path.Combine(tree, "mixed"), false, [receipts], [], 2, "receipts");
var expectedFailures = new[]
{
    new ProofCostReport.Unmeasured("ChangedSettings/Proof", "verification settings changed after verification"),
    new ProofCostReport.Unmeasured("ChangedConfig/Proof", "consumer configuration changed after verification: " +
        Path.Combine(receipts, "ChangedConfig", "lakefile.toml"))
};
var proofGroups = mixed.Rows.Where(row => row.Group.EndsWith("/Proof", StringComparison.Ordinal))
    .Select(row => row.Group).Distinct().ToArray();
if (mixed.Unmeasured.Count != 2 || !expectedFailures.All(mixed.Unmeasured.Contains) ||
    proofGroups is not ["Valid/Proof"] ||
    mixed.Rows.Count(row => row.Kind == ProofCostReport.ModuleKind &&
        row.Group.EndsWith("/Extracted", StringComparison.Ordinal)) != 3)
    throw new InvalidOperationException("Stale consumer settings or configuration lost the wrong proof rows: " +
        JsonSerializer.Serialize(mixed.Unmeasured));
Console.WriteLine("PASS stale consumer settings and configuration withhold only their own proof rows");
