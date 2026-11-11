#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Text.Json;

const double WorkGrowthLimit = 1.35;
const double TimeGrowthLimit = 2.0;
const int Repetitions = 3;

ScalingChecks();
if (args is ["--self-test"])
{
    return;
}
var package = args switch
{
    [] => FixturePackage(),
    ["--package", var path] => Path.GetFullPath(path),
    _ => throw new ArgumentException("Usage: SteppingScaling.cs [--package <compiled checkout>] | --self-test")
};
var directory = At("artifacts/SteppingScaling");
Directory.CreateDirectory(directory);
var reportPath = Path.Combine(directory, "results.json");
File.Delete(reportPath);
var sourcePatch = Run(["git", "diff", "HEAD", "--binary"]);
File.WriteAllText(Path.Combine(directory, "source.patch"), sourcePatch);
File.Copy(At("Tests/SteppingScaling.cs"), Path.Combine(directory, "Runner.cs"), overwrite: true);
var rows = new List<SteppingMeasurement>();
foreach (var workload in new[] { "scalar", "memory" })
    foreach (var requested in new[] { 16, 64, 256 })
        rows.Add(Measure(workload, requested));

var report = new
{
    Schema = 1,
    Revision = Run(["git", "rev-parse", "HEAD"]).Trim(),
    SourceStatus = Run(["git", "status", "--porcelain", "--untracked-files=no"]).Trim(),
    SourcePatchSha256 = Sha(Path.Combine(directory, "source.patch")),
    RunnerSha256 = Sha(Path.Combine(directory, "Runner.cs")),
    LibraryPackage = package,
    Toolchain = File.ReadAllText(At("lean-toolchain")).Trim(),
    Machine = new { RuntimeInformation.OSDescription, RuntimeInformation.ProcessArchitecture,
        Runtime = RuntimeInformation.FrameworkDescription, Environment.ProcessorCount },
    Concurrency = 1,
    Repetitions,
    CacheState = "Compiled library; fresh generated proof modules; OS caches unspecified",
    TimingIsolation = "External machine load is not controlled; wall times are observations",
    Measurement = "Frontend includes its initial kernel check; kernel columns are separate rechecks. " +
        "Module command time excludes imports. Compiled proof bytes subtract the same body without its proof.",
    Budgets = new { WorkGrowthLimit, TimeGrowthLimit },
    Rows = rows
};
File.WriteAllText(reportPath,
    JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }) + "\n");
foreach (var workload in rows.GroupBy(row => row.Workload))
{
    var measurements = workload.OrderBy(row => row.Instructions).ToArray();
    for (var index = 1; index < measurements.Length; index++)
        CheckGrowth(measurements[index - 1], measurements[index]);
}
Console.WriteLine("PASS scalar and memory stepping growth budgets; results: " + reportPath);

SteppingMeasurement Measure(string workload, int requested)
{
    var memory = workload == "memory";
    string[] cycle = memory
        ? [".arg 0", ".arg 1", ".store64", ".arg 0", ".load64", ".pop"]
        : [".arg 0", ".arg 1", ".add", ".pop"];
    string[] ending = memory ? [".arg 0", ".load64", ".ret"] : [".arg 0", ".ret"];
    var cycles = Math.Max(1, (requested - ending.Length) / cycle.Length);
    var operations = Enumerable.Range(0, cycles).SelectMany(_ => cycle).Concat(ending).ToArray();
    var module = "Stepping" + workload + requested;
    var path = Path.Combine(directory, module + ".lean");
    var header = $$"""
        import CIL.InstructionEquations
        import CIL.Safety.LoopFrames
        open CIL.Safety
        set_option maxRecDepth 8192
        set_option maxHeartbeats 800000
        /-- A synthetic body in the emitter's explicit instruction-list shape. -/
        def body : CIL.Method := {
          locals := [], returnsValue := true,
          code := [{{string.Join(",\n    ", operations)}}] }
        cil_instruction_equations body
        """ + "\n";
    var statement = memory
        ? $$"""
            /-- Checked reads and writes advance from reusable operation facts through the full body. -/
            theorem checked (memory : Memory) (target : Reference) (word : CIL.W64)
                (loaded : read memory target 8 1 = .ok (numberBytes word.toNat 8))
                (written : write memory target (numberBytes word.toNat 8) 1 = .ok memory) :
                invoke [body] {{operations.Length + 1}} 0
                  [.reference (.address target), .scalar (.i64 word)] memory =
                  .ok (memory, [.scalar (.i64 word)]) := by
              have formed := access_reference_valid _ _ _ _ _ (read_access loaded)
              have loadFact := load_word64_of_read loaded
              have storeFact := step_store64_of_write written
              cil_checked_steps [formed, loadFact, storeFact]
            """
        : $$"""
            /-- All scalar instructions execute and return the original first operand. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                invoke [body] {{operations.Length + 1}} 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory =
                  .ok (memory, [.scalar (.i64 left)]) := by
              cil_checked_steps
            """;
    const string Audit = """

        /-- info: 'checked' depends on axioms: [propext, Quot.sound] -/
        #guard_msgs (whitespace := lax) in
        #print axioms checked
        """;
    File.WriteAllText(path, header);
    var baseline = Compile(module, path, "header");
    File.WriteAllText(path, header + statement + "\n" + Audit + "\n");
    var samples = Enumerable.Range(0, Repetitions).Select(index => Compile(module, path, "proof" + index)).ToArray();
    var commands = samples.Select(sample => sample.Commands.Single(command => command.Label == "checked")).ToArray();
    if (commands.Select(command => command.Heartbeats).Distinct().Count() != 1 ||
        commands.Select(command => command.KernelHeartbeats).Distinct().Count() != 1 ||
        samples.Select(sample => sample.Bytes).Distinct().Count() != 1)
        throw new InvalidOperationException("Stepping work did not repeat exactly for " + module);
    var proofBytes = samples[0].Bytes - baseline.Bytes;
    if (proofBytes <= 0) throw new InvalidOperationException("Missing compiled proof bytes for " + module);
    var row = new SteppingMeasurement(workload, operations.Length, cycles, memory ? 2 * cycles + 1 : 0,
        commands[0].Heartbeats, commands[0].KernelHeartbeats, proofBytes,
        Median(commands.Select(command => command.ElapsedMs)), Median(commands.Select(command => command.KernelMs)),
        Median(samples.Select(sample => sample.Commands.Sum(command => command.ElapsedMs))),
        samples.Select(sample => sample.ProcessMs).ToArray(), baseline.ProcessMs)
    {
        CompiledModuleBytes = samples[0].Bytes,
        HeaderModuleBytes = baseline.Bytes,
        HeaderCommandsMs = baseline.Commands.Sum(command => command.ElapsedMs),
        SourceSha256 = Sha(path)
    };
    Console.WriteLine(string.Create(System.Globalization.CultureInfo.InvariantCulture, 
        $"{workload} {row.Instructions} instructions: {row.FrontendHeartbeatsPerInstruction:F0} frontend HB, " +
        $"{row.KernelHeartbeatsPerInstruction:F0} kernel HB, {row.ProofBytesPerInstruction:F0} proof bytes, " +
        $"{row.FrontendMsPerInstruction:F2} frontend ms per instruction"));
    return row;
}

CompiledSample Compile(string module, string source, string suffix)
{
    var report = Path.Combine(directory, module + "." + suffix + ".json");
    var compiled = Path.Combine(directory, module + "." + suffix + ".olean");
    var timer = Stopwatch.StartNew();
    Run(["lake", "env", "lean", "--run", At("scripts/ProofCost.lean"), module, source, report, compiled], cwd: package);
    timer.Stop();
    using var document = JsonDocument.Parse(File.ReadAllText(report));
    var commands = document.RootElement.GetProperty("commands").EnumerateArray().Select(command => new CommandSample(
        command.GetProperty("label").GetString()!, command.GetProperty("heartbeats").GetInt64(),
        command.GetProperty("kernelHeartbeats").GetInt64(), command.GetProperty("elapsedMs").GetInt64(),
        command.GetProperty("kernelMs").GetInt64())).ToArray();
    return new(commands, new FileInfo(compiled).Length, timer.ElapsedMilliseconds);
}

static long Median(IEnumerable<long> values)
{
    var sorted = values.Order().ToArray();
    return sorted[sorted.Length / 2];
}

static void CheckGrowth(SteppingMeasurement shorter, SteppingMeasurement longer)
{
    Check("frontend heartbeats", shorter.FrontendHeartbeatsPerInstruction,
        longer.FrontendHeartbeatsPerInstruction, WorkGrowthLimit);
    Check("kernel heartbeats", shorter.KernelHeartbeatsPerInstruction,
        longer.KernelHeartbeatsPerInstruction, WorkGrowthLimit);
    Check("compiled proof bytes", shorter.ProofBytesPerInstruction,
        longer.ProofBytesPerInstruction, WorkGrowthLimit);
    Check("frontend milliseconds", shorter.FrontendMsPerInstruction,
        longer.FrontendMsPerInstruction, TimeGrowthLimit);

    void Check(string metric, double before, double after, double budget)
    {
        if (before <= 0 || after / before > budget)
            throw new InvalidOperationException(string.Create(System.Globalization.CultureInfo.InvariantCulture, 
                $"{longer.Workload} {metric}/instruction grew from {before:F3} to {after:F3} " +
                $"between {shorter.Instructions} and {longer.Instructions} instructions; budget {budget:F2}."));
    }
}

static void ScalingChecks()
{
    var baseline = new SteppingMeasurement("test", 16, 4, 0,
        16000, 1600, 32000, 160, 16, 200, [], 1);
    var linear = baseline with { Instructions = 64, FrontendHeartbeats = 64000, KernelHeartbeats = 6400,
        ProofBytes = 128000, FrontendMs = 640 };
    CheckGrowth(baseline, linear);
    foreach (var mutant in new[] { linear with { FrontendHeartbeats = 256000 },
        linear with { KernelHeartbeats = 25600 }, linear with { ProofBytes = 512000 },
        linear with { FrontendMs = 2560 } })
    {
        try { CheckGrowth(baseline, mutant); }
        catch (InvalidOperationException) { continue; }
        throw new InvalidOperationException("Scaling budget accepted a quadratic work mutant.");
    }
    Console.WriteLine("PASS stepping budgets accept linear work and reject each quadratic metric");
}

internal sealed record CommandSample(string Label, long Heartbeats, long KernelHeartbeats,
    long ElapsedMs, long KernelMs);
internal sealed record CompiledSample(CommandSample[] Commands, long Bytes, long ProcessMs);
internal sealed record SteppingMeasurement(string Workload, int Instructions, int Cycles, int MemoryOperations,
    long FrontendHeartbeats, long KernelHeartbeats, long ProofBytes, long FrontendMs, long KernelMs,
    long ModuleCommandsMs, long[] ProcessMs, long HeaderProcessMs)
{
    public long CompiledModuleBytes { get; init; }
    public long HeaderModuleBytes { get; init; }
    public long HeaderCommandsMs { get; init; }
    public string SourceSha256 { get; init; } = "";
    public double FrontendHeartbeatsPerInstruction => (double)FrontendHeartbeats / Instructions;
    public double KernelHeartbeatsPerInstruction => (double)KernelHeartbeats / Instructions;
    public double ProofBytesPerInstruction => (double)ProofBytes / Instructions;
    public double FrontendMsPerInstruction => (double)FrontendMs / Instructions;
    public double KernelMsPerInstruction => (double)KernelMs / Instructions;
}
