#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Text.Json;

const double WorkGrowthLimit = 1.35;
const double TimeGrowthLimit = 2.0;
const int Repetitions = 3;
const int LocalCount = 8;
const int HypothesisBodyCycles = 30;
var localSlots = string.Join(", ", Enumerable.Repeat(".root (some target)", LocalCount));

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
// Sizes are instruction counts, except for hypotheses, where they count the hypotheses in scope. A
// reduced measurement compiles once and checks heartbeats only, which are exactly repeatable.
var workloads = new (string Name, int[] Sizes, bool Full)[]
{
    ("scalar", [16, 64, 256], true), ("memory", [16, 64, 256], true),
    ("accumulate", [16, 64, 256], true), ("accumulate", [1024], false),
    ("locals", [16, 64, 256], true), ("contract", [16, 64, 256], false), ("loop", [16, 64, 256], false),
    ("loopfacts", [16, 64, 256], false), ("outcome", [16, 64, 256], false),
    ("lemma", [16, 64, 256], false), ("depth", [16, 64, 256], false), ("hypotheses", [16, 64, 256], false),
    ("faulting", [16, 64], false)
};
foreach (var (workload, sizes, full) in workloads)
    foreach (var requested in sizes)
        rows.Add(Measure(workload, requested, full));

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
    var measurements = workload.OrderBy(row => row.Size).ToArray();
    if (workload.Key == "hypotheses")
    {
        CheckMarginalGrowth(measurements);
        continue;
    }
    for (var index = 1; index < measurements.Length; index++)
        CheckGrowth(measurements[index - 1], measurements[index]);
}
Console.WriteLine("PASS stepping growth budgets for scalar, memory, accumulate, locals, contract, loop, " +
    "loopfacts, outcome, lemma, depth, hypotheses and faulting bodies; results: " + reportPath);

// The instructions that open a body, repeat per cycle and end it. The accumulate, contract, lemma,
// outcome and loop bodies keep one value on the stack that grows by an operand per cycle, and the
// loop bodies end in a `nop` at the state their path reaches. The locals body stores a reference
// into each of eight reference locals per cycle. The hypotheses body is an accumulate body of
// fixed length. The faulting body divides, takes a remainder, adds with an overflow check and
// converts with one, each from the arguments, so each step reads a fact of constant size.
static (string[] Opening, string[] Cycle, string[] Ending) Shape(string workload) => workload switch
{
    "memory" => ([], [".arg 0", ".arg 1", ".store64", ".arg 0", ".load64", ".pop"], [".arg 0", ".load64", ".ret"]),
    "accumulate" or "contract" or "hypotheses" or "lemma" or "outcome" => ([".arg 0"], [".arg 1", ".add"], [".ret"]),
    "loop" or "loopfacts" => ([".arg 0"], [".arg 1", ".add"], [".nop"]),
    "locals" => ([], Enumerable.Range(0, LocalCount).SelectMany(slot => new[] { ".arg 0", $".stloc {slot}" })
        .ToArray(), [".local 0", ".ret"]),
    "faulting" => ([], [".arg 0", ".arg 1", ".div", ".pop", ".arg 0", ".arg 1", ".rem", ".pop", ".arg 0", ".arg 1",
        ".add_ovf", ".pop", ".arg 0", ".conv_ovf .i4", ".pop"], [".arg 0", ".ret"]),
    _ => ([], [".arg 0", ".arg 1", ".add", ".pop"], [".arg 0", ".ret"])
};

// The value a stack of `depth` copies of `right` adds up to, associated to the right as `.add` pops them.
static string DepthSum(int depth) =>
    "right" + string.Concat(Enumerable.Repeat(" + (right", depth - 1)) + new string(')', depth - 1);

SteppingMeasurement Measure(string workload, int requested, bool full)
{
    var memory = workload == "memory";
    var depth = Math.Max(2, requested / 2);
    var (opening, cycle, ending) = Shape(workload);
    var cycles = workload == "hypotheses" ? HypothesisBodyCycles
        : workload == "depth" ? depth - 1
        : Math.Max(1, (requested - opening.Length - ending.Length) / cycle.Length);
    var operations = workload == "depth"
        ? Enumerable.Repeat(".arg 1", depth).Concat(Enumerable.Repeat(".add", depth - 1)).Append(".ret").ToArray()
        : opening.Concat(Enumerable.Range(0, cycles).SelectMany(_ => cycle)).Concat(ending).ToArray();
    var module = "Stepping" + workload + requested;
    var path = Path.Combine(directory, module + ".lean");
    var extraImports = workload switch
    {
        "contract" or "loop" or "loopfacts" => "import CIL.Safety.MethodContract\nimport CIL.Safety.LoopAutomation\n",
        "outcome" => "import CIL.Safety.LoopOutcome\nimport CIL.Safety.LoopFrameSteps\n",
        _ => ""
    };
    var header = extraImports + $$"""
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
    var statement = workload switch
    {
        "memory" => $$"""
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
            """,
        "accumulate" => $$"""
            /-- The running sum stays on the stack, so each step's state holds every earlier addition. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                invoke [body] {{operations.Length + 1}} 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory =
                  .ok (memory, [.scalar (.i64 (left{{string.Concat(Enumerable.Repeat(" + right", cycles))}}))]) := by
              cil_checked_steps
            """,
        "contract" => $$"""
            /-- Contract stepping keeps the running sum on the stack. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                WP (Execution (fun fuel => invoke [body] fuel 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory))
                  (fun (final, values) => final = memory /\
                    values = [.scalar (.i64 (left{{string.Concat(Enumerable.Repeat(" + right", cycles))}}))]) := by
              cil_contract_steps []
              exact And.intro rfl rfl
            """,
        "loop" => $$"""
            /-- Loop stepping walks a path whose stack holds the running sum. -/
            theorem checked (memory : Memory) (left right : CIL.W64) (frame : Frame) :
                LoopReaches [body] 0 [.scalar (.i64 left), .scalar (.i64 right)]
                  (LoopState.mk 0 frame [] memory)
                  (LoopState.mk {{operations.Length - 1}} frame
                    [.scalar (.i64 (left{{string.Concat(Enumerable.Repeat(" + right", cycles))}}))] memory) := by
              cil_loop_steps
            """,
        "loopfacts" => $$"""
            /-- A case fact in the context makes every instruction read a second group of facts. -/
            theorem checked (memory : Memory) (left right : CIL.W64) (frame : Frame) (different : left ≠ right) :
                LoopReaches [body] 0 [.scalar (.i64 left), .scalar (.i64 right)]
                  (LoopState.mk 0 frame [] memory)
                  (LoopState.mk {{operations.Length - 1}} frame
                    [.scalar (.i64 (left{{string.Concat(Enumerable.Repeat(" + right", cycles))}}))] memory) := by
              cil_loop_steps
            """,
        "outcome" => $$"""
            /-- The outcome walk steps every instruction to the return, which closes the goal. -/
            theorem checked (memory : Memory) (left right : CIL.W64) (frame : Frame) :
                LoopOutcome [body] 0 [.scalar (.i64 left), .scalar (.i64 right)]
                  (fun _ values => values = [.scalar (.i64 (left{{string.Concat(Enumerable.Repeat(" + right", cycles))}}))])
                  none (LoopState.mk 0 frame [] memory) := by
              cil_loop_outcome_advance []
              rw [loop_outcome_none]
              cil_loop_finish
            """,
        "lemma" => $$"""
            /-- A universe-polymorphic lemma among the facts keeps the record, so the cost per step is flat. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                invoke [body] {{operations.Length + 1}} 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory =
                  .ok (memory, [.scalar (.i64 (left{{string.Concat(Enumerable.Repeat(" + right", cycles))}}))]) := by
              cil_checked_steps [List.length_append]
            """,
        "depth" => $$"""
            /-- The stack grows to {{depth}} values, then every one is added. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                invoke [body] {{operations.Length + 1}} 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory =
                  .ok (memory, [.scalar (.i64 ({{DepthSum(depth)}}))]) := by
              cil_checked_steps
            """,
        "hypotheses" => $$"""
            /-- Equations in scope before the run, which stepping must not scan again at each step. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                invoke [body] {{operations.Length + 1}} 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory =
                  .ok (memory, [.scalar (.i64 (left{{string.Concat(Enumerable.Repeat(" + right", cycles))}}))]) := by
            {{string.Join("\n", Enumerable.Range(1, requested).Select(index =>
                $"  have hypothesis{index} : right + {index} = right + {index} := rfl"))}}
              cil_checked_steps
            """,
        "faulting" => $$"""
            /-- Each faulting instruction advances from the fact that its operands do not fault. -/
            theorem checked (memory : Memory) (left right quotient remainder sum : CIL.W64) (narrowed : CIL.W32)
                (divided : CIL.divideValues true false (.i64 left) (.i64 right) = .ok (.i64 quotient))
                (reduced : CIL.divideValues true true (.i64 left) (.i64 right) = .ok (.i64 remainder))
                (added : CIL.checkedValues .add true (.i64 left) (.i64 right) = .ok (.i64 sum))
                (converted : CIL.convertInteger 32 true false (.i64 left) = .ok (.i32 narrowed)) :
                invoke [body] {{operations.Length + 1}} 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory =
                  .ok (memory, [.scalar (.i64 left)]) := by
              cil_checked_steps [divided, reduced, added, converted]
            """,
        "locals" => $$"""
            /-- Every cycle replaces all eight reference locals of a literal frame. -/
            theorem checked (memory : Memory) (target : ManagedReference) (activation : Nat)
                (formed : formValue memory target = .ok (.reference target)) :
                run [body] {{operations.Length + 1}} 0 0 [.reference target]
                  { activation := activation, locals := [{{localSlots}}], owned := [] } [] memory =
                  .ok (memory, [.reference target]) := by
              cil_checked_steps [formed]
            """,
        _ => $$"""
            /-- All scalar instructions execute and return the original first operand. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                invoke [body] {{operations.Length + 1}} 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory =
                  .ok (memory, [.scalar (.i64 left)]) := by
              cil_checked_steps
            """
    };
    const string Audit = """

        /-- info: 'checked' depends on axioms: [propext, Quot.sound] -/
        #guard_msgs (whitespace := lax) in
        #print axioms checked
        """;
    File.WriteAllText(path, header);
    var baseline = full ? Compile(module, path, "header") : null;
    File.WriteAllText(path, header + statement + "\n" + Audit + "\n");
    var samples = Enumerable.Range(0, full ? Repetitions : 1)
        .Select(index => Compile(module, path, "proof" + index)).ToArray();
    var commands = samples.Select(sample => sample.Commands.Single(command => command.Label == "checked")).ToArray();
    if (commands.Select(command => command.Heartbeats).Distinct().Count() != 1 ||
        commands.Select(command => command.KernelHeartbeats).Distinct().Count() != 1 ||
        samples.Select(sample => sample.Bytes).Distinct().Count() != 1)
        throw new InvalidOperationException("Stepping work did not repeat exactly for " + module);
    var proofBytes = baseline is null ? 0 : samples[0].Bytes - baseline.Bytes;
    if (full && proofBytes <= 0) throw new InvalidOperationException("Missing compiled proof bytes for " + module);
    var row = new SteppingMeasurement(workload, operations.Length, cycles, memory ? 2 * cycles + 1 : 0,
        commands[0].Heartbeats, commands[0].KernelHeartbeats, proofBytes,
        Median(commands.Select(command => command.ElapsedMs)), Median(commands.Select(command => command.KernelMs)),
        Median(samples.Select(sample => sample.Commands.Sum(command => command.ElapsedMs))),
        samples.Select(sample => sample.ProcessMs).ToArray(), baseline?.ProcessMs ?? 0)
    {
        Size = requested,
        Full = full,
        CompiledModuleBytes = samples[0].Bytes,
        HeaderModuleBytes = baseline?.Bytes ?? 0,
        HeaderCommandsMs = baseline?.Commands.Sum(command => command.ElapsedMs) ?? 0,
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
    // Proof bytes need the header-only module and milliseconds need repeated runs; a reduced
    // measurement has neither.
    if (shorter.Full && longer.Full)
    {
        Check("compiled proof bytes", shorter.ProofBytesPerInstruction,
            longer.ProofBytesPerInstruction, WorkGrowthLimit);
        Check("frontend milliseconds", shorter.FrontendMsPerInstruction,
            longer.FrontendMsPerInstruction, TimeGrowthLimit);
    }

    void Check(string metric, double before, double after, double budget)
    {
        if (before <= 0 || after / before > budget)
            throw new InvalidOperationException(string.Create(System.Globalization.CultureInfo.InvariantCulture, 
                $"{longer.Workload} {metric}/instruction grew from {before:F3} to {after:F3} " +
                $"between {shorter.Instructions} and {longer.Instructions} instructions; budget {budget:F2}."));
    }
}

// The cost of one more hypothesis in scope may not grow with the number already there: a step
// that scans the context costs a fixed amount per hypothesis, one that compares each hypothesis
// with every other costs more per hypothesis the more there are.
static void CheckMarginalGrowth(SteppingMeasurement[] measurements)
{
    double Marginal(SteppingMeasurement shorter, SteppingMeasurement longer) =>
        (double)(longer.FrontendHeartbeats - shorter.FrontendHeartbeats) / (longer.Size - shorter.Size);
    for (var index = 2; index < measurements.Length; index++)
    {
        var before = Marginal(measurements[index - 2], measurements[index - 1]);
        var after = Marginal(measurements[index - 1], measurements[index]);
        if (before <= 0 || after / before > WorkGrowthLimit)
            throw new InvalidOperationException(string.Create(System.Globalization.CultureInfo.InvariantCulture,
                $"{measurements[index].Workload} heartbeats per added hypothesis grew from {before:F0} to " +
                $"{after:F0} between {measurements[index - 1].Size} and {measurements[index].Size} " +
                $"hypotheses; budget {WorkGrowthLimit:F2}."));
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
    var scanned = new[] { 16, 64, 256 }.Select(size => baseline with { Size = size,
        FrontendHeartbeats = 1_000_000 + 1000L * size }).ToArray();
    CheckMarginalGrowth(scanned);
    var compared = new[] { 16, 64, 256 }.Select(size => baseline with { Size = size,
        FrontendHeartbeats = 1_000_000 + 1000L * size * size / 16 }).ToArray();
    try { CheckMarginalGrowth(compared); }
    catch (InvalidOperationException)
    {
        Console.WriteLine("PASS stepping budgets accept linear work and reject each quadratic metric");
        return;
    }
    throw new InvalidOperationException("The hypothesis budget accepted a quadratic mutant.");
}

internal sealed record CommandSample(string Label, long Heartbeats, long KernelHeartbeats,
    long ElapsedMs, long KernelMs);
internal sealed record CompiledSample(CommandSample[] Commands, long Bytes, long ProcessMs);
internal sealed record SteppingMeasurement(string Workload, int Instructions, int Cycles, int MemoryOperations,
    long FrontendHeartbeats, long KernelHeartbeats, long ProofBytes, long FrontendMs, long KernelMs,
    long ModuleCommandsMs, long[] ProcessMs, long HeaderProcessMs)
{
    /// <summary>The requested size: instructions, or hypotheses in scope for the hypotheses body.</summary>
    public int Size { get; init; }
    /// <summary>Whether the row was compiled three times with a header-only baseline.</summary>
    public bool Full { get; init; } = true;
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
