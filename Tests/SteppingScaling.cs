#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Text.Json;

const double WorkGrowthLimit = 1.35;
// Most heartbeats one more hypothesis in scope may add to one instruction, which costs about 120,000.
// Unifying each lookup with every equation hypothesis added 600 to 1,950. A lookup outside a stepping
// driver reads each hypothesis once, about 25 heartbeats; building an index for it took about 410.
const double HypothesisCostLimit = 100.0;
// Limit the frontend and kernel heartbeats for checked fields and intrinsic calls relative to their references.
const double DecodedFrontendLimit = 1.03;
const double DecodedKernelLimit = 1.08;
const int Repetitions = 3;
const int LocalCount = 8;
const int HypothesisBodyCycles = 30;
const int VirtualSites = 16;
const string Int32Type = ".primitive .int32";
const string Int64Type = ".primitive .int64";
const string NodeType = ".object \"Examples\" \"Examples.Node\"";
const string PairType = ".aggregate \"Examples.Pair\" 0";
const string PairElement = ".aggregate \"Examples.Pair\" 8";
var localSlots = string.Join(", ", Enumerable.Repeat(".root (some target)", LocalCount));

ScalingChecks();
if (args is ["--self-test"])
{
    return;
}
string[]? selectedWorkloads = null;
if (Array.IndexOf(args, "--workloads") is var selection && selection >= 0)
{
    if (selection != args.Length - 2)
        throw new ArgumentException("--workloads requires a final comma-separated list.");
    selectedWorkloads = args[^1].Split(',', StringSplitOptions.RemoveEmptyEntries);
    args = args[..selection];
}
var package = args switch
{
    [] => FixturePackage(),
    ["--package", var path] => Path.GetFullPath(path),
    _ => throw new ArgumentException(
        "Usage: SteppingScaling.cs [--package <compiled checkout>] [--workloads <names>] | --self-test")
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
    ("reference", [16, 64, 256], true), ("table", [16, 64, 256], true),
    ("accumulate", [16, 64, 256], true), ("accumulate", [1024], false),
    ("locals", [16, 64, 256], true), ("contract", [16, 64, 256], false), ("loop", [16, 64, 256], false),
    ("loopfacts", [16, 64, 256], false), ("outcome", [16, 64, 256], false),
    ("lemma", [16, 64, 256], false), ("depth", [16, 64, 256], false), ("hypotheses", [16, 64, 256], false),
    ("hypothesescontract", [16, 64, 256], false), ("hypothesesloop", [16, 64, 256], false),
    ("hypotheseslookup", [16, 64, 256], false), ("hypothesesdirect", [16, 256], false),
    ("snapshots", [10, 20, 40, 80], false), ("faulting", [16, 64], false), ("arguments", [16, 64, 256], false),
    ("homes", [16, 64, 256], false), ("allocation", [16, 64, 256], false), ("calls", [16, 64, 256], true),
    ("tablecalls", [16, 64, 256], true), ("objects", [16, 64, 256], false), ("statics", [16, 64, 256], false),
    ("constructions", [16, 64, 256], false), ("objectconstructors", [16, 64, 256], false),
    ("elements", [16, 64, 256], false), ("typedelements", [16, 64, 256], false),
    ("typedsteps", [16, 64, 256], false), ("addresses", [16, 64, 256], false),
    ("addresssteps", [16, 64, 256], false), ("instance", [16, 64, 256], false), ("virtual", [1, 16, 64], false),
    ("intrinsiccalls", [16, 64, 256], false), ("structfields", [16, 64, 256], false),
    ("structfieldscontract", [16, 64, 256], false)
};
if (selectedWorkloads is not null)
{
    if (selectedWorkloads.Length == 0 || selectedWorkloads.Any(name => !workloads.Any(row => row.Name == name)))
        throw new ArgumentException("Unknown or empty stepping workload selection.");
    workloads = workloads.Where(row => selectedWorkloads.Contains(row.Name, StringComparer.Ordinal)).ToArray();
}
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
    Budgets = new { WorkGrowthLimit, HypothesisCostLimit },
    Rows = rows
};
File.WriteAllText(reportPath,
    JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }) + "\n");
foreach (var workload in rows.GroupBy(row => row.Workload))
{
    var measurements = workload.OrderBy(row => row.Size).ToArray();
    // A lookup outside a driver reads every hypothesis in scope, so only the hypothesis limit bounds it.
    for (var index = 1; index < measurements.Length && workload.Key != "hypothesesdirect"; index++)
        CheckGrowth(measurements[index - 1], measurements[index], workload.Key is "arguments" or "homes",
            workload.Key == "virtual");
    if (workload.Key.StartsWith("hypotheses"))
        CheckHypothesisCost(measurements[0], measurements[^1]);
}
foreach (var decoded in rows.Where(row => row.Workload is "structfields" or "structfieldscontract" or "intrinsiccalls"))
    CheckReferenceBudget(decoded);
Console.WriteLine("PASS stepping growth budgets for " +
    string.Join(", ", rows.Select(row => row.Workload).Distinct()) + "; results: " + reportPath);

// The instructions that open a body, repeat per cycle and end it. The accumulate, contract, lemma,
// outcome and loop bodies keep one value on the stack that grows by an operand per cycle, and the
// loop bodies end in a `nop` at the state their path reaches. The locals body stores a reference
// into each of eight reference locals per cycle. The table body offsets a native method table by a
// symbolic int32 and pops the selected cursor. The hypotheses bodies are accumulate, contract and
// loop bodies of fixed length; the direct one looks up each of their instructions outside a stepping
// driver. The faulting body divides, takes a remainder, adds with an overflow check and converts
// with one, each from the arguments, so each step reads a fact of constant size. The arguments body
// declares half as many int32 parameters as it has instructions and adds each, read once, to the sum.
// The homes body gives each of as many reference parameters a home and loads each argument once,
// which reads its home. The allocation body allocates an array of two class references per cycle and
// pops it, so each `newarr` resolves its element shape and reads one allocation fact. The calls body
// passes its argument through one call per cycle to a callee that returns it, so each call reads its
// target from the body's link table, which it names as a tagged definition, as an extraction's decoded
// method does; the tablecalls body writes that table out, as a template does.
// The objects body loads an int64 field of its object argument and pops it per cycle, so each `ldfld`
// reads the field's shape fact and two memory facts of constant size.
// The statics body loads one static field and pops it per cycle, with one static site per load.
// The constructions body constructs a class instance and pops it per cycle, so each `newobj` reads its
// `.object` link from the body's table and one allocation fact and enters a constructor that returns.
// The objectconstructors body calls the `System.Object` constructor on its object argument per cycle, so
// each call reads that its pc has no link and the runtime model fact of its pc.
// The elements body loads and pops one int32 element of its array argument, then stores its index
// argument into that element, per cycle, so each access reads one element fact of constant size.
// The typed elements body does the same through `ldelem` and `stelem` with an `int32` type operand,
// then copies one struct element of a second array onto itself. Each step evaluates the typed access
// from element facts, its shape from the literal body's layouts; the generated shape facts are in scope
// but leave the cost unchanged. The typed steps body is the same body stepped by one fact per access.
// The instance body makes one receiver-checked instance call on its object argument per cycle, into a
// method that returns at once, through its direct link. The virtual body makes
// `VirtualSites` virtual calls on it through a named dispatch table whose size is the row's size, with
// the receiver's class last, so each call reads one runtime type fact and looks its class up in the table.
// The intrinsic calls body computes `Math.Max` of its two int64 arguments and pops it per cycle, so each
// call reads that its pc has no link and the runtime model fact of its pc, a scalar intrinsic.
// The struct fields body loads and pops the int64 field at byte 8 of the struct its byref argument
// addresses, then stores its int64 argument there, per cycle; the contract body is the same body under
// contract stepping. Each access reads the field's shape fact, then its address and its load or write
// from supplied facts.
// The addresses body forms a writable and a readonly address of one int32 element of its array argument
// and pops each, per cycle, each stepped by a fact derived from the element fact and the generated shape
// fact; the address steps body steps the same body by one supplied fact per address.
static (string[] Opening, string[] Cycle, string[] Ending) Shape(string workload, int field = 0) => workload switch
{
    "calls" or "tablecalls" => ([".ldarg 0"], [".call calleeMethod"], [".ret"]),
    "memory" => ([], [".ldarg 0", ".ldarg 1", ".stind .i8", ".ldarg 0", ".ldind .i8", ".pop"],
        [".ldarg 0", ".ldind .i8", ".ret"]),
    "reference" or "table" => ([], [".ldarg 0", ".ldarg 1", ".add", ".pop"], [".ldarg 0", ".ret"]),
    "accumulate" or "contract" or "hypotheses" or "hypothesescontract" or "hypotheseslookup"
        or "hypothesesdirect" or "lemma" or "outcome" => ([".ldarg 0"], [".ldarg 1", ".add"], [".ret"]),
    "loop" or "loopfacts" or "hypothesesloop" => ([".ldarg 0"], [".ldarg 1", ".add"], [".nop"]),
    "locals" => ([], Enumerable.Range(0, LocalCount).SelectMany(slot => new[] { ".ldarg 0", $".stloc {slot}" })
        .ToArray(), [".ldloc 0", ".ret"]),
    "statics" => ([], [".ldsfld staticField", ".pop"], [".ldsfld staticField", ".ret"]),
    "faulting" => ([], [".ldarg 0", ".ldarg 1", ".div", ".pop", ".ldarg 0", ".ldarg 1", ".rem", ".pop",
        ".ldarg 0", ".ldarg 1", ".add_ovf", ".pop", ".ldarg 0", ".conv_ovf .i4", ".pop"], [".ldarg 0", ".ret"]),
    "allocation" => ([], [".ldc_i4 2", $".newarr ({NodeType})", ".pop"], [".ldc_i4 0", ".ret"]),
    // The constructor reference is a literal, as an extraction writes it.
    "constructions" => ([], [$".newobj {{ owner := {NodeType}, name := name!\".ctor\", hasThis := true, " +
        "genericArity := 0, returnType := .void, parameters := [] }", ".pop"], [".ldc_i4 0", ".ret"]),
    "objects" => ([], [".ldarg 0", ".ldfld counter", ".pop"], [".ldc_i4 0", ".ret"]),
    "objectconstructors" => ([], [".ldarg 0", ".call CIL.Extraction.objectConstructorMethod {}"],
        [".ldc_i4 0", ".ret"]),
    "instance" or "virtual" => ([], [".ldarg 0", ".callvirt (.arity 0)"], [".ldc_i4 0", ".ret"]),
    "intrinsiccalls" => ([], [".ldarg 0", ".ldarg 1", ".call maxMethod {}", ".pop"], [".ldarg 0", ".ret"]),
    "elements" => ([], [".ldarg 0", ".ldarg 1", ".ldelem .i4", ".pop", ".ldarg 0", ".ldarg 1",
        ".ldarg 1", ".stelem .i4"], [".ldc_i4 0", ".ret"]),
    "typedelements" or "typedsteps" => ([], [".ldarg 0", ".ldarg 1", $".ldelem_any ({Int32Type})", ".pop", ".ldarg 0",
        ".ldarg 1", ".ldarg 1", $".stelem_any ({Int32Type})", ".ldarg 2", ".ldarg 1", ".ldarg 2", ".ldarg 1",
        $".ldelem_any ({PairType})", $".stelem_any ({PairType})"], [".ldc_i4 0", ".ret"]),
    "structfields" or "structfieldscontract" => ([], [".ldarg 0", $".ldfld word{field}", ".pop",
        ".ldarg 0", ".ldarg 1", $".stfld word{field}"], [".ldc_i4 0", ".ret"]),
    "addresses" or "addresssteps" => ([], [".ldarg 0", ".ldarg 1", $".ldelema ({Int32Type}) false", ".pop",
        ".ldarg 0", ".ldarg 1", ".nop", $".ldelema ({Int32Type}) true", ".pop"], [".ldc_i4 0", ".ret"]),
    _ => ([], [".ldarg 0", ".ldarg 1", ".add", ".pop"], [".ldarg 0", ".ret"])
};

// The numeric locals of the snapshot body; the first stores give each one a remembered value.
const int SnapshotLocalCount = 8;

// Stores `left` into each local, then updates one local per store from its remembered value, and
// returns local 0. Both the remembered values and the facts a walk carries grow with the stores.
static string[] SnapshotOperations(int stores)
{
    var operations = new List<string>();
    for (var local = 0; local < SnapshotLocalCount; local++)
        operations.AddRange([".ldarg 0", $".stloc {local}"]);
    for (var store = SnapshotLocalCount; store < stores; store++)
        operations.AddRange([$".ldloc {store % SnapshotLocalCount}", ".ldarg 1", ".add",
            $".stloc {store % SnapshotLocalCount}"]);
    operations.AddRange([".ldloc 0", ".ret"]);
    return [.. operations];
}

// The value local 0 holds at the end of the snapshot body: `left` plus `right` once per update.
static string SnapshotResult(int stores) =>
    "left" + string.Concat(Enumerable.Repeat(" + right", (stores - 1) / SnapshotLocalCount));

// The value a stack of `depth` copies of `right` adds up to, associated to the right as `.add` pops them.
static string DepthSum(int depth) =>
    "right" + string.Concat(Enumerable.Repeat(" + (right", depth - 1)) + new string(')', depth - 1);

// An explicit layout gives each named word the same address, so each cycle uses the same memory facts.
static string StructFieldDefinitions(int count)
{
    var definitions = Enumerable.Range(0, count).Select(index => $$"""
        /-- The word selected by field index {{index}}. -/
        def word{{index}} : CIL.Extraction.FieldRef :=
          { owner := {{PairType}}, index := {{index}}, type := {{Int64Type}}, name := name!"Word{{index}}" }
        cil_field_shape environment word{{index}}
        """);
    return $$"""
        /-- An explicit struct with one named word per cycle, all at byte eight. -/
        def pairLayout : CIL.Extraction.RawLayout :=
          { identity := "Examples.Pair", explicit := true, packing := 0, declaredSize := 16,
            fields := List.replicate {{count}} { type := .signed64, offset := some 8 } }
        /-- The sixteen-byte layout shared by every field access. -/
        def pairComputed : CIL.Extraction.ComputedLayout :=
          { layout := { size := 16, fields := List.replicate {{count}} { offset := 8, width := 8 } },
            alignment := 8 }
        /-- The method environment containing the struct's raw and computed layouts. -/
        @[cil_code] def environment : CIL.LayoutEnvironment :=
          { rawLayouts := [pairLayout], layouts := #[pairComputed] }
        {{string.Join('\n', definitions)}}
        set_option cil.requireFieldShapeFacts true

        """;
}

SteppingMeasurement Measure(string workload, int requested, bool full)
{
    var memory = workload == "memory";
    var depth = Math.Max(2, requested / 2);
    var (opening, cycle, ending) = Shape(workload);
    var hypotheses = workload.StartsWith("hypotheses");
    var snapshots = workload == "snapshots";
    var parameters = Math.Max(2, requested / 2);
    var cycles = hypotheses ? HypothesisBodyCycles
        : workload == "depth" ? depth - 1
        : workload is "arguments" or "homes" ? parameters - 1
        : snapshots ? requested - SnapshotLocalCount
        : workload == "virtual" ? VirtualSites
        : Math.Max(1, (requested - opening.Length - ending.Length) / cycle.Length);
    var operations = workload switch
    {
        "depth" => Enumerable.Repeat(".ldarg 1", depth).Concat(Enumerable.Repeat(".add", depth - 1)).Append(".ret")
            .ToArray(),
        "arguments" => Enumerable.Range(1, parameters - 1).SelectMany(index => new[] { $".ldarg {index}", ".add" })
            .Prepend(".ldarg 0").Append(".ret").ToArray(),
        "homes" => Enumerable.Range(1, parameters - 1).SelectMany(index => new[] { $".ldarg {index}", ".pop" })
            .Prepend(".ldarg 0").Append(".ret").ToArray(),
        "snapshots" => SnapshotOperations(requested),
        "structfields" or "structfieldscontract" => Enumerable.Range(0, cycles)
            .SelectMany(index => Shape(workload, index).Cycle).Concat(ending).ToArray(),
        _ => opening.Concat(Enumerable.Range(0, cycles).SelectMany(_ => cycle)).Concat(ending).ToArray()
    };
    var parameterType = workload == "homes" ? $".byref ({Int32Type})" : Int32Type;
    var parameterTypes = string.Join(", ", Enumerable.Repeat(parameterType, parameters));
    var signature = $"{{ parameters := [{parameterTypes}], returnType := {parameterType} }}";
    var homes = string.Join(", ", Enumerable.Range(0, parameters).Select(index => $"({index}, .reference)"));
    var declaredField = workload switch
    {
        "arguments" => $" declared := {signature},",
        "homes" => $" declared := {signature}, parameterHomes := [{homes}],",
        "objects" or "typedelements" or "typedsteps" or "structfields" or "structfieldscontract" =>
            " environment := environment,",
        _ => ""
    };
    var statics = workload == "statics";
    var staticField = statics
        ? "def staticField : CIL.Extraction.FieldRef :=\n" +
            "  { owner := .atom \"Fixture\" \"Holder\" .classType, index := 0,\n" +
            "    type := .atom \"Fixture\" \"System.Int32\" .valueType,\n" +
            "    name := name!\"Value\" }\n" +
            "def staticValue : CIL.StaticDescriptor :=\n" +
            "  { identity := 0, field := staticField, bytes := [7, 0, 0, 0],\n" +
            "    initializer := some { method := 1, arguments := [] }, scalar := some true }\n"
        : "";
    // One site per load, so every step resolves its own pc among all the body's sites.
    var sitesField = statics
        ? " staticSites := [" + string.Join(", ", operations.Select((operation, pc) => (operation, pc))
            .Where(entry => entry.operation.StartsWith(".ldsfld", StringComparison.Ordinal))
            .Select(entry => $"({entry.pc}, staticValue)")) + "],"
        : "";
    var linkTable = "[" + string.Join(", ", Enumerable.Range(1, cycles).Select(pc => $"({pc}, .direct 1)")) + "]";
    var receiverLink = workload == "instance" ? ".direct 1" : ".virtual dispatch";
    var linksField = workload switch
    {
        "instance" or "virtual" => $""" links := [{string.Join(", ", Enumerable.Range(0, cycles)
            .Select(cycle => $"({2 * cycle + 1}, {receiverLink})"))}],""",
        "tablecalls" => $" links := {linkTable},",
        "calls" => " links := callLinks,",
        "constructions" => " links := [" +
            string.Join(", ", Enumerable.Range(0, cycles).Select(cycle => $"({cycle * 2}, .object 1 [] 8)")) + "],",
        _ => ""
    };
    var callDefinitions = workload is "calls" or "tablecalls" ? $$"""
        /-- The method every call names: one `int64` argument and an `int64` result. -/
        def calleeMethod : CIL.Extraction.MethodRef :=
          { owner := .atom "Tests" "Stepping" .classType, name := name!"Identity", hasThis := false, genericArity := 0,
            returnType := {{Int64Type}}, parameters := [{{Int64Type}}] }
        """ + "\n" + (workload == "calls" ? $$"""
        /-- The body's link table, every call entering method 1. -/
        @[cil_code] def callLinks : List (Nat × CIL.Link) := {{linkTable}}
        """ + "\n" : "") : "";
    // The dispatch table of the virtual body: one class per entry, each entering method 1.
    var dispatchDefinition = workload == "virtual" ? $$"""
        /-- The virtual body's dispatch table; the receiver's class is its last entry. -/
        @[cil_code] def dispatch : List (CIL.Extraction.TypeExpr × Nat) :=
          [{{string.Join(", ", Enumerable.Range(0, requested).Select(entry => $"({VirtualClass(entry)}, 1)"))}}]
        """ + "\n" : "";
    var maxDefinition = workload == "intrinsiccalls" ? $$"""
        /-- `Math.Max(long, long)`, which the runtime table models as a scalar intrinsic. -/
        def maxMethod : CIL.Extraction.MethodRef :=
          { owner := .atom CIL.Extraction.runtimeScope "System.Math" .classType, name := name!"Max", hasThis := false,
            genericArity := 0, returnType := {{Int64Type}}, parameters := [{{Int64Type}}, {{Int64Type}}] }
        """ + "\n" : "";
    var module = "Stepping" + workload + requested;
    var path = Path.Combine(directory, module + ".lean");
    var extraImports = workload switch
    {
        "contract" or "loop" or "loopfacts" or "hypothesescontract" or "hypothesesloop" or "hypotheseslookup"
            or "structfieldscontract" =>
            "import CIL.Safety.MethodContract\nimport CIL.Safety.LoopAutomation\n",
        "outcome" => "import CIL.Safety.LoopOutcome\nimport CIL.Safety.LoopFrameSteps\n",
        "snapshots" => "import CIL.Safety.CallingFields\nimport CIL.Safety.LocalSnapshotSteps\n",
        "allocation" or "constructions" => "import CIL.Safety.ObjectSteps\nimport CIL.Safety.SymbolicExecution\n",
        "objects" or "objectconstructors" or "instance" or "virtual" =>
            "import CIL.Safety.ObjectSteps\nimport CIL.Safety.ResolutionFacts\nimport CIL.Safety.SymbolicExecution\n",
        "elements" => "import CIL.Safety.ArrayContents\n",
        "intrinsiccalls" => "import CIL.Safety.ResolutionFacts\n",
        "typedelements" or "typedsteps" or "addresses" or "addresssteps" =>
            "import CIL.Safety.ArrayContents\nimport CIL.Safety.ResolutionFacts\n",
        _ => ""
    };
    // The objects body reads field 1 of a class, an int64 in the slot at model offset 8; a step that
    // evaluates the shape instead of reading the fact fails the row.
    var fieldDefinitions = workload switch
    {
        "objects" => $$"""
            @[cil_code] def environment : CIL.LayoutEnvironment := {}
            /-- The `int64` field 1 of a class. -/
            def counter : CIL.Extraction.FieldRef :=
              { owner := {{NodeType}}, index := 1, type := {{Int64Type}}, name := name!"count" }
            cil_field_shape environment counter
            set_option cil.requireFieldShapeFacts true
            """ + "\n",
        "structfields" or "structfieldscontract" => StructFieldDefinitions(cycles),
        "typedelements" or "typedsteps" => """
            /-- A struct of two `int32` fields. -/
            def pairLayout : CIL.Extraction.RawLayout :=
              { identity := "Examples.Pair", explicit := false, packing := 0, declaredSize := 0,
                fields := [{ type := .signed32 }, { type := .signed32 }] }
            /-- The checked layout of `pairLayout`: eight bytes. -/
            def pairComputed : CIL.Extraction.ComputedLayout :=
              { layout := { size := 8, fields := [{ offset := 0, width := 4 }, { offset := 4, width := 4 }] },
                alignment := 4 }
            /-- The one struct the body's typed accesses name. -/
            def environment : CIL.LayoutEnvironment := { rawLayouts := [pairLayout], layouts := #[pairComputed] }
            """ + "\n",
        _ => ""
    };
    // The raw view names each element type a typed access of the body names, as an extraction's does.
    var rawView = workload is "addresses" or "addresssteps" ? $$"""
        /-- The element address opcode of `body` with its type operand. -/
        def bodyClosed : CIL.Extraction.RawMethod :=
          { token := 1, owner := "Examples", hasThis := false, explicitThis := false, callingConvention := 0,
            attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
            initLocals := true, maxStack := 2, genericParameters := [],
            code := [⟨0, 143, .type ({{Int32Type}})⟩] }
        """ + "\n" : workload is "typedelements" or "typedsteps" ? $$"""
        /-- The element opcodes of `body` with their type operands. -/
        def bodyClosed : CIL.Extraction.RawMethod :=
          { token := 1, owner := "Examples", hasThis := false, explicitThis := false, callingConvention := 0,
            attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
            initLocals := true, maxStack := 4, genericParameters := [],
            code := [⟨0, 163, .type ({{Int32Type}})⟩,
              ⟨5, 164, .type ({{Int32Type}})⟩,
              ⟨10, 163, .type ({{PairType}})⟩,
              ⟨15, 164, .type ({{PairType}})⟩] }
        """ + "\n" : "";
    var localKinds = string.Join(", ", Enumerable.Repeat(".word64", SnapshotLocalCount));
    var localValues = string.Join(", ", Enumerable.Repeat(".i64 0", SnapshotLocalCount));
    var bodyDefinition = snapshots ? $$"""
        /-- Stores into numeric locals, each later update reading the local's remembered value. -/
        def body : CIL.Method := {
          code := [{{string.Join(", ", operations)}}]
          locals := [{{localValues}}]
          localKinds := [{{localKinds}}], returnsValue := true }
        cil_instruction_equations body
        """ : $$"""
        /-- A synthetic body in the emitter's explicit instruction-list shape. -/
        def body : CIL.Method := {
          locals := [], returnsValue := true,{{declaredField}}{{linksField}}{{sitesField}}
          code := [{{string.Join(",\n    ", operations)}}] }
        cil_instruction_equations body
        """;
    var header = extraImports + $$"""
        import CIL.InstructionEquations
        import CIL.Safety.LoopFrames
        open CIL.Safety
        set_option maxRecDepth 8192
        set_option maxHeartbeats 800000
        {{fieldDefinitions}}{{staticField}}{{callDefinitions}}{{dispatchDefinition}}{{maxDefinition}}{{bodyDefinition}}
        """ + "\n" + (workload is "calls" or "tablecalls" ? """
        /-- The callee every call of the calls body enters; it returns its argument. -/
        def callee : CIL.Method := { locals := [], returnsValue := true, code := [.ldarg 0, .ret] }
        cil_instruction_equations callee
        """ + "\n" : "") + (workload == "constructions" ? """
        /-- The constructor every construction of the constructions body enters; it returns at once. -/
        def constructor : CIL.Method := { locals := [], returnsValue := false, code := [.ret] }
        cil_instruction_equations constructor
        """ + "\n" : "") + (workload is "instance" or "virtual" ? """
        /-- The instance method every call of the instance and virtual bodies enters; it returns at once. -/
        def instanceMethod : CIL.Method := { locals := [], returnsValue := false, code := [.ret] }
        cil_instruction_equations instanceMethod
        """ + "\n" : "") + (workload is "objectconstructors" or "intrinsiccalls" ? """
        cil_runtime_models body
        """ + "\n" : "") + (workload is "arguments" or "homes" or "typedelements" or "typedsteps" or "addresses" or
            "addresssteps" || statics ? $$"""
        theorem body_returnsValue : body.returnsValue = true := rfl
        theorem body_declared : body.declared = {{(workload is "arguments" or "homes" ? signature : "{}")}} := rfl
        {{rawView}}cil_resolution_facts body
        """ + "\n" : "");
    var incoming = string.Join(", ",
        Enumerable.Range(0, parameters).Select(index => $".scalar (.i32 (argument {index}))"));
    var sum = string.Join(" + ", Enumerable.Range(0, parameters).Select(index => $"argument {index}"));
    var homeSlots = string.Join(", ", Enumerable.Repeat(".root (some target)", parameters));
    // Odd hypotheses are equations headed by an operator and even ones by a local variable; the direct
    // body has only the first kind. The lookup hypotheses are instruction lookups like those stepping
    // makes, which a lookup that unified with every equation hypothesis would try at each instruction.
    var hypothesisLines = string.Join("\n", Enumerable.Range(1, hypotheses ? requested : 0).Select(index =>
        workload == "hypotheseslookup"
            ? $"  have hypothesis{index} : ([.ldc_i4 {index}] : List CIL.Instruction)[0]? = " +
              $"some (.ldc_i4 {index}) := rfl"
        : index % 2 == 1 || workload == "hypothesesdirect"
            ? $"  have hypothesis{index} : right + {index} = right + {index} := rfl"
            : $"  obtain ⟨witness{index}, hypothesis{index}⟩ : ∃ witness : CIL.W64, " +
              $"witness = right + {index} := ⟨_, rfl⟩"));
    var runningSum = $"left{string.Concat(Enumerable.Repeat(" + right", cycles))}";
    // The tactic that steps a hypotheses body; the setup measurement replaces it by `sorry`.
    string HypothesesStatement(bool setup) => workload switch
    {
        "hypothesescontract" or "hypotheseslookup" => $$"""
            /-- Equations in scope before contract stepping, which it must not scan at each step. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                WP (Execution (fun fuel => invoke [body] fuel 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory))
                  (fun (final, values) => final = memory /\ values = [.scalar (.i64 ({{runningSum}}))]) := by
            {{hypothesisLines}}
              {{(setup ? "sorry" : "cil_contract_steps []\n  exact And.intro rfl rfl")}}
            """,
        "hypothesesdirect" => $$"""
            /-- Equations in scope before lookups outside a stepping driver, which scan them. -/
            theorem checked (right : CIL.W64) :
                {{string.Join(" ∧\n      ", operations.Select((operation, pc) =>
                    $"body.code[{pc}]? = some (CIL.Instruction{operation})"))}} := by
            {{hypothesisLines}}
              {{(setup ? "sorry" : $"refine ⟨{string.Join(", ", operations.Select(_ => "?_"))}⟩\n" +
                  "  all_goals cil_lookup []")}}
            """,
        "hypothesesloop" => $$"""
            /-- Equations in scope before loop stepping, which it must not scan at each step. -/
            theorem checked (memory : Memory) (left right : CIL.W64) (frame : Frame) :
                LoopReaches [body] 0 [.scalar (.i64 left), .scalar (.i64 right)]
                  (LoopState.mk 0 frame [] memory)
                  (LoopState.mk {{operations.Length - 1}} frame [.scalar (.i64 ({{runningSum}}))] memory) := by
            {{hypothesisLines}}
              {{(setup ? "sorry" : "cil_loop_steps")}}
            """,
        _ => $$"""
            /-- Equations in scope before the run, which stepping must not scan again at each step. -/
            theorem checked (memory : Memory) (left right : CIL.W64) :
                invoke [body] {{operations.Length + 1}} 0
                  [.scalar (.i64 left), .scalar (.i64 right)] memory =
                  .ok (memory, [.scalar (.i64 ({{runningSum}}))]) := by
            {{hypothesisLines}}
              {{(setup ? "sorry" : "cil_checked_steps")}}
            """
    };
    var statement = workload switch
    {
        "hypotheses" or "hypothesescontract" or "hypothesesloop" or "hypotheseslookup" or "hypothesesdirect" =>
            HypothesesStatement(false),
        "snapshots" => $$"""
            /-- Numeric locals stored and reloaded through snapshots, each store updating one local. -/
            theorem checked (memory : Memory) (slots : List LocalSlot) (boundary : Nat)
                (homes : CompleteWritableHomes memory boundary body.localKinds slots)
                (inputs outputs : List ArgumentView) (valid : ValidCall memory inputs outputs)
                (left right : BitVec 64) :
                WP (Execution (fun fuel => run [body] fuel 0 0
                  [.scalar (.i64 left), .scalar (.i64 right)] ⟨0, slots, [], 0, []⟩ [] memory))
                  (fun result => result.2 = [.scalar (.i64 ({{SnapshotResult(requested)}}))]) := by
              have formed := valid.wellFormed
              have preserved := MemoryBelow.refl boundary memory
              have authority := (MemoryBelow.refl memory.nextIdentity memory).accessBelow
              have snapshots := LocalSnapshots.empty memory slots
              cil_contract_steps (snapshots := snapshots) []
              exact rfl
            """,
        "reference" => $$"""
            /-- Repeated byte offsets retain checked reference formation and displacement. -/
            theorem checked (memory : Memory) (target moved : Reference) (offset : CIL.W32)
                (formed : formValue memory (.address target) = .ok (.reference (.address target)))
                (displaced : add memory target 1 (BitVec.ofInt 64 offset.toInt) = .ok moved) :
                invoke [body] {{operations.Length + 1}} 0
                  [.reference (.address target), .scalar (.i32 offset)] memory =
                  .ok (memory, [.reference (.address target)]) := by
              cil_checked_steps [formed, displaced]
            """,
        "table" => $$"""
            /-- Repeated native table offsets need only the checked cursor addition of each step. -/
            theorem checked (memory : Memory) (table selected : CIL.MethodTable) (offset : CIL.W32)
                (added : addNativeTable table memory (offset.signExtend 64) = .ok selected) :
                invoke [body] {{operations.Length + 1}} 0
                  [.methodTable table, .scalar (.i32 offset)] memory =
                  .ok (memory, [.methodTable table]) := by
              cil_checked_steps [added]
            """,
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
              have storeFact := step_stind_i8_of_write written
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
        "statics" => $$"""
            /-- Every static load reads the descriptor its pc's site binds and leaves memory unchanged. -/
            theorem checked (memory : Memory) :
                invoke [body] {{operations.Length + 1}} 0 [] memory = .ok (memory, [.scalar (.i32 7)]) := by
              cil_checked_steps
              rfl
            """,
        "arguments" => $$"""
            /-- Each argument is read once and added to the running sum of the ones before it. -/
            theorem checked (memory : Memory) (argument : Nat -> CIL.W32) :
                invoke [body] {{operations.Length + 1}} 0 [{{incoming}}] memory =
                  .ok (memory, [.scalar (.i32 ({{sum}}))]) := by
              cil_checked_steps
            """,
        "allocation" => $$"""
            /-- Every `newarr` resolves its class element and allocates by one fact that keeps the memory. -/
            theorem checked (memory : Memory) (array : Reference)
                (allocated : newReferenceArray memory ({{NodeType}}) (.i32 2) = .ok (array, memory)) :
                invoke [body] {{operations.Length + 1}} 0 [] memory = .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [allocated]
            """,
        "constructions" => $$"""
            /-- Every `newobj` allocates by one fact that keeps the memory and enters the constructor. -/
            theorem checked (memory : Memory) (object : Reference)
                (allocated : allocateObject memory ⟨{{NodeType}}, []⟩ 8 = .ok (object, memory))
                (formed : formObject memory (.address object) = .ok (.object (.address object))) :
                invoke [body, constructor] {{operations.Length + 3}} 0 [] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [allocated, formed]
            """,
        "objects" => $$"""
            /-- Every `ldfld` reads its slot from the field's shape fact and two memory facts of its object. -/
            theorem checked (memory : Memory) (object field : Reference) (word : CIL.W64)
                (formed : formObject memory (.address object) = .ok (.object (.address object)))
                (located : objectFieldAddress memory (.address object) ({{NodeType}}) 8 = .ok field)
                (loaded : loadValue memory (.address field) 8 false = .ok (.i64 word)) :
                invoke [body] {{operations.Length + 1}} 0 [.object (.address object)] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [formed, located, loaded]
            """,
        "structfields" => $$"""
            /-- Every struct field load and store reads its address and memory access from supplied facts. -/
            theorem checked (memory : Memory) (target field : Reference) (word : CIL.W64)
                (formed : form memory target = .ok target)
                (located : add memory target 1 (BitVec.ofNat 64 8) = .ok field)
                (loaded : loadValue memory (.address field) 8 false = .ok (.i64 word))
                (written : write memory field (numberBytes word.toNat 8) ordinaryAccessAlignment = .ok memory) :
                invoke [body] {{operations.Length + 1}} 0
                  [.reference (.address target), .scalar (.i64 word)] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [formed, located, loaded, written]
            """,
        "structfieldscontract" => $$"""
            /-- Contract stepping reads each struct field access from the same supplied facts. -/
            theorem checked (memory : Memory) (target field : Reference) (word : CIL.W64)
                (formed : form memory target = .ok target)
                (located : add memory target 1 (BitVec.ofNat 64 8) = .ok field)
                (loaded : loadValue memory (.address field) 8 false = .ok (.i64 word))
                (written : write memory field (numberBytes word.toNat 8) ordinaryAccessAlignment = .ok memory) :
                WP (Execution (fun fuel => invoke [body] fuel 0
                  [.reference (.address target), .scalar (.i64 word)] memory))
                  (fun (final, values) => final = memory /\ values = [.scalar (.i32 0)]) := by
              cil_contract_steps [formed, located, loaded, written]
              exact And.intro rfl rfl
            """,
        "objectconstructors" => $$"""
            /-- Every call of the `System.Object` constructor consumes the receiver and keeps the memory. -/
            theorem checked (memory : Memory) (object : Reference)
                (formed : formObject memory (.address object) = .ok (.object (.address object))) :
                invoke [body] {{operations.Length + 1}} 0 [.object (.address object)] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [formed]
            """,
        "instance" => $$"""
            /-- Every receiver-checked call enters the method on the live receiver and keeps the memory. -/
            theorem checked (memory : Memory) (object : Reference)
                (formed : formObject memory (.address object) = .ok (.object (.address object))) :
                invoke [body, instanceMethod] {{operations.Length + 3}} 0 [.object (.address object)] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [formed]
            """,
        "virtual" => $$"""
            /-- Every virtual call reads the receiver's class and enters the entry the table lists for it. -/
            theorem checked (memory : Memory) (object : Reference)
                (formed : formObject memory (.address object) = .ok (.object (.address object)))
                (typed : runtimeTypeOf memory object =
                  .ok { identity := {{VirtualClass(requested - 1)}}, bases := [] }) :
                invoke [body, instanceMethod] {{operations.Length + 3}} 0 [.object (.address object)] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [formed, typed]
            """,
        "elements" => $$"""
            /-- Every element access reads the one element the index names, whose store keeps the memory. -/
            theorem checked (memory : Memory) (view : ArrayView) (index : CIL.W32) (element : Reference)
                (word : CIL.Value) (valid : view.validate memory = .ok ())
                (found : arrayElement memory view index.toNat 4 = .ok element)
                (loaded : loadValue memory (.address element) 4 false = .ok word)
                (written : write memory element (numberBytes index.toNat 4) 1 = .ok memory) :
                invoke [body] {{operations.Length + 1}} 0 [.array view, .scalar (.i32 index)] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              have loadFact := step_ldelem_of_element .i4 (index := .i32 index) rfl found loaded
              have storeFact := step_stelem_narrow_of_write .i4 (index := .i32 index) rfl found written
              cil_checked_steps [valid, loadFact, storeFact]
            """,
        "typedelements" => $$"""
            /-- Every typed access evaluates to the element the index names, and every store keeps the
                memory. -/
            theorem checked (memory : Memory) (view pairs : ArrayView) (index : CIL.W32) (element : Reference)
                (word pair : CIL.Value) (valid : view.validate memory = .ok ())
                (pairsValid : pairs.validate memory = .ok ())
                (found : arrayElement memory view index.toNat 4 = .ok element)
                (loaded : loadValue memory (.address element) 4 false = .ok word)
                (written : write memory element (numberBytes index.toNat 4) 1 = .ok memory)
                (specified : pair.hasUnspecified = false)
                (pairLoaded : ∀ rest, arrayTransferInstruction ({{PairElement}}) false
                  (.scalar (.i32 index) :: .array pairs :: rest) memory = .ok (memory, .scalar pair :: rest))
                (pairStored : ∀ rest, arrayTransferInstruction ({{PairElement}}) true
                  (.scalar pair :: .scalar (.i32 index) :: .array pairs :: rest) memory = .ok (memory, rest)) :
                invoke [body] {{operations.Length + 1}} 0 [.array view, .scalar (.i32 index), .array pairs]
                  memory = .ok (memory, [.scalar (.i32 0)]) := by
              have load := step_ldelem_any_of_element (index := .i32 index) body_elementShape0 rfl rfl
                found loaded
              have store := step_stelem_any_of_write (index := .i32 index) body_elementShape0 rfl rfl
                found written
              have pairLoad := step_ldelem_any_of_transfer (index := .i32 index) body_elementShape1 rfl rfl
                pairLoaded
              have pairStore := step_stelem_any_of_transfer (index := .i32 index) body_elementShape1 rfl rfl
                specified pairStored
              cil_checked_steps [valid, pairsValid, load, store, pairLoad, pairStore]
            """,
        "typedsteps" => $$"""
            /-- Every typed access steps by one supplied fact, and every store keeps the memory. -/
            theorem checked (memory : Memory) (view pairs : ArrayView) (index : CIL.W32) (word pair : CIL.Value)
                (valid : view.validate memory = .ok ()) (pairsValid : pairs.validate memory = .ok ())
                (load : ∀ body pc args frame rest, step body (.ldelem_any ({{Int32Type}})) pc args frame
                  (.scalar (.i32 index) :: .array view :: rest) memory =
                  .ok (.next (pc + 1) (.scalar word :: rest) frame memory))
                (store : ∀ body pc args frame rest, step body (.stelem_any ({{Int32Type}})) pc args frame
                  (.scalar (.i32 index) :: .scalar (.i32 index) :: .array view :: rest) memory =
                  .ok (.next (pc + 1) rest frame memory))
                (pairLoad : ∀ body pc args frame rest, step body (.ldelem_any ({{PairType}})) pc args frame
                  (.scalar (.i32 index) :: .array pairs :: rest) memory =
                  .ok (.next (pc + 1) (.scalar pair :: rest) frame memory))
                (pairStore : ∀ body pc args frame rest, step body (.stelem_any ({{PairType}})) pc args frame
                  (.scalar pair :: .scalar (.i32 index) :: .array pairs :: rest) memory =
                  .ok (.next (pc + 1) rest frame memory)) :
                invoke [body] {{operations.Length + 1}} 0 [.array view, .scalar (.i32 index), .array pairs]
                  memory = .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [valid, pairsValid, load, store, pairLoad, pairStore]
            """,
        "addresses" => $$"""
            /-- Every element address is the element the index names, writable or read-only. -/
            theorem checked (memory : Memory) (view : ArrayView) (index : CIL.W32) (element : Reference)
                (valid : view.validate memory = .ok ()) (typed : view.elementType = .signed32)
                (found : arrayElement memory view index.toNat 4 = .ok element) :
                invoke [body] {{operations.Length + 1}} 0 [.array view, .scalar (.i32 index)] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              have writable := step_ldelema_of_element false body_elementShape0 typed (index := .i32 index) rfl
                found
              have readOnly := step_ldelema_of_element true body_elementShape0 typed (index := .i32 index) rfl
                found
              cil_checked_steps [valid, writable, readOnly]
            """,
        "addresssteps" => $$"""
            /-- Every element address steps by one supplied fact. -/
            theorem checked (memory : Memory) (view : ArrayView) (index : CIL.W32) (element : Reference)
                (valid : view.validate memory = .ok ())
                (writable : ∀ body pc args frame rest, step body (.ldelema ({{Int32Type}}) false) pc args frame
                  (.scalar (.i32 index) :: .array view :: rest) memory =
                  .ok (.next (pc + 1) (.reference (.address element) :: rest) frame memory))
                (readOnly : ∀ body pc args frame rest, step body (.ldelema ({{Int32Type}}) true) pc args frame
                  (.scalar (.i32 index) :: .array view :: rest) memory =
                  .ok (.next (pc + 1) (.readOnlyReference (.address element) :: rest) frame memory)) :
                invoke [body] {{operations.Length + 1}} 0 [.array view, .scalar (.i32 index)] memory =
                  .ok (memory, [.scalar (.i32 0)]) := by
              cil_checked_steps [valid, writable, readOnly]
            """,
        "homes" => $$"""
            /-- Each reference parameter is read once from the home slot of a literal frame. -/
            theorem checked (memory : Memory) (target : ManagedReference) (activation : Nat)
                (formed : formValue memory target = .ok (.reference target)) :
                run [body] {{operations.Length + 1}} 0 0 [.reference target]
                  { activation := activation, locals := [{{homeSlots}}], owned := [] } [] memory =
                  .ok (memory, [.reference target]) := by
              cil_checked_steps [formed]
            """,
        "calls" or "tablecalls" => $$"""
            /-- Each call enters the callee, which returns its argument, so the value passes through. -/
            theorem checked (memory : Memory) (left : CIL.W64) :
                invoke [body, callee] {{operations.Length + 3}} 0 [.scalar (.i64 left)] memory =
                  .ok (memory, [.scalar (.i64 left)]) := by
              cil_checked_steps
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
    // The snapshot lemmas rest on choice, as `LocalSnapshots.store_at` and `LocalSnapshots.load` do.
    var axioms = snapshots ? "propext, Classical.choice, Quot.sound"
        : workload == "hypothesesdirect" ? "propext" : "propext, Quot.sound";
    var Audit = $$"""

        /-- info: 'checked' depends on axioms: [{{axioms}}] -/
        #guard_msgs (whitespace := lax) in
        #print axioms checked
        """;
    File.WriteAllText(path, header);
    var baseline = full ? Compile(module, path, "header") : null;
    File.WriteAllText(path, header + statement + "\n" + Audit + "\n");
    var samples = Enumerable.Range(0, full ? Repetitions : 1)
        .Select(index => Compile(module, path, "proof" + index)).ToArray();
    var commands = samples.Select(sample => sample.Commands.Single(command => command.Label == "checked")).ToArray();
    // The message carries every sample, so a run that differs says which count moved and by how much.
    if (commands.Select(command => command.Heartbeats).Distinct().Count() != 1 ||
        commands.Select(command => command.KernelHeartbeats).Distinct().Count() != 1 ||
        samples.Select(sample => sample.Bytes).Distinct().Count() != 1)
        throw new InvalidOperationException($"Stepping work did not repeat exactly for {module}: heartbeats " +
            $"{string.Join(", ", commands.Select(command => command.Heartbeats))}; kernel heartbeats " +
            $"{string.Join(", ", commands.Select(command => command.KernelHeartbeats))}; bytes " +
            $"{string.Join(", ", samples.Select(sample => sample.Bytes))}");
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
    // Elaborating each hypothesis costs the same with or without stepping, so the same statement
    // with `sorry` for the stepping tactic is measured and subtracted.
    if (hypotheses)
        row = WithoutSetup(row, SetupCost(module, header, HypothesesStatement(true)));
    Console.WriteLine(string.Create(System.Globalization.CultureInfo.InvariantCulture, 
        $"{workload} {row.Instructions} instructions: {row.FrontendHeartbeatsPerInstruction:F0} frontend HB, " +
        $"{row.KernelHeartbeatsPerInstruction:F0} kernel HB, {row.ProofBytesPerInstruction:F0} proof bytes, " +
        $"{row.FrontendMsPerInstruction:F2} frontend ms per instruction"));
    return row;
}

// What elaborating and checking the statement `statement` costs without stepping.
CommandSample SetupCost(string module, string header, string statement)
{
    var setupModule = module + "Setup";
    var setupPath = Path.Combine(directory, setupModule + ".lean");
    File.WriteAllText(setupPath, header + statement + "\n");
    var sample = Compile(setupModule, setupPath, "setup");
    return sample.Commands.Single(command => command.Label == "checked");
}

// The stepping share of `row`: its frontend heartbeats, kernel heartbeats and frontend milliseconds
// less those of `setup`, the same statement closed by `sorry`.
static SteppingMeasurement WithoutSetup(SteppingMeasurement row, CommandSample setup) => row with
{
    FrontendHeartbeats = row.FrontendHeartbeats - setup.Heartbeats,
    KernelHeartbeats = row.KernelHeartbeats - setup.KernelHeartbeats,
    FrontendMs = Math.Max(0, row.FrontendMs - setup.ElapsedMs)
};

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

// The class of entry `entry` of the virtual body's dispatch table.
static string VirtualClass(int entry) => $".object \"Examples\" \"Examples.Class{entry}\"";

static long Median(IEnumerable<long> values)
{
    var sorted = values.Order().ToArray();
    return sorted[sorted.Length / 2];
}

// A body whose argument count grows with its length may cost per instruction at most linearly in that
// count, since each read indexes the argument list. A virtual call looks its class up in a literal list, so it
// may cost at most linearly in the table size. Any other body costs a bounded amount per instruction.
static void CheckGrowth(SteppingMeasurement shorter, SteppingMeasurement longer, bool linearInArguments = false,
    bool linearInTable = false)
{
    var workBudget = linearInArguments ? (double)longer.Instructions / shorter.Instructions
        : linearInTable ? (double)longer.Size / shorter.Size : WorkGrowthLimit;
    Check("frontend heartbeats", shorter.FrontendHeartbeatsPerInstruction,
        longer.FrontendHeartbeatsPerInstruction, workBudget);
    Check("kernel heartbeats", shorter.KernelHeartbeatsPerInstruction,
        longer.KernelHeartbeatsPerInstruction, workBudget);
    // Proof bytes require the header-only module; timing remains a diagnostic measurement.
    if (shorter.Full && longer.Full)
    {
        Check("compiled proof bytes", shorter.ProofBytesPerInstruction,
            longer.ProofBytesPerInstruction, WorkGrowthLimit);
    }

    void Check(string metric, double before, double after, double budget)
    {
        if (before <= 0 || after / before > budget)
            throw new InvalidOperationException(string.Create(System.Globalization.CultureInfo.InvariantCulture, 
                $"{longer.Workload} {metric}/instruction grew from {before:F3} to {after:F3} " +
                $"between sizes {shorter.Size} and {longer.Size} ({shorter.Instructions} and " +
                $"{longer.Instructions} instructions); budget {budget:F2}."));
    }
}

// Heartbeats per hypothesis per instruction between the smallest and the largest number of
// hypotheses, which the limit bounds absolutely so that a cost far under the ratio limit still shows.
static void CheckHypothesisCost(SteppingMeasurement fewest, SteppingMeasurement most)
{
    var added = (double)(most.FrontendHeartbeats - fewest.FrontendHeartbeats) /
        ((most.Size - fewest.Size) * most.Instructions);
    if (added > HypothesisCostLimit)
        throw new InvalidOperationException(string.Create(System.Globalization.CultureInfo.InvariantCulture,
            $"{most.Workload}: each hypothesis in scope added {added:F0} heartbeats to each instruction " +
            $"between {fewest.Size} and {most.Size} hypotheses; limit {HypothesisCostLimit:F0}."));
}

static void ScalingChecks()
{
    var few = new SteppingMeasurement("test", 62, 30, 0, 7_900_000, 1, 0, 0, 0, 0, [], 0) { Size = 16 };
    CheckHypothesisCost(few, few with { Size = 256, FrontendHeartbeats = 7_900_000 + 240L * 62 * 40 });
    var costly = few with { Size = 256, FrontendHeartbeats = 7_900_000 + 240L * 62 * 380 };
    var rejected = false;
    try { CheckHypothesisCost(few, costly); }
    catch (InvalidOperationException) { rejected = true; }
    if (!rejected)
        throw new InvalidOperationException("The hypothesis limit accepted a cost of 380 heartbeats per hypothesis.");
    var stepped = WithoutSetup(few with { FrontendMs = 900 }, new CommandSample("checked", 400_000, 0, 700, 0));
    if (stepped.FrontendHeartbeats != 7_500_000 || stepped.FrontendMs != 200)
        throw new InvalidOperationException("A hypotheses row kept the cost of elaborating its hypotheses.");
    var baseline = new SteppingMeasurement("test", 16, 4, 0,
        16000, 1600, 32000, 160, 16, 200, [], 1);
    var linear = baseline with { Instructions = 64, FrontendHeartbeats = 64000, KernelHeartbeats = 6400,
        ProofBytes = 128000, FrontendMs = 640 };
    CheckGrowth(baseline, linear);
    CheckGrowth(baseline, linear with { FrontendMs = 2560 });
    foreach (var mutant in new[] { linear with { FrontendHeartbeats = 256000 },
        linear with { KernelHeartbeats = 25600 }, linear with { ProofBytes = 512000 } })
    {
        try { CheckGrowth(baseline, mutant); }
        catch (InvalidOperationException) { continue; }
        throw new InvalidOperationException("Scaling budget accepted a quadratic work mutant.");
    }
    // Per-instruction work four times higher at four times the arguments is linear; sixteen times is not.
    var reduced = baseline with { Full = false };
    var linearInArguments = reduced with { Instructions = 64, KernelHeartbeats = 4 * 6400 };
    CheckGrowth(reduced, linearInArguments, linearInArguments: true);
    if (!Rejects(() => CheckGrowth(reduced, linearInArguments with { KernelHeartbeats = 16 * 6400 }, true)))
        throw new InvalidOperationException("The argument budget accepted a per-instruction quadratic mutant.");
    var fieldBody = baseline with { Workload = "structfields", Size = 16, Instructions = 14,
        FrontendHeartbeats = 3_880_175, KernelHeartbeats = 83_853 };
    CheckReferenceBudget(fieldBody);
    if (!Rejects(() => CheckReferenceBudget(fieldBody with { KernelHeartbeats = 2 * fieldBody.KernelHeartbeats })) ||
        !Rejects(() => CheckReferenceBudget(fieldBody with { FrontendHeartbeats = 2 * fieldBody.FrontendHeartbeats })))
        throw new InvalidOperationException("The field budget accepted twice the reference cost.");
    // With the same instructions at every size, per-instruction cost must stay flat in the size: a
    // step that scans each hypothesis in scope grows with it.
    var flat = baseline with { Size = 256, FrontendHeartbeats = 17000, KernelHeartbeats = 1700 };
    CheckGrowth(baseline with { Size = 16 }, flat);
    var scanning = flat with { FrontendHeartbeats = 24000 };
    try { CheckGrowth(baseline with { Size = 16 }, scanning); }
    catch (InvalidOperationException)
    {
        Console.WriteLine("PASS stepping budgets accept linear work and reject each quadratic metric");
        return;
    }
    throw new InvalidOperationException("The hypothesis budget accepted a cost that grows with the hypotheses.");
}

// Lean 4.35.0 checked-theorem heartbeats at 3c7f6b5a, where every frame carries its handler resumptions.
static void CheckReferenceBudget(SteppingMeasurement decoded)
{
    var (instructions, frontend, kernel) = (decoded.Workload, decoded.Size) switch
    {
        ("structfields", 16) => (14, 3_880_175, 83_853),
        ("structfields", 64) => (62, 9_868_186, 192_761),
        ("structfields", 256) => (254, 33_709_768, 628_304),
        ("structfieldscontract", 16) => (14, 3_431_647, 83_568),
        ("structfieldscontract", 64) => (62, 9_681_966, 191_398),
        ("structfieldscontract", 256) => (254, 34_770_033, 622_713),
        ("intrinsiccalls", 16) => (14, 3_480_200, 87_919),
        ("intrinsiccalls", 64) => (62, 9_893_499, 201_217),
        ("intrinsiccalls", 256) => (254, 35_238_547, 654_510),
        _ => throw new InvalidOperationException($"Missing reference baseline for {decoded.Workload} {decoded.Size}.")
    };
    if (decoded.Instructions != instructions)
        throw new InvalidOperationException($"{decoded.Workload} baseline has {instructions} instructions, measured {decoded.Instructions}.");
    Check("frontend heartbeats", decoded.FrontendHeartbeats, frontend, DecodedFrontendLimit);
    Check("kernel heartbeats", decoded.KernelHeartbeats, kernel, DecodedKernelLimit);

    void Check(string metric, double decodedCost, double referenceCost, double limit)
    {
        var ratio = decodedCost / referenceCost;
        if (referenceCost <= 0 || ratio > limit)
            throw new InvalidOperationException(string.Create(System.Globalization.CultureInfo.InvariantCulture,
                $"""{decoded.Workload} {metric}: {ratio:F4} of reference at size {decoded.Size}; limit {limit:F4}"""));
    }
}

static bool Rejects(Action check)
{
    try { check(); }
    catch (InvalidOperationException) { return true; }
    return false;
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
