#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Globalization;
using System.Text.RegularExpressions;

// `cil_instruction_equations` proves each equation from the code suffix that starts its block. Proved
// against the whole code list instead, it walks one cell per preceding instruction and a method's equations
// cost quadratic time, which this fixture reports as a per-instruction cost that grows with the method.
const int ShortStatements = 125;
const int LongStatements = 500;
// Compiling four times the instructions may cost at most this much more per instruction.
const double AllowedGrowth = 1.25;
const int FewCalls = 100;
const int ManyCalls = 400;
// Link reads whose cost grows with the square of the calls make the recheck of an embedding cost 1.29 times as
// much per call at 2,048 calls as at 512; linear reads cost the same.
const int EmbedFewCalls = 512;
const int EmbedManyCalls = 2048;
// Segments in each of the two blocks of an embedding whose pc map puts the second block first.
const int ReorderFewSegments = 128;
const int ReorderManySegments = 512;
// Four times the calls of an embedding may cost at most this much more per call.
const double AllowedEmbedGrowth = 1.15;
// Two calls in bodies of these many statements: the link output must not grow with the body.
const int SparseShortStatements = 250;
const int SparseLongStatements = 1000;
// Four times the call sites may cost at most this much more per call site.
const double AllowedCallGrowth = 1.35;
// Type identities compare one code per name, so a name four times as long may cost at most this much more.
const double AllowedNameGrowth = 1.05;
// The most heartbeats deciding equality or inequality of two type identities may cost at either name length.
const long TypeDecisionLimit = 9_500;
// `decide +kernel` costs about 2,000 heartbeats for any statement; less means the decision was not measured.
const long KernelDecisionFloor = 2_000;
// Bodies of these many array element addresses. A readonly rule that scans the body at every address costs
// about 1.5 times as much per address at each doubling; the indexed rule costs about 1.1 times as much at 512.
const int FewAddresses = 128;
const int MoreAddresses = 256;
const int ManyAddresses = 512;
// Bodies of these many local loads, stores, addresses and pops, which cycle over four int32 locals.
const int FewLocalAccesses = 256;
const int MoreLocalAccesses = 1024;
const int ManyLocalAccesses = 4096;
// Bodies of these many locals, each stored once and then loaded or addressed. A check that walks the locals list,
// or the list of locals a `calli` consumes, at each such site costs between 1.3 and 2.3 times as much per
// instruction at 512 as at 128; reading indexes built once per body costs at most about 1.1 times as much.
const int FewLocals = 128;
const int MoreLocals = 256;
const int ManyLocals = 512;

var directory = At("artifacts/LookupScaling");
Directory.CreateDirectory(directory);

// The heartbeats `decide +kernel` adds to the same statement closed with `sorry`, for equal and unequal type
// identities whose names have 20 and 80 characters and share all but their last character. Each statement is
// distinct, so no decision reuses the auxiliary lemma of another.
Dictionary<string, long> TypeDecisionCosts()
{
    const string Prefix = "System.Runtime.InteropServices.Marshalling.Collections.Generic.Dictionary.Keys.";
    string Type(int length, char last)
    {
        var name = Prefix[..(length - 1)] + last;
        return $$"""({ assembly := runtime, typeNamespace := name!"System", name := name!"{{name}}" } : """ +
            "TypeIdentity)";
    }
    var statements = new[] { 20, 80 }.SelectMany(length => new[]
    {
        $"#kernel_cost \"equal {length}\" {Type(length, '0')} = {Type(length, '0')}",
        $"#kernel_cost \"unequal {length}\" Not ({Type(length, '1')} = {Type(length, '2')})"
    });
    var path = Path.Combine(directory, "TypeIdentityEquality.lean");
    File.WriteAllText(path, """
        import CIL.Identity
        open CIL Lean Elab Command
        /-- The core library assembly of .NET 10. -/
        def runtime : AssemblyName :=
          { name := name!"System.Runtime", version := { major := 10, minor := 0, build := 0, revision := 0 },
            culture := name!"", publicKeyToken := some 0xb03f5f7f11d50a3a }
        /-- Logs what `decide +kernel` costs beyond elaborating the statement. -/
        elab "#kernel_cost " label:str statement:term : command => do
          let before <- IO.getNumHeartbeats
          elabCommand (<- `(example : $statement := sorry))
          let middle <- IO.getNumHeartbeats
          elabCommand (<- `(example : $statement := by decide +kernel))
          let after <- IO.getNumHeartbeats
          let cost : Int := ((after - middle : Nat) : Int) - ((middle - before : Nat) : Int)
          logInfo m!"{label.getString} {cost} heartbeats"

        """ + string.Join("\n", statements) + "\n");
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var costs = LookupPatterns.TypeDecision().Matches(output).ToDictionary(
        match => match.Groups[1].Value, match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
    if (costs.Count != 4) throw new InvalidOperationException("Missing type identity decision costs:\n" + output);
    return costs;
}
var decisions = TypeDecisionCosts();
foreach (var outcome in new[] { "equal", "unequal" })
{
    long shortName = decisions[outcome + " 20"], longName = decisions[outcome + " 80"];
    var measured = $"{shortName} heartbeats at 20 characters and {longName} at 80";
    if (Math.Min(shortName, longName) < KernelDecisionFloor || Math.Max(shortName, longName) > TypeDecisionLimit ||
        longName > shortName * AllowedNameGrowth)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Deciding {outcome} type identities costs {measured}; the limits are {TypeDecisionLimit} heartbeats " +
            $"and {AllowedNameGrowth} times as many at 80 characters."));
    Console.WriteLine($"PASS deciding {outcome} type identities costs {measured}");
}

var source = Path.Combine(directory, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Lookups.csproj"), """
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
</Project>
""");
string Method(string name, int statements) =>
    $"public static ulong {name}(ulong x, ulong y) {{ ulong word = x; " +
    string.Concat(Enumerable.Repeat("word = word * y + x; ", statements)) + "return word; } ";
// A body with a call at every statement, to measure what its link table and link facts cost.
string Calling(string name, int calls) =>
    $"public static ulong {name}(ulong x, ulong y) {{ ulong word = x; " +
    string.Concat(Enumerable.Repeat("word = Step(word, y); ", calls)) + "return word; } ";
// A long body with two calls, where the link table stays the same size as the body grows.
string Sparse(string name, int statements) =>
    $"public static ulong {name}(ulong x, ulong y) {{ ulong word = Step(x, y); " +
    string.Concat(Enumerable.Repeat("word = word * y + x; ", statements)) +
    "word = Step(word, y); return word; } ";
File.WriteAllText(Path.Combine(source, "Lookups.cs"), "public static class Lookups { " +
    Method("Short", ShortStatements) + Method("Long", LongStatements) +
    "public static ulong Step(ulong a, ulong b) { return a * b + a; } " +
    Calling("Few", FewCalls) + Calling("Many", ManyCalls) +
    Sparse("SparseShort", SparseShortStatements) + Sparse("SparseLong", SparseLongStatements) + "}");
Run(["dotnet", "build", Path.Combine(source, "Lookups.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Lookups.dll");

const string Report = "\n#eval show IO Nat from IO.getNumHeartbeats\n";

// Heartbeats count the elaborator's and the kernel's work on one thread, so they repeat exactly
// where compile time varies with the machine's load.
long Heartbeats(string path, string text, bool equations = true)
{
    File.WriteAllText(path, text + Report);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException("Untrusted lookup equations: " + path);
    var count = Regex.Match(output, @"(?m)^([0-9]+)\r?$");
    if (!count.Success) throw new InvalidOperationException("Missing heartbeat count:\n" + output);
    // Each file reports the last equation's axioms once; a report per equation would walk the body each time.
    if (equations && Regex.Matches(output, @"_instruction[0-9]+' depends on axioms: \[propext\]").Count != 1)
        throw new InvalidOperationException("Instruction equations must depend on propext alone:\n" + output);
    return long.Parse(count.Groups[1].Value, CultureInfo.InvariantCulture);
}

// The last pc is the farthest from the head of the code list. Its equation must keep the statement
// stepping tactics rewrite with, depend on `propext` alone, and still be fetched by `cil_code`.
long Checked(string path, string text, string binder, string method, string equation, int last)
{
    var statement = $"example {binder}: {method}.code[{last}]? = some CIL.Instruction.ret";
    return Heartbeats(path, text + $"""

        {statement} := {equation}
        {statement} := by simp only [cil_code]
        """);
}

// The three places `cil_instruction_equations` states lookup equations for one method: its extraction, a
// hand-written body with a parameter, and the shared template of the extraction.
(int Instructions, long[] Heartbeats) Measure(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    const string Header = "def method0 : Method := { profile := profile,";
    // The definition lists one instruction per line after its header.
    var definition = Regex.Match(extracted, @"(?m)^" + Regex.Escape(Header) + @"[^\r\n]*(\r?\n  [^\r\n]*)+");
    var depth = Regex.Match(extracted, @"(?m)^set_option maxRecDepth [0-9]+");
    if (!definition.Success || !depth.Success ||
        !Regex.IsMatch(extracted, @"(?m)^cil_instruction_equations method0\r?$"))
        throw new InvalidOperationException($"Missing the definition, equations or recursion depth of {name}.");
    var instructions = definition.Groups[1].Captures.Count;
    var last = instructions - 1;
    var extraction = Checked(Path.Combine(output, "Measured.lean"),
        extracted + $"\n#print axioms Extracted.method0_instruction{last}\n",
        "", "Extracted.method0", $"Extracted.method0_instruction{last}", last);
    const string Binder = "(profile : CIL.FeatureProfile) (environment : CIL.LayoutEnvironment) ";
    var body = "def method0 (profile : FeatureProfile) (environment : LayoutEnvironment) : Method :=" +
        " { profile := profile," +
        definition.Value[Header.Length..];
    var command = Checked(Path.Combine(output, "Body.lean"), $"""
        import CIL.InstructionEquations

        namespace Body
        open CIL
        {depth.Value}
        {body}
        cil_instruction_equations method0
        #print axioms method0_instruction{last}
        end Body
        """, Binder, "(Body.method0 profile environment)",
        $"Body.method0_instruction{last} profile environment", last);

    var shared = Path.Combine(output, "Shared");
    Run(["dotnet", ExtractorPath, "templates", shared, output]);
    var templates = File.ReadAllText(Path.Combine(shared, "Templates.lean"));
    if (!templates.Contains("cil_instruction_equations method0", StringComparison.Ordinal))
        throw new InvalidOperationException($"The template of {name} has no instruction equations.");
    var template = Checked(Path.Combine(shared, "Measured.lean"), templates,
        Binder, "(Templates.method0 profile environment)",
        $"Templates.method0_instruction{last} profile environment", last);
    return (instructions, [extraction, command, template]);
}

var imports = Path.Combine(directory, "Imports.lean");
var floor = Heartbeats(imports, "import CIL.Extraction.Translation\nimport CIL.SymbolicExecution\n" +
    "import CIL.Safety.Execution\nimport CIL.InstructionEquations\n", equations: false);
var brief = Measure("Short");
var extended = Measure("Long");
if (brief.Instructions < 500 || extended.Instructions < 4 * brief.Instructions - 8)
    throw new InvalidOperationException(
        $"Expected about 500 and 2,000 instructions; found {brief.Instructions} and {extended.Instructions}.");
Console.WriteLine($"PASS {extended.Instructions} instructions compile at the emitted recursion depth");
string[] producers = ["an extracted method", "a cil_instruction_equations body", "a generated template"];
for (var producer = 0; producer < producers.Length; producer++)
{
    double Cost((int Instructions, long[] Heartbeats) run) =>
        (double)(run.Heartbeats[producer] - floor) / run.Instructions;
    var growth = Cost(extended) / Cost(brief);
    var measured = string.Create(CultureInfo.InvariantCulture,
        $"{Cost(brief):F0} heartbeats per instruction at {brief.Instructions} instructions and " +
        $"{Cost(extended):F0} at {extended.Instructions}, {growth:F2} times as many");
    if (growth > AllowedGrowth)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Compiling {producers[producer]} costs {measured}; the limit is {AllowedGrowth}."));
    Console.WriteLine($"PASS compiling {producers[producer]} costs {measured}");
}

// The extraction of a body with many calls: its link table, link index, per-site facts and the checks that
// tie them together must each cost the same per call site at four times the size.
long CallingCost(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    return Heartbeats(Path.Combine(output, "Measured.lean"), File.ReadAllText(Path.Combine(output, "Extracted.lean")),
        equations: false);
}
var fewCost = (double)(CallingCost("Few") - floor) / FewCalls;
var manyCost = (double)(CallingCost("Many") - floor) / ManyCalls;
var callGrowth = manyCost / fewCost;
var callsMeasured = string.Create(CultureInfo.InvariantCulture,
    $"{fewCost:F0} heartbeats per call at {FewCalls} calls and {manyCost:F0} at {ManyCalls}, " +
    $"{callGrowth:F2} times as many");
if (callGrowth > AllowedCallGrowth)
    throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
        $"Extracting a body with many calls costs {callsMeasured}; the limit is {AllowedCallGrowth}."));
Console.WriteLine($"PASS extracting a body with many calls costs {callsMeasured}");

// The kernel heartbeats to recheck the proof that `written` embeds into `extraction`, both defined by
// `definitions`. The two link tables differ and their call sites sit at different pcs, so the kernel cannot close
// the link clause by comparing equal arguments: it must read both tables, and a read that scans the table per
// call grows with the call count. `cil_embed` states the proof as an auxiliary lemma, so that lemma is rechecked.
long EmbeddingCost(string name, string definitions)
{
    var path = Path.Combine(directory, name + ".lean");
    File.WriteAllText(path, $$"""
        import CIL.Embedding.Tactic
        set_option maxHeartbeats 0
        set_option maxRecDepth 100000
        open CIL
        namespace Embedded
        {{definitions}}
        theorem embeds : MethodEmbeds [extraction] 0 written := by cil_embed
        end Embedded
        open Lean in
        run_cmd do
          let env ← getEnv
          let some (.thmInfo declaration) := env.find? `Embedded.embeds | throwError "missing"
          let start ← IO.getNumHeartbeats
          let mut count : Nat := 0
          for name in declaration.value.getUsedConstants do
            let some (.thmInfo used) := env.find? name | continue
            let copy : Declaration := .thmDecl { used with name := name ++ `recheck }
            match env.toKernelEnv.addDeclCore 0 1000000 copy none with
            | .ok _ => count := count + 1
            | .error _ => throwError "Kernel rejected the recheck of {name}"
          let beats := (← IO.getNumHeartbeats) - start
          logInfo m!"{count} lemmas rechecked, {beats} kernel heartbeats"
        """ + "\n");
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var cost = LookupPatterns.EmbeddingRecheck().Match(output);
    if (!cost.Success || cost.Groups[1].Value == "0")
        throw new InvalidOperationException("Missing the embedding recheck cost:\n" + output);
    return long.Parse(cost.Groups[2].Value, CultureInfo.InvariantCulture);
}

// A hand-written body embedded into an extraction with a dead block after each return.
string DeadBlocks(int calls) => $$"""
/-- What an extraction emits for one call followed by a dead block. -/
def extractedSegment : List Instruction :=
  [.arg 0, .call 1 1, .pop, .ret, .unsupported "Unreachable under selected profile"]
/-- The hand-written segment without the dead block. -/
def writtenSegment : List Instruction := [.arg 0, .call 1 1, .pop, .ret]
/-- The extraction, whose calls sit at pcs 1, 6, 11 and so on. -/
def extraction : Method :=
  { locals := [], returnsValue := false,
    code := (List.replicate {{calls}} extractedSegment).flatten ++ [.ret] }
/-- The proof's body, built with the links its own code implies, with calls at pcs 1, 5, 9. -/
def written : Method :=
  extraction.withCode ((List.replicate {{calls}} writtenSegment).flatten ++ [.ret])
""";

// A body whose head branches over its first block to its second, embedded into an extraction that places the
// second block first, so the pc map descends once at every size.
string Reordered(int segments) => $$"""
/-- The block after the head. -/
def first : List Instruction := [.arg 0, .call 1 1, .pop, .ret]
/-- The block the head branches to. -/
def second : List Instruction := [.arg 1, .call 2 1, .pop, .ret]
/-- The extraction, with the second block first. -/
def extraction : Method :=
  { locals := [], returnsValue := false,
    code := [.br 1] ++ (List.replicate {{segments}} second).flatten ++
      (List.replicate {{segments}} first).flatten ++ [.ret] }
/-- The proof's body, with the blocks in source order. -/
def written : Method :=
  extraction.withCode ([.br {{1 + 4 * segments}}] ++ (List.replicate {{segments}} first).flatten ++
    (List.replicate {{segments}} second).flatten ++ [.ret])
#guard let map := (MethodBinding.alignLive written.code.toArray extraction.code.toArray).toList
  (map.zip map.tail).countP (fun (left, right) => right < left) == 1
""";

// Fails when a fixture at the larger size costs more per call to embed than the allowed growth.
void CheckEmbeddingGrowth(string fixture, string description, Func<int, string> definitions, int callsPerSize,
    int few, int many)
{
    double Cost(int size) => (double)EmbeddingCost(fixture + size, definitions(size)) / (callsPerSize * size);
    var fewCost = Cost(few);
    var manyCost = Cost(many);
    var growth = manyCost / fewCost;
    var measured = string.Create(CultureInfo.InvariantCulture,
        $"{fewCost:F0} kernel heartbeats per call at {callsPerSize * few} calls and {manyCost:F0} at " +
        $"{callsPerSize * many}, {growth:F2} times as many");
    if (growth > AllowedEmbedGrowth)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Embedding {description} costs {measured}; the limit is {AllowedEmbedGrowth}."));
    Console.WriteLine($"PASS embedding {description} costs {measured}");
}
CheckEmbeddingGrowth("Embedding", "a body with many calls", DeadBlocks, 1, EmbedFewCalls, EmbedManyCalls);
CheckEmbeddingGrowth("Reordered", "a body whose blocks the extraction reorders", Reordered, 2,
    ReorderFewSegments, ReorderManySegments);

// The text a method emits for its links and the kernel heartbeats to recheck its link index, for a body
// with two calls: both depend on the calls, not on the length of the body.
(long Bytes, long Heartbeats) SparseLinkCost(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var linkLines = extracted.Split('\n').Where(line => LookupPatterns.LinkLine().IsMatch(line))
        .Sum(line => (long)line.Length + 1);
    if (linkLines == 0) throw new InvalidOperationException("The extraction of " + name + " has no link output.");
    var path = Path.Combine(output, "LinkIndex.lean");
    File.WriteAllText(path, extracted + """

        open Lean in
        run_cmd do
          let env ← getEnv
          let some (.thmInfo declaration) := env.find? `Extracted.method0_linkIndex_valid
            | throwError "missing the link index check"
          let start ← IO.getNumHeartbeats
          let copy : Declaration := .thmDecl { declaration with name := declaration.name ++ `recheck }
          match env.toKernelEnv.addDeclCore 0 1000000 copy none with
          | .ok _ => pure ()
          | .error _ => throwError "Kernel rejected the link index check"
          logInfo m!"{(← IO.getNumHeartbeats) - start} kernel heartbeats"
        """ + "\n");
    var report = Run(["lake", "env", "lean", path], cwd: FixturePackage());
    var beats = LookupPatterns.KernelHeartbeats().Match(report);
    if (!beats.Success) throw new InvalidOperationException("Missing the link index recheck cost:\n" + report);
    return (linkLines, long.Parse(beats.Groups[1].Value, CultureInfo.InvariantCulture));
}
var sparseShort = SparseLinkCost("SparseShort");
var sparseLong = SparseLinkCost("SparseLong");
var sparseMeasured = $"{sparseShort.Bytes} link bytes and {sparseShort.Heartbeats} kernel heartbeats at " +
    $"{SparseShortStatements} statements, {sparseLong.Bytes} and {sparseLong.Heartbeats} at {SparseLongStatements}";
if (sparseLong.Bytes > sparseShort.Bytes * 1.1 || sparseLong.Heartbeats > sparseShort.Heartbeats * AllowedCallGrowth)
    throw new InvalidOperationException("A longer body with the same calls emits more link output: " + sparseMeasured);
Console.WriteLine("PASS link output and index check of a body with two calls do not grow with the body: " +
    sparseMeasured);

// Subtract the same generated body's cost to isolate computed lookup from equation generation.
long ComputedLookupCost(int cases)
{
    var header = $$"""
        import CIL.InstructionEquations
        import CIL.Safety.SymbolicExecution
        open CIL.Safety
        def segment : List CIL.Instruction := [.arg 0, .arg 1, .add, .nop, .nop, .nop, .nop]
        def body : CIL.Method :=
          { locals := [], returnsValue := true,
            code := [.nop] ++ (List.replicate {{cases}} segment).flatten ++ [.ret] }
        cil_instruction_equations body
        """ + "\n";
    var path = Path.Combine(directory, "Computed" + cases + ".lean");
    var generated = Heartbeats(path, header, equations: false);
    var checkedLookup = Heartbeats(path, header + $$"""
        /-- Each repeated segment has its addition at the same relative offset. -/
        theorem fetched (index : Fin {{cases}}) : body.code[1 + 7 * index.val + 2]? = some .add := by
          cil_lookup []
        #print axioms fetched
        """ + "\n", equations: false);
    return checkedLookup - generated;
}
var fourCaseCost = ComputedLookupCost(4) / 4.0;
var sixteenCaseCost = ComputedLookupCost(16) / 16.0;
Console.WriteLine(FormattableString.Invariant(
    $"PASS computed lookup: {fourCaseCost:F0} heartbeats/case at 4; {sixteenCaseCost:F0} at 16"));
if (sixteenCaseCost > fourCaseCost * AllowedGrowth)
    throw new Exception("Computed lookup cost per case grows with the segment count.");

// The kernel heartbeats of the scalar certificate of a body whose segments each address an array element, with
// or without a `readonly.` prefix, and branch to the next segment, less those of stating the same certificate.
long ArrayAddressCost(bool prefixed, int sites)
{
    var flag = prefixed ? "true" : "false";
    var header = $$"""
        import CIL.Extraction.Scalars
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace ArrayAddresses
        open CIL CIL.Extraction
        def intType : TypeExpr := .atom runtimeScope "System.Int32"
        def width (prefixed : Bool) : Nat := if prefixed then 6 else 5
        def segment (prefixed : Bool) (index : Nat) : List RawInstruction :=
          [⟨0, 2, .none⟩, ⟨0, 3, .none⟩] ++ (if prefixed then [⟨0, 65054, .none⟩] else []) ++
            [⟨0, 143, .type intType⟩, ⟨0, 38, .none⟩, ⟨0, 43, .target ((index + 1) * width prefixed)⟩]
        def raw (prefixed : Bool) (sites : Nat) : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
          callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
          parameters := [.array intType, intType], locals := [], initLocals := true, maxStack := 2,
          genericParameters := [],
          code := (List.range sites).flatMap (segment prefixed) ++ [⟨0, 42, .none⟩] }
        def featureSegment (prefixed : Bool) : FeatureCertificate :=
          [some ⟨[], []⟩, some ⟨[none], []⟩] ++
            (if prefixed then [some ⟨[none, none], []⟩] else []) ++
            [some ⟨[none, none], []⟩, some ⟨[none], []⟩, some ⟨[], []⟩]
        def features (prefixed : Bool) (sites : Nat) : FeatureCertificate :=
          (List.replicate sites (featureSegment prefixed)).flatten ++ [some ⟨[], []⟩]
        def stateSegment (prefixed : Bool) : ScalarCertificate :=
          [some [], some [.array .signed32]] ++
            (if prefixed then [some [.word32, .array .signed32]] else []) ++
            [some [.word32, .array .signed32], some [.reference], some []]
        def states (prefixed : Bool) (sites : Nat) : ScalarCertificate :=
          (List.replicate sites (stateSegment prefixed)).flatten ++ [some []]
        def codeSegment (prefixed : Bool) (index : Nat) : List Instruction :=
          [.arg 0, .arg 1] ++ (if prefixed then [.nop] else []) ++
            [.memory (.arrayAddress .signed32 !prefixed), .pop, .br ((index + 1) * width prefixed)]
        def code (prefixed : Bool) (sites : Nat) : List Instruction :=
          (List.range sites).flatMap (codeSegment prefixed) ++ [.ret]
        """ + "\n";
    var statement = $"ScalarFlowValid #[] (raw {flag} {sites}) (features {flag} {sites}) " +
        $"(states {flag} {sites}) (code {flag} {sites})";
    var path = Path.Combine(directory, $"ArrayAddresses{(prefixed ? "Prefixed" : "")}{sites}.lean");
    var stated = Heartbeats(path, header + $"example : Prop := {statement}\nend ArrayAddresses\n", equations: false);
    var decided = Heartbeats(path, header + $"""
        theorem valid : {statement} := by decide +kernel
        #print axioms valid
        end ArrayAddresses
        """ + "\n", equations: false);
    return decided - stated;
}
foreach (var prefixed in new[] { false, true })
{
    var label = prefixed ? "readonly element addresses" : "element addresses";
    var perSite = new[] { FewAddresses, MoreAddresses, ManyAddresses }
        .Select(sites => (Sites: sites, Cost: (double)ArrayAddressCost(prefixed, sites) / sites)).ToArray();
    var addressesMeasured = string.Join("; ", perSite.Select(run =>
        string.Create(CultureInfo.InvariantCulture, $"{run.Cost:F0} kernel heartbeats per address at {run.Sites}")));
    if (perSite.Skip(1).Any(run => run.Cost > perSite[0].Cost * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking the scalar certificate of {label} costs {addressesMeasured}; the limit is {AllowedGrowth} " +
            $"times the cost per address at {FewAddresses}."));
    Console.WriteLine($"PASS checking the scalar certificate of {label} costs {addressesMeasured}");
}

// The kernel heartbeats of the feature certificate of a body that loads, stores and addresses four int32 locals in
// turn, popping each address, less those of stating the same certificate. A local load, store or address checks
// its opcode and index alone.
long LocalAccessCost(int accesses)
{
    var cycles = accesses / 4;
    var header = $$"""
        import CIL.Extraction.Features
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace LocalAccesses
        open CIL CIL.Extraction
        def intType : TypeExpr := .atom runtimeScope "System.Int32"
        def localCount : Nat := 4
        def segment (index : Nat) : List RawInstruction :=
          [⟨0, 17, .local (index % localCount)⟩, ⟨0, 19, .local ((index + 1) % localCount)⟩,
            ⟨0, 18, .local ((index + 2) % localCount)⟩, ⟨0, 38, .none⟩]
        def raw (cycles : Nat) : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
          callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
          parameters := [], locals := List.replicate localCount intType, initLocals := true,
          maxStack := 1, genericParameters := [],
          code := (List.range cycles).flatMap segment ++ [⟨0, 42, .none⟩] }
        def unknown : List (Option W32) := List.replicate localCount none
        def features (cycles : Nat) : FeatureCertificate :=
          (List.replicate cycles [some ⟨[], unknown⟩, some ⟨[none], unknown⟩, some ⟨[], unknown⟩,
            some ⟨[none], unknown⟩]).flatten ++ [some ⟨[], unknown⟩]
        def codeSegment (index : Nat) : List Instruction :=
          [.local (index % localCount), .setLocal ((index + 1) % localCount),
            .localAddr ((index + 2) % localCount), .pop]
        def code (cycles : Nat) : List Instruction := (List.range cycles).flatMap codeSegment ++ [.ret]
        """ + "\n";
    var statement = $"FeatureFlowValid #[] (fun _ => none) (raw {cycles}) .scalar (features {cycles}) " +
        $"(List.replicate {accesses + 1} true) (code {cycles})";
    var path = Path.Combine(directory, $"LocalAccesses{accesses}.lean");
    var stated = Heartbeats(path, header + $"example : Prop := {statement}\nend LocalAccesses\n", equations: false);
    var decided = Heartbeats(path, header + $"""
        theorem valid : {statement} := by decide +kernel
        #print axioms valid
        end LocalAccesses
        """ + "\n", equations: false);
    return decided - stated;
}
var perAccess = new[] { FewLocalAccesses, MoreLocalAccesses, ManyLocalAccesses }
    .Select(accesses => (Accesses: accesses, Cost: (double)LocalAccessCost(accesses) / accesses)).ToArray();
var accessesMeasured = string.Join("; ", perAccess.Select(run =>
    string.Create(CultureInfo.InvariantCulture,
        $"{run.Cost:F0} kernel heartbeats per instruction at {run.Accesses}")));
if (perAccess.Skip(1).Any(run => run.Cost > perAccess[0].Cost * AllowedGrowth))
    throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
        $"Checking the feature certificate of local loads, stores and addresses costs {accessesMeasured}; " +
        $"the limit is {AllowedGrowth} times the cost per instruction at {FewLocalAccesses}."));
Console.WriteLine(
    $"PASS checking the feature certificate of local loads, stores and addresses costs {accessesMeasured}");
// The kernel heartbeats of a check over a body that stores each of its locals once and then loads or addresses
// it, less those of stating the same check. Integer locals take a constant and are popped after a load or after
// `ldloca`, which also names each as a receiver fold candidate; native-int locals take a method address and are
// consumed by `calli`, which makes each a pointer local. The check is the scalar certificate, or for pointer
// locals also the closed argument storage.
long LocalSlotCost(LocalSlots slots, int count, bool storage = false)
{
    var pointers = slots == LocalSlots.Pointer;
    var addressed = slots == LocalSlots.Addressed;
    var slotType = pointers ? "System.IntPtr" : "System.Int32";
    var kind = pointers ? ".methodPointer signature" : ".word32";
    var push = pointers ? "⟨0, 65030, .call handler⟩" : "⟨0, 22, .none⟩";
    var load = addressed ? "⟨0, 18, .local index⟩" : "⟨0, 17, .local index⟩";
    var consume = pointers ? "⟨0, 41, .indirectCall .void [] false false 0⟩" : "⟨0, 38, .none⟩";
    var loaded = addressed ? ".reference" : "kind";
    var pushed = pointers ? ".managed (.address ⟨⟨\"Scaling\", 2, []⟩, 0⟩ signature)" : ".ldc_i4 0";
    var emittedLoad = addressed ? ".localAddr index" : ".local index";
    var consumed = pointers ? ".managed (.call signature [] false)" : ".pop";
    var header = $$"""
        import CIL.Extraction.Scalars
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace LocalSlots
        open CIL CIL.Extraction
        def slotType : TypeExpr := .atom runtimeScope "{{slotType}}"
        def handler : CallSite :=
          { target := .managed 2, typeArguments := [], parameterCount := 0, hasThis := false,
            returnsValue := false }
        def signature : ManagedSignature := ⟨.void, []⟩
        def kind : ScalarKind := {{kind}}
        def segment (index : Nat) : List RawInstruction :=
          [{{push}}, ⟨0, 19, .local index⟩, {{load}}, {{consume}}]
        def raw (slots : Nat) : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
          callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
          parameters := [], locals := List.replicate slots slotType, initLocals := true, maxStack := 1,
          genericParameters := [],
          code := (List.range slots).flatMap segment ++ [⟨0, 42, .none⟩] }
        def features (slots : Nat) : FeatureCertificate :=
          (List.replicate slots [some ⟨[], []⟩, some ⟨[none], []⟩, some ⟨[], []⟩, some ⟨[none], []⟩]).flatten ++
            [some ⟨[], []⟩]
        def states (slots : Nat) : ScalarCertificate :=
          (List.replicate slots [some [], some [kind], some [], some [{{loaded}}]]).flatten ++ [some []]
        def codeSegment (index : Nat) : List Instruction :=
          [{{pushed}}, .setLocal index, {{emittedLoad}}, {{consumed}}]
        def code (slots : Nat) : List Instruction := (List.range slots).flatMap codeSegment ++ [.ret]
        """ + "\n";
    var statement = storage ? $"(closedArguments [] (raw {count})).isSome = true"
        : $"ScalarFlowValid #[] (raw {count}) (features {count}) (states {count}) (code {count})";
    var path = Path.Combine(directory, $"{slots}{(storage ? "Storage" : "Locals")}{count}.lean");
    var stated = Heartbeats(path, header + $"example : Prop := {statement}\nend LocalSlots\n", equations: false);
    var decided = Heartbeats(path, header + $"""
        theorem valid : {statement} := by decide +kernel
        #print axioms valid
        end LocalSlots
        """ + "\n", equations: false);
    return decided - stated;
}
(LocalSlots Slots, bool Storage, string Label)[] localChecks =
[
    (LocalSlots.Integer, false, "the scalar certificate of integer locals"),
    (LocalSlots.Addressed, false, "the scalar certificate of addressed integer locals"),
    (LocalSlots.Pointer, false, "the scalar certificate of native-int locals consumed by calli"),
    (LocalSlots.Pointer, true, "the closed argument storage of native-int locals consumed by calli"),
];
foreach (var (slots, storage, label) in localChecks)
{
    // Each local is stored once and loaded or addressed once, between a push and a pop or call; `ret` ends the body.
    var perInstruction = new[] { FewLocals, MoreLocals, ManyLocals }
        .Select(count => (Count: count, Cost: (double)LocalSlotCost(slots, count, storage) / (4 * count + 1)))
        .ToArray();
    var localsMeasured = string.Join("; ", perInstruction.Select(run => string.Create(CultureInfo.InvariantCulture,
        $"{run.Cost:F0} kernel heartbeats per instruction at {run.Count} locals")));
    if (perInstruction.Skip(1).Any(run => run.Cost > perInstruction[0].Cost * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking {label} costs {localsMeasured}; the limit is {AllowedGrowth} " +
            $"times the cost per instruction at {FewLocals} locals."));
    Console.WriteLine($"PASS checking {label} costs {localsMeasured}");
}

/// <summary>How the generated bodies of the local slot checks use each local.</summary>
enum LocalSlots
{
    /// <summary>An int32 local that takes a constant and is loaded and popped.</summary>
    Integer,
    /// <summary>An int32 local that takes a constant and whose address is taken and popped.</summary>
    Addressed,
    /// <summary>A native-int local that takes a method address and is loaded by `calli`.</summary>
    Pointer,
}

/// <summary>The patterns that read the cost reports and the link output of the fixtures above.</summary>
static partial class LookupPatterns
{
    [GeneratedRegex(@"([0-9]+) lemmas rechecked, ([0-9]+) kernel heartbeats")]
    internal static partial Regex EmbeddingRecheck();

    [GeneratedRegex(@"([0-9]+) kernel heartbeats")]
    internal static partial Regex KernelHeartbeats();

    [GeneratedRegex(@"^(@\[cil_code\] )?(def method0Link|theorem method0_link)")]
    internal static partial Regex LinkLine();

    [GeneratedRegex(@"\b((?:un)?equal [0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex TypeDecision();
}
