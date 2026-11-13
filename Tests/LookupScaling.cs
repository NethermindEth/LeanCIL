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
// The recheck of an embedding with a link scan per call grows by about 1.9 times per doubling and a body of
// 1,024 calls exhausts the kernel's stack, so these sizes separate it from the one-pass read.
const int EmbedFewCalls = 256;
const int EmbedManyCalls = 1024;
// Two calls in bodies of these many statements: the link output must not grow with the body.
const int SparseShortStatements = 250;
const int SparseLongStatements = 1000;
// Four times the call sites may cost at most this much more per call site.
const double AllowedCallGrowth = 1.35;

var directory = At("artifacts/LookupScaling");
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

// The kernel heartbeats to recheck the proof that a hand-written body embeds into an extraction with a dead
// block before each of its many calls. The two link tables differ and their call sites sit at different pcs, so
// the kernel cannot close the link clause by comparing equal arguments: it must read both tables, and a read
// that scans the table per call grows with the call count. `cil_embed` states the proof as an auxiliary lemma,
// so that lemma is rechecked.
long EmbeddingCost(int calls)
{
    var path = Path.Combine(directory, "Embedding" + calls + ".lean");
    File.WriteAllText(path, $$"""
        import CIL.Embedding.Tactic
        set_option maxHeartbeats 0
        set_option maxRecDepth 100000
        open CIL
        namespace Embedded
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
    var output = Run(["lake", "env", "lean", path], cwd: FixturePackage());
    var cost = LookupPatterns.EmbeddingRecheck().Match(output);
    if (!cost.Success || cost.Groups[1].Value == "0")
        throw new InvalidOperationException("Missing the embedding recheck cost:\n" + output);
    return long.Parse(cost.Groups[2].Value, CultureInfo.InvariantCulture);
}
var embedFewCost = (double)EmbeddingCost(EmbedFewCalls) / EmbedFewCalls;
var embedManyCost = (double)EmbeddingCost(EmbedManyCalls) / EmbedManyCalls;
var embedGrowth = embedManyCost / embedFewCost;
var embedMeasured = string.Create(CultureInfo.InvariantCulture,
    $"{embedFewCost:F0} kernel heartbeats per call at {EmbedFewCalls} calls and {embedManyCost:F0} at " +
    $"{EmbedManyCalls}, {embedGrowth:F2} times as many");
if (embedGrowth > AllowedCallGrowth)
    throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
        $"Embedding a body with many calls costs {embedMeasured}; the limit is {AllowedCallGrowth}."));
Console.WriteLine($"PASS embedding a body with many calls costs {embedMeasured}");

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

/// <summary>The patterns that read the cost reports and the link output of the fixtures above.</summary>
static partial class LookupPatterns
{
    [GeneratedRegex(@"([0-9]+) lemmas rechecked, ([0-9]+) kernel heartbeats")]
    internal static partial Regex EmbeddingRecheck();

    [GeneratedRegex(@"([0-9]+) kernel heartbeats")]
    internal static partial Regex KernelHeartbeats();

    [GeneratedRegex(@"^(@\[cil_code\] )?(def method0Link|theorem method0_link)")]
    internal static partial Regex LinkLine();
}
