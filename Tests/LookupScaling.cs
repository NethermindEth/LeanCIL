#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include GeneratedEvidence.cs

using System.Globalization;
using System.Text.RegularExpressions;

// `cil_instruction_equations` proves each equation from the code suffix that starts its block. Proved
// against the whole code list instead, it walks one cell per preceding instruction and a method's equations
// cost quadratic time, which this fixture reports as a per-instruction cost that grows with the method.
const int ShortStatements = 125;
const int LongStatements = 500;
// Compiling four times the instructions may cost at most this much more per instruction.
const double AllowedGrowth = 1.25;

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
File.WriteAllText(Path.Combine(source, "Lookups.cs"), "public static class Lookups { " +
    Method("Short", ShortStatements) + Method("Long", LongStatements) + "}");
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
    const string Binder = "(profile : CIL.FeatureProfile) ";
    var body = "def method0 (profile : FeatureProfile) : Method := { profile := profile," +
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
        """, Binder, "(Body.method0 profile)", $"Body.method0_instruction{last} profile", last);

    var shared = Path.Combine(output, "Shared");
    Run(["dotnet", ExtractorPath, "templates", shared, output]);
    var templates = File.ReadAllText(Path.Combine(shared, "Templates.lean"));
    if (!templates.Contains("cil_instruction_equations method0", StringComparison.Ordinal))
        throw new InvalidOperationException($"The template of {name} has no instruction equations.");
    var template = Checked(Path.Combine(shared, "Measured.lean"), templates,
        Binder, "(Templates.method0 profile)", $"Templates.method0_instruction{last} profile", last);
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

// Each distinct metadata token of a body adds a row lookup and a decode to the kernel's metadata check, so the cost per
// token may not grow with the number of tokens, whichever table the token names: user strings, instance fields of a
// class, and methods (whose count also grows the number of methods of the extraction and so the metadata carried).
const int FewTokens = 125;
const int ManyTokens = 500;
// Each called method is an extracted method with a certificate of its own, and composing the certificate of an
// extraction of about 500 methods exceeds the default heartbeat budget, so the call counts stay below that.
const int FewCalls = 25;
const int ManyCalls = 100;
var tokenSource = Path.Combine(directory, "TokenAssembly");
Directory.CreateDirectory(tokenSource);
File.WriteAllText(Path.Combine(tokenSource, "Tokens.csproj"), """
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
</Project>
""");
string Join(int count, Func<int, string> piece) => string.Concat(Enumerable.Range(0, count).Select(piece));
string StringMethod(int count, string name) =>
    $"public static ulong {name}(ulong x) {{ " + Join(count, index => $"Use(\"{name}{index}\"); ") + "return x; } ";
string FieldMethod(int count, string name) =>
    $"public static ulong {name}(Wide{count} w) {{ return 0UL" + Join(count, index => $" + w.F{index}") + "; } " +
    $"public sealed class Wide{count} {{ " + Join(count, index => $"public ulong F{index}; ") + "} ";
string CallMethod(int count, string name) =>
    $"public static ulong {name}(ulong x) {{ " + Join(count, index => $"x = {name}{index}(x); ") + "return x; } " +
    Join(count, index => $"static ulong {name}{index}(ulong x) => x + {index + 1}UL; ");
File.WriteAllText(Path.Combine(tokenSource, "Tokens.cs"),
    "public static class Tokens { public static void Use(string text) { } " +
    StringMethod(FewTokens, "StringsFew") + StringMethod(ManyTokens, "StringsMany") +
    FieldMethod(FewTokens, "FieldsFew") + FieldMethod(ManyTokens, "FieldsMany") +
    CallMethod(FewCalls, "CallsFew") + CallMethod(ManyCalls, "CallsMany") + "}");
Run(["dotnet", "build", Path.Combine(tokenSource, "Tokens.csproj"), "-c", "Release"]);
var tokenAssembly = Path.Combine(tokenSource, "bin/Tokens.dll");
double TokenCost(string name, string selector, int count, string distinctPattern)
{
    var output = Path.Combine(directory, "Tokens" + name);
    Run(Extract("extract", tokenAssembly, "Tokens", selector, output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var distinct = Regex.Matches(extracted, distinctPattern).Count;
    if (distinct < count)
        throw new InvalidOperationException($"Expected {count} distinct tokens in {name}; found {distinct}.");
    return (double)(Heartbeats(Path.Combine(output, "Measured.lean"), extracted, equations: false) - floor) / count;
}
foreach (var (kind, few, many, pattern, fewCount, manyCount) in new[]
{
    ("Strings", "Tokens::StringsFew(ulong)", "Tokens::StringsMany(ulong)", @"\(\d+, \.text ""[^""]*""\)", FewTokens, ManyTokens),
    ("Fields", $"Tokens::FieldsFew(Tokens/Wide{FewTokens})", $"Tokens::FieldsMany(Tokens/Wide{ManyTokens})",
        @"\(\d+, \.field ", FewTokens, ManyTokens),
    ("Calls", "Tokens::CallsFew(ulong)", "Tokens::CallsMany(ulong)", @"\(\d+, \.call ", FewCalls, ManyCalls)
})
{
    var tokenGrowth = TokenCost(kind + "Many", many, manyCount, pattern) /
        TokenCost(kind + "Few", few, fewCount, pattern);
    Console.WriteLine(string.Create(CultureInfo.InvariantCulture,
        $"PASS metadata check of {fewCount} and {manyCount} distinct {kind.ToLowerInvariant()} tokens: " +
        $"{tokenGrowth:F2} times the cost per token"));
    if (tokenGrowth > AllowedGrowth)
        throw new Exception(string.Create(CultureInfo.InvariantCulture,
            $"Checking {manyCount} {kind.ToLowerInvariant()} tokens costs {tokenGrowth:F2} times as much per token " +
            $"as {fewCount}; the limit is {AllowedGrowth}."));
}

// One method's body check reads its module's literal lookup tables by name, so its kernel cost is its own body and
// tokens times a logarithm: independent of the number of methods in the extraction and of the rows its module carries.
const double AllowedBodyGrowth = 1.35;
int[] chainLengths = [8, 32, 128];
int[] bulkSizes = [125, 500];
var bodySource = Path.Combine(directory, "BodyAssembly");
Directory.CreateDirectory(bodySource);
File.WriteAllText(Path.Combine(bodySource, "Bodies.csproj"), File.ReadAllText(Path.Combine(tokenSource, "Tokens.csproj")));
string Chain(int count) =>
    $"public static ulong Chain{count}(ulong x) {{ " + Join(count, index => $"x = Chain{count}_{index}(x); ") + "return x; } " +
    Join(count, index => $"static ulong Chain{count}_{index}(ulong x) => x + {index + 1}UL; ");
string Rows(int count) =>
    $"public static ulong Rows{count}(ulong x) {{ x = Small{count}(x); return Bulk{count}(x); }} " +
    $"static ulong Small{count}(ulong x) => x + 1UL; " +
    $"static ulong Bulk{count}(ulong x) {{ " + Join(count, index => $"Use(\"r{count}_{index}\"); ") + "return x; } ";
File.WriteAllText(Path.Combine(bodySource, "Bodies.cs"), "public static class Bodies { public static void Use(string text) { } " +
    string.Concat(chainLengths.Select(Chain)) + string.Concat(bulkSizes.Select(Rows)) + "}");
Run(["dotnet", "build", Path.Combine(bodySource, "Bodies.csproj"), "-c", "Release"]);
var bodyAssembly = Path.Combine(bodySource, "bin/Bodies.dll");
// Heartbeats of the method's `method{n}_body_validated`, less the same file with its proof left open.
long BodyCheck(string name, string entry, string method)
{
    var output = Path.Combine(directory, "Body" + name);
    Run(Extract("extract", bodyAssembly, "Bodies", $"Bodies::{entry}(ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var number = Regex.Match(extracted, @"def method(\d+)Signature : String := ""[^""]*Bodies::" +
        Regex.Escape(method) + @"\(").Groups[1].Value;
    if (number.Length == 0) throw new InvalidOperationException($"Method {method} is not in the extraction {name}.");
    var theorem = $"method{number}_body_validated";
    var narrowed = NarrowEvidence(extracted, theorem);
    var proof = Regex.Match(narrowed, @"(?m)^theorem " + theorem + @" : [^\r\n]*? := ⟨[^\r\n]*⟩\r?$").Value;
    if (proof.Length == 0) throw new InvalidOperationException("Missing body obligation " + theorem);
    var open = narrowed.Replace(proof, proof[..proof.IndexOf(" := ⟨", StringComparison.Ordinal)] + " := sorry");
    return Heartbeats(Path.Combine(output, "BodyChecked.lean"), narrowed, equations: false) -
        Heartbeats(Path.Combine(output, "BodyOpen.lean"), open, equations: false);
}
var chainCosts = chainLengths.Select(count => (double)BodyCheck("Chain" + count, "Chain" + count,
    $"Chain{count}_{count - 1}")).ToArray();
var rowCosts = bulkSizes.Select(count => (double)BodyCheck("Rows" + count, "Rows" + count, $"Small{count}")).ToArray();
for (var step = 1; step < chainCosts.Length; step++)
{
    var growth = chainCosts[step] / chainCosts[step - 1];
    Console.WriteLine(FormattableString.Invariant(
        $"PASS body check of one method in {chainLengths[step - 1]} and {chainLengths[step]} methods: ") +
        FormattableString.Invariant($"{chainCosts[step - 1]:F0} and {chainCosts[step]:F0} heartbeats, ") +
        FormattableString.Invariant($"{growth:F2} times"));
    if (growth > AllowedBodyGrowth)
        throw new Exception(FormattableString.Invariant(
            $"One body check costs {growth:F2} times as much at {chainLengths[step]} methods ") +
            FormattableString.Invariant($"as at {chainLengths[step - 1]}; the limit is {AllowedBodyGrowth}."));
}
var rowGrowth = rowCosts[1] / rowCosts[0];
Console.WriteLine(FormattableString.Invariant(
    $"PASS body check of one method against {bulkSizes[0]} and {bulkSizes[1]} metadata rows: {rowGrowth:F2} times"));
if (rowGrowth > AllowedBodyGrowth)
    throw new Exception(FormattableString.Invariant(
        $"One body check costs {rowGrowth:F2} times as much against {bulkSizes[1]} rows ") +
        FormattableString.Invariant($"as against {bulkSizes[0]}; the limit is {AllowedBodyGrowth}."));
// The kernel's one decision per module that its literal tables are the decoder's costs the rows carried, times a
// logarithm; it is paid once per extraction, not once per method.
long TablesCheck(string name)
{
    var output = Path.Combine(directory, "Body" + name);
    var narrowed = NarrowEvidence(File.ReadAllText(Path.Combine(output, "Extracted.lean")), "module0_tables_valid");
    var proof = Regex.Match(narrowed, @"(?m)^theorem module0_tables_valid : [^\r\n]*? := by decide \+kernel\r?$").Value;
    if (proof.Length == 0) throw new InvalidOperationException("Missing tables obligation in " + name);
    var open = narrowed.Replace(proof, proof[..proof.IndexOf(" := by", StringComparison.Ordinal)] + " := sorry");
    return Heartbeats(Path.Combine(output, "TablesChecked.lean"), narrowed, equations: false) -
        Heartbeats(Path.Combine(output, "TablesOpen.lean"), open, equations: false);
}
var tablesFew = TablesCheck("Rows" + bulkSizes[0]);
var tablesMany = TablesCheck("Rows" + bulkSizes[1]);
var tablesGrowth = tablesMany / (double)tablesFew;
Console.WriteLine(FormattableString.Invariant(
    $"PASS module tables check with {bulkSizes[0]} and {bulkSizes[1]} user string rows: ") +
    FormattableString.Invariant($"{tablesFew} and {tablesMany} heartbeats, ") +
    FormattableString.Invariant($"{tablesGrowth / (bulkSizes[1] / (double)bulkSizes[0]):F2} times the cost per row"));
if (tablesGrowth > AllowedBodyGrowth * bulkSizes[1] / bulkSizes[0])
    throw new Exception(FormattableString.Invariant(
        $"The module tables check costs {tablesGrowth:F2} times as much for {bulkSizes[1]} rows ") +
        FormattableString.Invariant($"as for {bulkSizes[0]}."));
