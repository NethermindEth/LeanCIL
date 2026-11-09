#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Globalization;
using System.Text.RegularExpressions;

// Each instruction equation is proved from the code suffix that starts its block. Proved against the
// whole code list instead, it walks one cell per preceding instruction and a method's equations cost
// quadratic time, which this fixture reports as a per-instruction cost that grows with the method.
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

// Heartbeats count the elaborator's and the kernel's work on one thread, so they repeat exactly
// where compile time varies with the machine's load.
long Heartbeats(string path)
{
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException("Untrusted extraction: " + path);
    var count = Regex.Match(output, @"(?m)^([0-9]+)\r?$");
    if (!count.Success) throw new InvalidOperationException("Missing heartbeat count:\n" + output);
    if (path.EndsWith("Measured.lean", StringComparison.Ordinal) &&
        Regex.Matches(output, @"_instruction[0-9]+' depends on axioms: \[propext\]").Count != 1)
        throw new InvalidOperationException("Instruction equations must depend on propext alone:\n" + output);
    return long.Parse(count.Groups[1].Value, CultureInfo.InvariantCulture);
}

const string Report = "\n#eval show IO Nat from IO.getNumHeartbeats\n";

(int Instructions, long Heartbeats) Measure(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var instructions = Regex.Matches(extracted, @"(?m)^@\[cil_code ↓\] theorem method0_instruction[0-9]+ : ").Count;
    var last = instructions - 1;
    // The statement is what stepping tactics and proofs rewrite with; only its proof may differ.
    if (!extracted.Contains(
            $"@[cil_code ↓] theorem method0_instruction{last} : method0.code[{last}]? = some (.ret : Op) := ",
            StringComparison.Ordinal))
        throw new InvalidOperationException($"Missing the lookup equation of the final instruction of {name}.");
    var measured = Path.Combine(output, "Measured.lean");
    // The last pc is the farthest from the head of the code list, and `cil_code` must still fetch it.
    File.WriteAllText(measured, extracted + $"""

        #print axioms Extracted.method0_instruction{last}
        example : Extracted.method0.code[{last}]? = some CIL.Op.ret := by simp only [cil_code]
        """ + Report);
    return (instructions, Heartbeats(measured));
}

var imports = Path.Combine(directory, "Imports.lean");
File.WriteAllText(imports,
    "import CIL.Extraction.Translation\nimport CIL.SymbolicExecution\nimport CIL.Safety.Execution\n" + Report);
var floor = Heartbeats(imports);
var brief = Measure("Short");
var extended = Measure("Long");
if (brief.Instructions < 500 || extended.Instructions < 4 * brief.Instructions - 8)
    throw new InvalidOperationException(
        $"Expected about 500 and 2,000 instructions; found {brief.Instructions} and {extended.Instructions}.");
double Cost((int Instructions, long Heartbeats) run) => (double)(run.Heartbeats - floor) / run.Instructions;
var growth = Cost(extended) / Cost(brief);
Console.WriteLine(string.Create(CultureInfo.InvariantCulture,
    $"{brief.Instructions} instructions: {Cost(brief):F0} heartbeats each; " +
    $"{extended.Instructions} instructions: {Cost(extended):F0} heartbeats each; growth {growth:F2}"));
if (growth > AllowedGrowth)
    throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
        $"Compiling an extracted method costs {growth:F2} times more per instruction at " +
        $"{extended.Instructions} instructions than at {brief.Instructions}; the limit is {AllowedGrowth}."));
Console.WriteLine($"PASS {extended.Instructions} instructions compile at the emitted recursion depth");
Console.WriteLine("PASS instruction lookup equations cost the same per instruction in a long method");
