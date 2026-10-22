#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// The outcome proofs verify against the compiled build; an off-by-one threshold or a different
// exception type must fail them and provably violate the callee's contract.
using var verification = new Program();
var root = At("artifacts/OutcomeContract");
const string Selector = "Calls::Root(ulong)";
const string Callers = "public static ulong Strict(ulong value) => Percent(value) == 0 ? throw new ArgumentException(nameof(value)) : value; " +
    "public static ulong Root(ulong value) => Strict(value) + 1;";

string Build(string name, string percent)
{
    var source = Path.Combine(root, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Outcomes.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
    """);
    File.WriteAllText(Path.Combine(source, "Outcomes.cs"),
        "using System; namespace Outcomes; public static class Calls { " + percent + " " + Callers + " }");
    Run(["dotnet", "build", Path.Combine(source, "Outcomes.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Outcomes.dll");
}

var original = Build("Original",
    "public static ulong Percent(ulong value) => value <= 100 ? value : throw new ArgumentOutOfRangeException(nameof(value));");
var threshold = Build("Threshold",
    "public static ulong Percent(ulong value) => value < 100 ? value : throw new ArgumentOutOfRangeException(nameof(value));");
var exception = Build("Exception",
    "public static ulong Percent(ulong value) => value <= 100 ? value : throw new ArgumentException(nameof(value));");

// The synthetic extraction in the Lean test mirrors the original build, so its sections are shared.
var test = File.ReadAllText(At("Tests/OutcomeContract.lean"));
string Section(string from, string to)
{
    var start = test.IndexOf(from, StringComparison.Ordinal);
    var end = start < 0 ? -1 : test.IndexOf(to, start, StringComparison.Ordinal);
    return end < 0 ? throw new InvalidDataException($"Tests/OutcomeContract.lean has no section from '{from}' to '{to}'") : test[start..end];
}
var contracts = Section("bind_method root rootBody", "theorem percent_holds");
var proofs = Section("theorem percent_holds", "theorem root_correct");
const string Composed = "theorem correctness : rootContract.Holds Extracted.program root := root_holds (strict_holds percent_holds)\n";

string Proof(string name, string body)
{
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, "import Extracted\nimport CIL.MethodIdentity\nimport CIL.StructuralLabels\nimport CIL.Safety.OutcomeContract\n\n" +
        "open CIL.Safety\nnamespace ExampleProof\n\n" + contracts + body + "\nend ExampleProof\n");
    return path;
}

verification.Verify(original, "Outcomes", Selector, Proof("Original", proofs + Composed), Path.Combine(root, "Original-Verified"));
Console.WriteLine("PASS Original: every outcome of both callers follows from their callees' contracts");

const string Empty = """
def empty : Memory := { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

""";
const string RefuteThreshold = Empty + """
/-- This build throws for `100`; the contract requires it to return. -/
theorem correctness : ¬ percentContract.Holds Extracted.program percent := by
  intro holds
  obtain ⟨_, _, _, ran, -⟩ := holds.returning (input := 100) (initial := empty) trivial (by decide)
  have thrown : invoke Extracted.program 16 percent (percentContract.args 100) empty =
      .error ⟨percent, 6, .thrown "System.ArgumentOutOfRangeException"⟩ := rfl
  cases invoke_unique (by trivial) (by simp [Settled]) ran thrown

""";
const string RefuteException = Empty + """
/-- This build throws `ArgumentException` for `101`; the contract names `ArgumentOutOfRangeException`. -/
theorem correctness : ¬ percentContract.Holds Extracted.program percent := by
  intro holds
  obtain ⟨_, fault, ran, named⟩ := holds.raising (input := 101) (initial := empty)
    (exception := "System.ArgumentOutOfRangeException") trivial (by decide)
  have thrown : invoke Extracted.program 16 percent (percentContract.args 101) empty =
      .error ⟨percent, 6, .thrown "System.ArgumentException"⟩ := rfl
  cases invoke_unique (by simp [Settled, named]) (by simp [Settled]) ran thrown
  simp at named

""";
foreach (var (name, assembly, refutation) in new[] { ("Threshold", threshold, RefuteThreshold), ("Exception", exception, RefuteException) })
{
    var failed = false;
    try
    {
        verification.Verify(assembly, "Outcomes", Selector, Proof(name, proofs + Composed), Path.Combine(root, name + "-Verified"));
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
    {
        failed = true;
    }
    if (!failed) throw new InvalidOperationException($"The {name} build passed the original outcome proofs.");
    verification.Verify(assembly, "Outcomes", Selector, Proof(name + "Refuted", refutation), Path.Combine(root, name + "-Refuted"));
    Console.WriteLine($"PASS {name}: the bug fails the outcome proofs and its contract is refuted");
}

Run(["dotnet", "run", "--file", "Tests/RuntimeExceptions.cs"], streamOutput: true);
