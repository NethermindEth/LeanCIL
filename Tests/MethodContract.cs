#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;

// One caller proof, unedited, must verify against a build whose helpers are reimplemented and
// renumbered; builds with an arithmetic or an aliasing bug must provably violate the same contracts.
using var verification = new Program();
var root = At("artifacts/MethodContract");
const string Selector = "Calls::Root(ulong&,ulong&)";
const string AddTo = "System.Void Contracts.Calls::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)";
const string Root = "public static void Root(ref ulong r, in ulong b) { AddTo(in r, in b, out r); r = Mix(r, b); }";

string Build(string name, string helpers)
{
    var source = Path.Combine(root, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Contracts.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
    """);
    File.WriteAllText(Path.Combine(source, "Contracts.cs"), "namespace Contracts; public static class Calls { " + helpers + Root + " }");
    Run(["dotnet", "build", Path.Combine(source, "Contracts.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Contracts.dll");
}

var original = Build("Original",
    "public static ulong Mix(ulong x, ulong y) => x * 3 + y; " +
    "public static void AddTo(in ulong a, in ulong b, out ulong res) => res = a + b; ");
// Triple is reached through Mix first, so it takes AddTo's extraction index.
var replaced = Build("Replaced",
    "public static ulong Triple(ulong x) => x + x + x; " +
    "public static ulong Mix(ulong x, ulong y) => Triple(x) + y; " +
    "public static void AddTo(in ulong a, in ulong b, out ulong res) => res = a - ~b - 1; ");
var arithmetic = Build("Arithmetic",
    "public static ulong Mix(ulong x, ulong y) => x * 3 + y + 1; " +
    "public static void AddTo(in ulong a, in ulong b, out ulong res) => res = a + b; ");
// Correct unless `res` aliases `b`, which the contract permits.
var aliasing = Build("Aliasing",
    "public static ulong Mix(ulong x, ulong y) => x * 3 + y; " +
    "public static void AddTo(in ulong a, in ulong b, out ulong res) { res = a; res += b; } ");

int Index(string assembly, string name)
{
    var folder = Path.Combine(root, name + "-Extraction");
    Run(Extract("extract", assembly, "Contracts", Selector, folder));
    var extracted = File.ReadAllText(Path.Combine(folder, "Extracted.lean"));
    return int.Parse(Regex.Matches(extracted, @"(?m)^def method(\d+)Signature : String := ""([^""]+)""")
        .Single(m => Regex.Unescape(m.Groups[2].Value) == AddTo).Groups[1].Value);
}
if (Index(original, "Original") == Index(replaced, "Replaced"))
    throw new InvalidOperationException("The replaced build did not renumber AddTo; the suite would prove nothing.");

// The synthetic extraction in the Lean test mirrors the original build, so its sections are shared.
var test = File.ReadAllText(At("Tests/MethodContract.lean"));
string Section(string from, string to)
{
    var start = test.IndexOf(from, StringComparison.Ordinal);
    var end = start < 0 ? -1 : test.IndexOf(to, start, StringComparison.Ordinal);
    return end < 0 ? throw new InvalidDataException($"Tests/MethodContract.lean has no section from '{from}' to '{to}'") : test[start..end];
}
var contracts = Section("bind_method root rootBody", "theorem mix_holds");
var helpers = Section("theorem mix_holds", "set_option maxHeartbeats");
var caller = Section("set_option maxHeartbeats", "theorem root_correct");
const string Composed = "theorem correctness : rootContract.Holds Extracted.program root := root_holds mix_holds add_holds\n";

string Proof(string name, string body)
{
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, "import Extracted\nimport CIL.MethodIdentity\nimport CIL.StructuralLabels\nimport CIL.Safety.MethodContract\n" +
        "import CIL.Safety.WordMemory\nimport CIL.Safety.WordFootprint\n\nopen CIL.Safety\nnamespace ExampleProof\n\n" +
        contracts + body + "\nend ExampleProof\n");
    return path;
}

const string ReplacedHelpers = """
theorem mix_holds : mixContract.Holds Extracted.program mix := by
  rintro ⟨x, y⟩ m -
  dsimp only [mixContract]
  have same : x + x + x + y = x * 3 + y := by bv_omega
  refine ⟨16, m, _, ?_, Confined.refl _ m, rfl⟩
  rw [← same]
  cil_checked_steps

theorem add_holds : addContract.Holds Extracted.program addTo := by
  rintro ⟨a, b, res, x, y⟩ m ⟨readA, readB, writable⟩
  dsimp only [addContract] at *
  have length : (numberBytes (x + y).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨stored, wrote⟩ := write_succeeds (bytes := numberBytes (x + y).toNat 8) (by simpa only [length] using writable)
  have readback := write_readback _ _ _ _ _ wrote
  rw [length] at readback
  have store : storeValue m (.address res) (.i64 (x - ~~~y - 1#64)) = .ok stored := by
    rw [show x - ~~~y - 1#64 = x + y by bv_omega]
    simp only [storeValue, referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have fa := access_reference_valid _ _ _ _ _ (read_access readA)
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  have fr := access_reference_valid _ _ _ _ _ writable
  have la := load_word64_of_read readA
  have lb := load_word64_of_read readB
  refine ⟨12, stored, [], ?_, Confined.write wrote (by simp [numberBytes]), rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    fa, fb, fr, la, lb, store, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

""";

foreach (var (name, assembly, body) in new[] { ("Original", original, helpers), ("Replaced", replaced, ReplacedHelpers) })
{
    verification.Verify(assembly, "Contracts", Selector, Proof(name, body + caller + Composed), Path.Combine(root, name + "-Verified"));
    Console.WriteLine($"PASS {name}: the unedited caller proof composes the helper contracts");
}

// Each bug fails the original helper proofs, and a concrete run refutes the contract itself.
const string RefuteArithmetic = """
def empty : Memory := { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

/-- This build returns `Mix(0, 0) = 1`; the contract requires `0 * 3 + 0`. -/
theorem correctness : ¬ mixContract.Holds Extracted.program mix := by
  intro holds
  obtain ⟨_, final, values, ran, -, wrong⟩ := holds (0, 0) empty ⟨fun _ _ h => (nomatch h), fun _ h => (nomatch h)⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (invoke_ok_unique ran (rfl : invoke Extracted.program 16 mix
    (mixContract.args (0, 0)) empty = .ok _))
  simp [mixContract] at wrong

""";
const string RefuteAliasing = """
/-- `a` holds 1 at offset 0; `b` and `res` alias at offset 8, holding 2. -/
def aliased : Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
  cells := fun _ offset => ⟨if offset = 0 then 1 else if offset = 8 then 2 else 0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1 }

/-- The contract permits `res` to alias `b`; this build then writes `2`, not `1 + 2`. -/
theorem correctness : ¬ addContract.Holds Extracted.program addTo := by
  intro holds
  obtain ⟨_, final, values, ran, -, -, wrong⟩ := holds ⟨⟨0, 0⟩, ⟨0, 8⟩, ⟨0, 8⟩, 1, 2⟩ aliased ⟨rfl, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (invoke_ok_unique ran (rfl : invoke Extracted.program 16 addTo
    (addContract.args ⟨⟨0, 0⟩, ⟨0, 8⟩, ⟨0, 8⟩, 1, 2⟩) aliased = .ok _))
  have observed : (Except.ok (numberBytes (1 + 2 : CIL.W64).toNat 8) : Checked (List (BitVec 8))) =
      .ok (numberBytes 2 8) := wrong.symm.trans rfl
  exact absurd (Except.ok.inj observed) (by decide)

""";
foreach (var (name, assembly, refutation) in new[] { ("Arithmetic", arithmetic, RefuteArithmetic), ("Aliasing", aliasing, RefuteAliasing) })
{
    var failed = false;
    try
    {
        verification.Verify(assembly, "Contracts", Selector, Proof(name, helpers + caller + Composed), Path.Combine(root, name + "-Verified"));
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
    {
        failed = true;
    }
    if (!failed) throw new InvalidOperationException($"The {name} build passed the original helper proofs.");
    verification.Verify(assembly, "Contracts", Selector, Proof(name + "Refuted", refutation), Path.Combine(root, name + "-Refuted"));
    Console.WriteLine($"PASS {name}: the bug fails the helper proofs and its contract is refuted");
}
