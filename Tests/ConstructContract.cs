#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// One caller proof, unedited, must verify against a build whose constructors are reimplemented;
// a build whose constructor stores the wrong value must fail the constructor proof and violate its contract.
using var verification = new Program();
var root = At("artifacts/ConstructContract");
const string Selector = "Calls::Root(ulong,ulong)";
const string Root = "public static class Calls { public static ulong Root(ulong x, ulong y) => new Pair(x, y).High + new Word(y, 1, 2, x).U3; }";

string Build(string name, string pair, string word)
{
    var source = Path.Combine(root, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Constructs.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
    """);
    File.WriteAllText(Path.Combine(source, "Constructs.cs"), "namespace Constructs; " +
        "public struct Pair { public ulong Low; public ulong High; public Pair(ulong low, ulong high) { " + pair + " } } " +
        "public struct Word { public ulong U0; public ulong U1; public ulong U2; public ulong U3; " +
        "public Word(ulong u0, ulong u1, ulong u2, ulong u3) { " + word + " } } " + Root);
    Run(["dotnet", "build", Path.Combine(source, "Constructs.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Constructs.dll");
}

const string Word = "U0 = u0; U1 = u1; U2 = u2; U3 = u3;";
var original = Build("Original", "Low = low; High = high;", Word);
// Every field is written in the opposite order, so both constructor proofs change.
var replaced = Build("Replaced", "High = high; Low = low;", "U3 = u3; U2 = u2; U1 = u1; U0 = u0;");
var arithmetic = Build("Arithmetic", "Low = low; High = high + 1;", Word);

// The synthetic extraction in the Lean test mirrors the original build, so its sections are shared.
var test = File.ReadAllText(At("Tests/ConstructContract.lean"));
string Section(string from, string to)
{
    var start = test.IndexOf(from, StringComparison.Ordinal);
    var end = start < 0 ? -1 : test.IndexOf(to, start, StringComparison.Ordinal);
    return end < 0 ? throw new InvalidDataException($"Tests/ConstructContract.lean has no section from '{from}' to '{to}'") : test[start..end];
}
var contracts = Section("bind_method root rootBody", "theorem pair_holds");
var helpers = Section("theorem pair_holds", "/-- Uses only the constructors'");
var caller = Section("/-- Uses only the constructors'", "theorem root_correct");
const string Composed = "theorem correctness : rootContract.Holds Extracted.program root := root_holds pair_holds word_holds\n";

string Proof(string name, string body)
{
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, "import Extracted\nimport CIL.MethodIdentity\nimport CIL.StructuralLabels\nimport CIL.Safety.ConstructContract\n" +
        "import CIL.Safety.WordMemory\nimport CIL.Safety.ReturnMemory\n\nopen CIL.Safety\nnamespace ExampleProof\n\n" +
        contracts + body + "\nend ExampleProof\n");
    return path;
}

const string ReplacedHelpers = """
theorem pair_holds : pairContract.Holds Extracted.program pair := by
  rintro ⟨⟨id, offset⟩, low, high⟩ m ⟨formed, writable⟩
  dsimp only [pairContract] at *
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have length : ∀ v : CIL.W64, (numberBytes v.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨m1, w1⟩ := write_succeeds (bytes := numberBytes high.toNat 8)
    (by simpa only [length] using (ready.slice formed 8 8 (by decide) (by decide)).access)
  have formed1 := write_preserves_wellFormed _ _ _ _ _ formed w1
  have ready1 := ready.after_write w1
  obtain ⟨m2, w2⟩ := write_succeeds (bytes := numberBytes low.toNat 8)
    (by simpa only [length] using (ready1.slice formed1 0 8 (by decide) (by decide)).access)
  have a1 := ready.add_slice formed 1 8 8 (by decide) (by decide)
  have a2 := ready1.add_slice formed1 1 0 8 (by decide) (by decide)
  have f0 := access_reference_valid _ _ _ _ _ writable
  have f1 := access_reference_valid _ _ _ _ _ ready1.access
  simp only [Nat.add_zero, Nat.one_mul] at a1 a2 w2
  have high1 := write_readback _ _ _ _ _ w1
  have high2 := write_preserves_disjoint_read w2 high1 (Or.inr (Or.inr (by simp [length])))
  have low2 := write_readback _ _ _ _ _ w2
  rw [length] at high2 low2
  have readback := read_append (left := 8) (right := 8) ((ready1.after_write w2).access) low2 high2
  have c1 : Confined [(⟨id, offset⟩, 16)] m m1 :=
    (Confined.write w1 (List.mem_singleton_self _)).cover rfl (by simp) (by simp [length])
  have c2 : Confined [(⟨id, offset⟩, 16)] m1 m2 :=
    (Confined.write w2 (List.mem_singleton_self _)).cover rfl (by simp) (by simp [length])
  refine ⟨8, m2, [], ?_, c1.trans c2, (), rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    f0, f1, a1, a2, w1, w2, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem word_holds : wordContract.Holds Extracted.program word := by
  rintro ⟨⟨id, offset⟩, u0, u1, u2, u3⟩ m ⟨formed, writable⟩
  dsimp only [wordContract] at *
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have length : ∀ v : CIL.W64, (numberBytes v.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨m1, w1⟩ := write_succeeds (bytes := numberBytes u3.toNat 8)
    (by simpa only [length] using (ready.slice formed 24 8 (by decide) (by decide)).access)
  have formed1 := write_preserves_wellFormed _ _ _ _ _ formed w1
  have ready1 := ready.after_write w1
  obtain ⟨m2, w2⟩ := write_succeeds (bytes := numberBytes u2.toNat 8)
    (by simpa only [length] using (ready1.slice formed1 16 8 (by decide) (by decide)).access)
  have formed2 := write_preserves_wellFormed _ _ _ _ _ formed1 w2
  have ready2 := ready1.after_write w2
  obtain ⟨m3, w3⟩ := write_succeeds (bytes := numberBytes u1.toNat 8)
    (by simpa only [length] using (ready2.slice formed2 8 8 (by decide) (by decide)).access)
  have formed3 := write_preserves_wellFormed _ _ _ _ _ formed2 w3
  have ready3 := ready2.after_write w3
  obtain ⟨m4, w4⟩ := write_succeeds (bytes := numberBytes u0.toNat 8)
    (by simpa only [length] using (ready3.slice formed3 0 8 (by decide) (by decide)).access)
  have formed4 := write_preserves_wellFormed _ _ _ _ _ formed3 w4
  have ready4 := ready3.after_write w4
  have a1 := ready.add_slice formed 1 24 8 (by decide) (by decide)
  have a2 := ready1.add_slice formed1 1 16 8 (by decide) (by decide)
  have a3 := ready2.add_slice formed2 1 8 8 (by decide) (by decide)
  have a4 := ready3.add_slice formed3 1 0 8 (by decide) (by decide)
  have f0 := access_reference_valid _ _ _ _ _ writable
  have f1 := access_reference_valid _ _ _ _ _ ready1.access
  have f2 := access_reference_valid _ _ _ _ _ ready2.access
  have f3 := access_reference_valid _ _ _ _ _ ready3.access
  have w4' := w4
  simp only [Nat.add_zero, Nat.one_mul] at a1 a2 a3 a4 w4'
  have r1 := write_readback _ _ _ _ _ w1
  have r2 := write_readback _ _ _ _ _ w2
  have r3 := write_readback _ _ _ _ _ w3
  have r4 := write_readback _ _ _ _ _ w4'
  rw [length] at r1 r2 r3 r4
  -- Each limb survives the later, disjoint limb writes below it.
  have later : ∀ {a b : Memory} {r : Reference} {bytes old : List (BitVec 8)} {start : Nat},
      write a { allocation := id, offset := offset + start } bytes 1 = .ok b →
      read a r 8 1 = .ok old → offset + start + bytes.length ≤ r.offset → read b r 8 1 = .ok old :=
    fun written readable after => write_preserves_disjoint_read written readable (Or.inr (Or.inr after))
  have two := read_append (left := 8) (right := 8) (ready4.slice formed4 0 16 (by decide) (by decide)).access
    (by simpa using r4) (later (start := 0) w4 r3 (by simp [length]))
  have three := read_append (left := 16) (right := 8) (ready4.slice formed4 0 24 (by decide) (by decide)).access
    (by simpa using two) (later (start := 0) w4 (later w3 r2 (by simp [length])) (by simp [length]))
  have readback := read_append (left := 24) (right := 8) ready4.access (by simpa using three)
    (later (start := 0) w4 (later w3 (later w2 r1 (by simp [length])) (by simp [length])) (by simp [length]))
  have covered : ∀ {a b : Memory} {start : Nat} {bytes : List (BitVec 8)},
      write a { allocation := id, offset := offset + start } bytes 1 = .ok b → start + bytes.length ≤ 32 →
      Confined [(⟨id, offset⟩, 32)] a b :=
    fun written inside => (Confined.write written (List.mem_singleton_self _)).cover rfl (by simp) (by simp; omega)
  refine ⟨14, m4, [], ?_, (covered w1 (by simp [length])).trans ((covered w2 (by simp [length])).trans
    ((covered w3 (by simp [length])).trans (covered (start := 0) w4 (by simp [length])))), (), rfl, ?_⟩
  · cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
      f0, f1, f2, f3, a1, a2, a3, a4, w1, w2, w3, w4', Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simpa [wordBytes, List.append_assoc] using readback

""";

foreach (var (name, assembly, body) in new[] { ("Original", original, helpers), ("Replaced", replaced, ReplacedHelpers) })
{
    verification.Verify(assembly, "Constructs", Selector, Proof(name, body + caller + Composed), Path.Combine(root, name + "-Verified"));
    Console.WriteLine($"PASS {name}: the unedited caller proof composes the constructor contracts");
}

// The bug fails the original constructor proof, and a concrete run refutes the constructor's contract.
const string RefuteArithmetic = """
/-- One writable 16-byte allocation, already zeroed as `newobj` leaves it. -/
def storage : Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1 }

theorem storage_formed : storage.WellFormed := by
  refine ⟨fun id allocation found => ?_, fun view member => ?_⟩
  · by_cases zero : id = 0
    · subst zero
      simp only [storage, ite_true, Option.some.injEq] at found
      subst found
      exact ⟨by decide, by decide, by simp, by simp⟩
    · simp [storage, zero] at found
  · simp only [storage, List.mem_singleton] at member
    subst member
    exact ⟨_, rfl, by decide⟩

/-- This build stores `high + 1`, so `Pair(0, 0)` reads back as `Pair(0, 1)`. -/
theorem correctness : ¬ pairContract.Holds Extracted.program pair := by
  intro holds
  obtain ⟨_, final, values, ran, -, _, -, wrong⟩ := holds ⟨⟨0, 0⟩, 0, 0⟩ storage ⟨storage_formed, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (invoke_ok_unique ran (rfl : invoke Extracted.program 16 pair
    (pairContract.args ⟨⟨0, 0⟩, 0, 0⟩) storage = .ok _))
  have observed : (Except.ok (pairBytes ⟨⟨0, 0⟩, 0, 0⟩) : Checked (List (BitVec 8))) =
      .ok (numberBytes 0 8 ++ numberBytes 1 8) := wrong.symm.trans rfl
  exact absurd (Except.ok.inj observed) (by decide)

""";
var failed = false;
try
{
    verification.Verify(arithmetic, "Constructs", Selector, Proof("Arithmetic", helpers + caller + Composed), Path.Combine(root, "Arithmetic-Verified"));
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed) throw new InvalidOperationException("The Arithmetic build passed the original constructor proofs.");
verification.Verify(arithmetic, "Constructs", Selector, Proof("ArithmeticRefuted", RefuteArithmetic), Path.Combine(root, "Arithmetic-Refuted"));
Console.WriteLine("PASS Arithmetic: the bug fails the constructor proof and its contract is refuted");
