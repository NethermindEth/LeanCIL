import Extracted
import CIL.Verification
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-! The filled `leancil new-proof` outline of the closure `StaticValues` uses to lay out a word's
    bytes, `index => (byte)(word.Bits >> (8 * index))`, extracted from LeanCIL's own assembly. The
    statement is the outline's; the specification and the proof replace its holes. -/

open CIL.Safety
open CIL (W32 W64)
open Extracted.Classes
namespace ExampleProof

/-- The captured `word` refers to a `Word` whose `Bits` can be read. -/
def Precondition (receiver : Reference) (_ : W32) (initial : Memory) : Prop :=
  ∃ word, «<>c__DisplayClass10_0».word.of initial receiver = .address word ∧
    Word.Bits.Readable initial word

/-- The result is byte `index % 8` of the captured word's bits, least significant first, which is
    the byte the static value's little-endian layout stores at offset `index`. -/
def Postcondition (receiver : Reference) (index : W32) (initial _ : Memory) (result : W32)
    : Prop :=
  ∀ word, «<>c__DisplayClass10_0».word.of initial receiver = .address word →
    result = ((Word.Bits.of initial word >>> (8 * (index.toNat % 8))).setWidth 8).setWidth 32

/-- The caller memory the method may write: the fields it stores of its object arguments. -/
def footprint (_ : Reference) (_ : W32) : List (Reference × Nat) :=
  []

/-- The `Word.Bits` getter returns the field and changes no memory. -/
def bitsContract : MethodContract Reference W64 where
  args word := [.object (.address word)]
  results bits := [.scalar (.i64 bits)]
  pre word memory := Word.Bits.Readable memory word
  footprint _ := []
  post word initial final bits := final = initial ∧ bits = Word.Bits.of initial word

/-- The getter meets its contract for every word whose `Bits` is readable. -/
theorem bits_holds : bitsContract.Holds Extracted.program 1 := by
  intro word memory readable
  dsimp only [bitsContract] at *
  refine ⟨CIL.executionBound Extracted.program 1, memory,
    [.scalar (.i64 (Word.Bits.of memory word))], ?_, Confined.refl _ _, _, rfl, rfl, rfl⟩
  cil_checked_steps [readable.facts]

#print axioms bits_holds

theorem correctness (receiver : Reference) (index : W32) : Ensures Extracted.program 0
    (fun args initial => args = [.object (.address receiver), .scalar (.i32 index)] ∧
      initial.WellFormed ∧ LiveObject initial receiver ∧
      «<>c__DisplayClass10_0».word.Readable initial receiver ∧ Precondition receiver index initial)
    (fun _ initial final results => ∃ result : W32, results = [.scalar (.i32 result)] ∧
      Confined (footprint receiver index) initial final ∧
      Postcondition receiver index initial final result) := by
  rintro args initial ⟨rfl, wellFormed, receiverLive, receiverWord, assumed⟩
  obtain ⟨word, held, bits⟩ := assumed
  -- The captured reference loads through its `Readable` fact; the getter call composes through
  -- its contract, which leaves memory unchanged.
  cil_contract_steps [bits_holds, bitsContract, receiverLive.formed,
    receiverWord.facts held bits.live, bits, bits.live.formed]
  rename_i final confined output post _
  dsimp only [bitsContract] at confined post
  obtain ⟨rfl, rfl⟩ := post
  refine ⟨_, rfl, (Confined.refl [] _).after_leaveFrame (by simp), ?_⟩
  intro target targetHeld
  rw [held] at targetHeld
  cases targetHeld
  -- C# masks the shift count to 6 bits, so `8 * index` shifts by byte `index % 8`.
  have shift : (8 * index.toNat % 4294967296 &&& 63) % 64 = 8 * (index.toNat % 8) := by
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [shift]
  generalize Word.Bits.of final word >>> (8 * (index.toNat % 8)) = shifted
  simp only [CIL.NarrowKind.extend]
  bv_decide

#print axioms correctness
end ExampleProof
