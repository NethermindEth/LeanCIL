import Extracted
import CIL.Verification
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-! The filled `leancil new-proof` outline of the closure `StaticValues` uses to lay out a word's
    bytes, `index => (byte)(word.Bits >> (8 * index))`, extracted from LeanCIL's own assembly. Only
    the outline's holes are filled: the specification and the arithmetic of the returned byte. -/

open CIL.Safety
open CIL (W32 W64)
open Extracted.Classes
namespace ExampleProof

/-- `get_Bits` as the outline reads its body: it needs the facts of `pre`, writes only `footprint`
    and leaves `post`. -/
def get_BitsContract : MethodContract Reference W64 where
  args := fun word => [.object (.address word)]
  results result := [.scalar (.i64 result)]
  pre := fun word memory => LiveObject memory word ∧ Word.Bits.Readable memory word
  footprint := fun _ => []
  post := fun word initial final result => final = initial ∧ result = (Word.Bits.of initial word)

/-- `get_Bits` meets its contract; callers use only the contract. -/
theorem get_Bits_holds : get_BitsContract.Holds Extracted.program 1 := by
  rintro word initial permitted
  dsimp only [get_BitsContract] at *
  obtain ⟨wordLive, wordBits⟩ := permitted
  cil_contract_steps [leaveFrame]
  exact MethodContract.Holds.returns (Confined.refl _ _) ⟨rfl, rfl⟩

#print axioms get_Bits_holds

/-- The statement already asks for the captured word and its readable `Bits`. -/
def Precondition (_ : Reference) (_ : W32) (_ : Memory) : Prop := True

/-- The result is byte `index % 8` of the captured word's bits, least significant first, which is
    the byte the static value's little-endian layout stores at offset `index`. -/
def Postcondition (receiver : Reference) (index : W32) (initial _ : Memory) (result : W32)
    : Prop :=
  ∀ word, «<>c__DisplayClass10_0».word.of initial receiver = .address word →
    result = ((Word.Bits.of initial word >>> (8 * (index.toNat % 8))).setWidth 8).setWidth 32

/-- The caller memory the method may write: the fields it stores of its object arguments. -/
def footprint (_ : Reference) (_ : W32) : List (Reference × Nat) :=
  []

theorem correctness (receiver : Reference) (index : W32) (receiverWordTarget : Reference)
    : Ensures Extracted.program 0
    (fun args initial => args = [.object (.address receiver), .scalar (.i32 index)] ∧
      initial.WellFormed ∧ LiveObject initial receiver ∧
      «<>c__DisplayClass10_0».word.Readable initial receiver ∧
      «<>c__DisplayClass10_0».word.of initial receiver = .address receiverWordTarget ∧
      LiveObject initial receiverWordTarget ∧ Word.Bits.Readable initial receiverWordTarget ∧
      Precondition receiver index initial)
    (fun _ initial final results => ∃ result : W32, results = [.scalar (.i32 result)] ∧
      Confined (footprint receiver index) initial final ∧
      Postcondition receiver index initial final result) := by
  rintro args initial ⟨rfl, wellFormed, receiverLive, receiverWord, receiverWordHeld,
      receiverWordTargetLive, receiverWordTargetBits, assumed⟩
  cil_contract_steps [receiverWord.facts receiverWordHeld receiverWordTargetLive,
      receiverWordTargetLive, receiverWordTargetLive.formed, receiverWordTargetBits, get_Bits_holds,
      get_BitsContract, leaveFrame]
    with called1 output1 call1
  have post1 := call1.post
  dsimp only [get_BitsContract] at post1
  obtain ⟨post1, rfl⟩ := post1
  subst called1
  try cil_contract_steps [get_BitsContract, leaveFrame]
  refine ⟨_, rfl, Confined.refl _ _, ?_⟩
  intro word held
  rw [receiverWordHeld] at held
  cases held
  -- C# masks the shift count to 6 bits, so `8 * index` shifts by byte `index % 8`.
  have shift : (8 * index &&& 63#32).toNat % 64 = 8 * (index.toNat % 8) := by
    rw [BitVec.toNat_and, BitVec.toNat_mul]
    change (8 * index.toNat % 4294967296 &&& 63) % 64 = _
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [show 2 ^ 6 = 64 from rfl, Nat.mod_mod]
    rw [Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 4294967296)]
    exact Nat.mul_mod_mul_left 8 index.toNat 8
  simp only [shift]
  generalize Word.Bits.of initial receiverWordTarget >>> (8 * (index.toNat % 8)) = shifted
  simp only [CIL.NarrowKind.extend]
  bv_decide

#print axioms correctness
end ExampleProof
