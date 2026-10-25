import Extracted
import DerivedInterface
import CIL.Safety.WordMemory
import CIL.Safety.WordFootprint

/-! The producer proof of `AddTo(in left, in right, out sum) { sum = left + right; }`, against
    its actual extraction. The internal contract names the exact 8-byte footprint `sum`; the
    exported `addPublic` theorem widens it to the caller's region and adds the frame fact for
    `left` through `MethodContract.Holds.weaken` alone. The internal contract stays in this
    unpublished module. The rejected section refutes a smaller footprint on the same extraction. -/

namespace DerivedAddProof
open CIL.Safety

/-- What `AddTo` needs: `left` and `right` hold their words and `sum` is writable. -/
def addPre (input : DerivedInterface.AddInput) (memory : Memory) : Prop :=
  read memory input.left 8 1 = .ok (numberBytes input.leftValue.toNat 8) ∧
    read memory input.right 8 1 = .ok (numberBytes input.rightValue.toNat 8) ∧
    access memory input.sum 8 1 true = .ok ()

/-- The internal contract: `AddTo` writes only the 8 bytes of `sum`, which then hold the sum. -/
def addInternal : MethodContract DerivedInterface.AddInput where
  args := DerivedInterface.addArguments
  pre := addPre
  footprint input := [(input.sum, 8)]
  post input _ final values := values = [] ∧
    read final input.sum 8 1 = .ok (numberBytes (input.leftValue + input.rightValue).toNat 8)

/-- `AddTo` writes the sum into `sum` and nothing else. -/
theorem add_internal : addInternal.Holds Extracted.program 0 := by
  rintro ⟨left, right, sum, region, leftValue, rightValue⟩ memory ⟨readLeft, readRight, writable⟩
  dsimp only [addInternal, DerivedInterface.addArguments] at *
  have width : (numberBytes (leftValue + rightValue).toNat 8).length = 8 := by
    simp [numberBytes]
  obtain ⟨stored, wrote⟩ := write_succeeds (bytes := numberBytes (leftValue + rightValue).toNat 8)
    (by simpa only [width] using writable)
  have readback := write_readback _ _ _ _ _ wrote
  rw [width] at readback
  have store : storeValue memory (.address sum) (.i64 (leftValue + rightValue)) = .ok stored := by
    simp only [storeValue, CIL.Value.hasUnspecified, Bool.false_eq_true, ↓reduceIte,
      referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have leftForm := access_reference_valid _ _ _ _ _ (read_access readLeft)
  have rightForm := access_reference_valid _ _ _ _ _ (read_access readRight)
  have sumForm := access_reference_valid _ _ _ _ _ writable
  have leftLoad := load_word64_of_read readLeft
  have rightLoad := load_word64_of_read readRight
  refine ⟨CIL.executionBound Extracted.program 0, stored, [], ?_,
    Confined.write wrote (by simp [numberBytes]), _, rfl, rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction,
    memoryInstruction, observerCount, unspecifiedOperands, Value.hasUnspecified,
    CIL.Value.hasUnspecified, leftForm, rightForm, sumForm, leftLoad, rightLoad, store,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms add_internal

/-- The region covers the internal footprint, and `left` survives because it lies apart from
    `sum`; the frame fact follows from the internal footprint alone. -/
theorem add_public_refines : addInternal.Refines DerivedInterface.addPublic where
  args _ := rfl
  results _ := rfl
  pre _ _ permitted := ⟨permitted.2.1, permitted.2.2.1, permitted.2.2.2.1⟩
  footprint _ _ permitted _ member :=
    ⟨_, List.mem_singleton_self _, List.mem_singleton.mp member ▸ permitted.2.2.2.2.2⟩
  post _ _ _ _ permitted framed satisfied :=
    ⟨satisfied.1, satisfied.2, framed.read_apart permitted.1 permitted.2.1
      fun _ member => List.mem_singleton.mp member ▸ permitted.2.2.2.2.1⟩

#print axioms add_public_refines

/-- The exported theorem: the actual `AddTo` meets its public contract. -/
theorem correctness : DerivedInterface.addPublic.Holds Extracted.program 0 :=
  add_internal.weaken add_public_refines

#print axioms correctness

/-! A rejected derivation: the footprint premise fails on a concrete input, and the contract it
    would derive is false of the actual extraction. -/
namespace Rejected

/-- One 24-byte writable allocation holding the words 1, 1 and 0. -/
def sample : Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨24, 1, []⟩, true, [24]⟩ else none
  cells := fun _ offset => ⟨if offset = 0 ∨ offset = 8 then 1 else 0, true⟩
  views := [⟨0, 0, 24, true, true⟩]
  nextIdentity := 1 }

/-- `left` and `right` are the words 1 at offsets 0 and 8; `sum` is the word at 16. -/
def sampleInput : DerivedInterface.AddInput := ⟨⟨0, 0⟩, ⟨0, 8⟩, ⟨0, 16⟩, ⟨0, 0⟩, 1, 1⟩

/-- The sample meets the internal precondition. -/
theorem sample_pre : addPre sampleInput sample := ⟨rfl, rfl, rfl⟩

#print axioms sample_pre

/-- A smaller footprint: `AddTo` changes `sum`, which an empty footprint would keep. -/
def addUnframed : MethodContract DerivedInterface.AddInput :=
  { addInternal with footprint := fun _ => [] }

/-- The exact contract does not refine an empty footprint. -/
theorem smaller_footprint_not_refines : ¬ addInternal.Refines addUnframed := fun refines => by
  obtain ⟨_, member, _⟩ :=
    refines.footprint sampleInput sample sample_pre _ (List.mem_singleton_self _)
  exact nomatch member

/-- No proof of the empty footprint exists for the actual extraction. -/
theorem smaller_footprint_rejected : ¬ addUnframed.Holds Extracted.program 0 := fun holds => by
  obtain ⟨_, final, values, invoked, framed, -⟩ := holds sampleInput sample sample_pre
  obtain ⟨_, otherFinal, otherValues, otherInvoked, -, _, rfl, -, readback⟩ :=
    add_internal sampleInput sample sample_pre
  have same := congrArg Prod.fst (invoke_ok_unique invoked otherInvoked)
  dsimp only at same
  subst same
  have kept := framed.read_eq sampleInput.sum (by decide) 8 1 fun _ _ => Outside.nil _ _
  have zero : read sample sampleInput.sum 8 1 = .ok (numberBytes 0 8) := rfl
  rw [readback, zero] at kept
  exact absurd (Except.ok.inj kept) (by decide)

-- An explicit `sorry` is only a warning, so each refutation's axioms are pinned to fail the build.
/-- info: 'DerivedAddProof.Rejected.smaller_footprint_not_refines'
  depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms smaller_footprint_not_refines
/-- info: 'DerivedAddProof.Rejected.smaller_footprint_rejected'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smaller_footprint_rejected

end Rejected

end DerivedAddProof
