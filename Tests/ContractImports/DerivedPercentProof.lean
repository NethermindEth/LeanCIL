import Extracted
import DerivedInterface
import CIL.Safety.SymbolicExecution

/-! The producer proof of `Percent(value) => value <= 100 ? value : throw new
    ArgumentOutOfRangeException(...)`, against its actual extraction. An exact internal outcome
    contract is proved by stepping; the exported `percentBounded` theorem is derived from it by
    `OutcomeContract.Holds.weaken` alone. The internal contract stays in this unpublished module.
    The rejected section refutes, on the same extraction, every derivation that would strengthen
    the post, weaken the pre or rename the exception. -/

namespace DerivedPercentProof
open CIL.Safety

/-- The internal contract: under any memory, `Percent` returns its input exactly or throws
    `ArgumentOutOfRangeException` above 100. -/
def percentExact : OutcomeContract CIL.W64 CIL.W64 where
  args value := [.scalar (.i64 value)]
  results output := [.scalar (.i64 output)]
  pre _ _ := True
  footprint _ := []
  post value _ _ output := output = value
  raises value _ := DerivedInterface.percentRaises value

/-- Stepped on the actual extraction: each input returns itself or throws as named. -/
theorem percent_exact : percentExact.Holds Extracted.program 0 := by
  rintro value memory -
  by_cases within : value ≤ 100
  · have bound : value ≤ 100#64 := within
    simp only [percentExact, DerivedInterface.percentRaises, within, ite_true]
    refine ⟨CIL.executionBound Extracted.program 0, memory, _, ?_, Confined.refl _ memory, _,
      rfl, rfl⟩
    cil_checked_steps [bound]
  · have bound : ¬ value ≤ 100#64 := within
    simp only [percentExact, DerivedInterface.percentRaises, within, ite_false]
    cil_raise_steps [bound]

#print axioms percent_exact

/-- The public bound follows from the exact result on the inputs that return. -/
theorem percent_bounded_refines : percentExact.Refines DerivedInterface.percentBounded where
  args _ := rfl
  results _ := rfl
  pre _ _ _ := trivial
  raises _ _ _ := rfl
  footprint _ _ _ _ _ member := nomatch member
  post value _ _ output _ normal _ same := by
    dsimp only [DerivedInterface.percentBounded, DerivedInterface.percentRaises] at normal ⊢
    split at normal
    · exact same ▸ ‹value ≤ 100›
    · cases normal

#print axioms percent_bounded_refines

/-- The exported theorem: no instruction of `Percent` is stepped again. -/
theorem correctness : DerivedInterface.percentBounded.Holds Extracted.program 0 :=
  percent_exact.weaken percent_bounded_refines

#print axioms correctness

/-! Rejected derivations: each premise fails on a concrete input, and the contract it would
    derive is false of the actual extraction. -/
namespace Rejected

/-- A memory with nothing allocated; `Percent` reads no memory. -/
def empty : Memory :=
  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [],
    nextIdentity := 0 }

/-- `empty` meets the public precondition. -/
theorem empty_formed : empty.WellFormed := by
  simp [Memory.WellFormed, empty]

/-- Two outcomes of one invocation that both raise name the same exception. -/
theorem raises_unique {method : Nat} {args : List Value} {memory : Memory}
    {one other : String} (first : Raises Extracted.program method args memory one)
    (second : Raises Extracted.program method args memory other) : one = other := by
  obtain ⟨_, fault, ran, thrown⟩ := first
  obtain ⟨_, otherFault, otherRan, otherThrown⟩ := second
  cases invoke_unique (by simp [Settled, thrown]) (by simp [Settled, otherThrown]) ran otherRan
  rw [thrown] at otherThrown
  cases otherThrown
  rfl

/-- An invocation that raises never also returns. -/
theorem raises_not_returns {method fuel : Nat} {args : List Value} {memory : Memory}
    {exception : String} {result : Memory × List Value}
    (raised : Raises Extracted.program method args memory exception)
    (returned : invoke Extracted.program fuel method args memory = .ok result) : False := by
  obtain ⟨_, fault, ran, thrown⟩ := raised
  cases invoke_unique (second := .ok result) (by simp [Settled, thrown]) trivial ran returned

/-- `Percent(100)` returns 100. -/
theorem percent_hundred : ∃ fuel final,
    invoke Extracted.program fuel 0 [.scalar (.i64 100)] empty =
      .ok (final, [.scalar (.i64 100)]) := by
  obtain ⟨fuel, final, values, invoked, -, output, encoded, same⟩ :=
    percent_exact.returning (input := 100) (initial := empty) trivial (by decide)
  dsimp only [percentExact] at encoded same
  subst same encoded
  exact ⟨fuel, final, invoked⟩

/-- `Percent(101)` raises `ArgumentOutOfRangeException`. -/
theorem percent_above : Raises Extracted.program 0 [.scalar (.i64 101)] empty
    "System.ArgumentOutOfRangeException" :=
  percent_exact.raising (input := 101) trivial (by decide)

/-- An unjustified stronger post: `Percent(100)` returns 100, which is not below 100. -/
def percentTooStrong : OutcomeContract CIL.W64 CIL.W64 :=
  { DerivedInterface.percentBounded with post := fun _ _ _ output => output < 100 }

/-- The exact contract does not refine the stronger post. -/
theorem stronger_post_not_refines : ¬ percentExact.Refines percentTooStrong := fun refines => by
  have bound : (100 : CIL.W64) < 100 :=
    refines.post 100 empty empty 100 empty_formed (by decide) (Confined.refl _ _) rfl
  exact absurd bound (by decide)

/-- No proof of the stronger post exists for the actual extraction. -/
theorem stronger_post_rejected : ¬ percentTooStrong.Holds Extracted.program 0 := fun holds => by
  obtain ⟨fuel, final, values, invoked, -, output, rfl, bound⟩ :=
    holds.returning (input := 100) (initial := empty) empty_formed (by decide)
  obtain ⟨otherFuel, otherFinal, otherInvoked⟩ := percent_hundred
  have same := invoke_ok_unique invoked otherInvoked
  simp only [percentTooStrong, DerivedInterface.percentBounded, Prod.mk.injEq, List.cons.injEq,
    Value.scalar.injEq, CIL.Value.i64.injEq, and_true] at same bound
  rw [same.2] at bound
  exact absurd bound (by decide)

/-- The normal-only contract `Percent` meets when its pre excludes every throwing input. -/
def percentInRange : MethodContract CIL.W64 CIL.W64 :=
  { percentExact.toMethodContract with pre := fun value _ => value ≤ 100 }

/-- A weaker pre that admits 101, where `Percent` throws instead of returning. -/
def percentUnguarded : MethodContract CIL.W64 CIL.W64 :=
  { percentInRange with pre := fun _ _ => True }

/-- The in-range contract does not refine the unguarded one. -/
theorem weaker_pre_not_refines : ¬ percentInRange.Refines percentUnguarded := fun refines => by
  have bound : (101 : CIL.W64) ≤ 100 := refines.pre 101 empty trivial
  exact absurd bound (by decide)

/-- No proof of the weaker pre exists for the actual extraction. -/
theorem weaker_pre_rejected : ¬ percentUnguarded.Holds Extracted.program 0 := fun holds => by
  obtain ⟨fuel, final, values, invoked, -⟩ := holds 101 empty trivial
  exact raises_not_returns percent_above invoked

/-- A changed exception type: `Percent(101)` throws `ArgumentOutOfRangeException`, not
    `ArgumentException`. -/
def percentRenamed : OutcomeContract CIL.W64 CIL.W64 :=
  { DerivedInterface.percentBounded with
    raises := fun value _ => if value ≤ 100 then none else some "System.ArgumentException" }

/-- The exact contract does not refine a renamed exception. -/
theorem changed_exception_not_refines : ¬ percentExact.Refines percentRenamed :=
  fun refines => absurd (refines.raises 101 empty empty_formed) (by decide)

/-- No proof of the renamed exception exists for the actual extraction. -/
theorem changed_exception_rejected : ¬ percentRenamed.Holds Extracted.program 0 :=
  fun holds => by
    have renamed : Raises Extracted.program 0 [.scalar (.i64 101)] empty
        "System.ArgumentException" := holds.raising (input := 101) empty_formed (by decide)
    exact absurd (raises_unique renamed percent_above) (by decide)

#print axioms stronger_post_not_refines
#print axioms stronger_post_rejected
#print axioms weaker_pre_not_refines
#print axioms weaker_pre_rejected
#print axioms changed_exception_not_refines
#print axioms changed_exception_rejected

end Rejected

end DerivedPercentProof
