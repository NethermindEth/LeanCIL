import CIL.Safety.SymbolicExecution

/-!
# Composable instruction segments

A `Segment` is a checked run-to-run contract between two instruction positions. Its witness
records the intermediate frame, stack and memory and the exact additional fuel. Contracts
compose without executing the prefix again, and retain all arguments and runtime premises.
-/

namespace CIL.Safety

/-- The mutable state visible at an instruction boundary. Method arguments stay fixed. -/
structure SegmentState where
  frame : Frame
  stack : List Value
  memory : Memory

/-- An exact state assertion retains method arguments as well as frame, stack and memory. -/
def SegmentState.exact (arguments : List Value) (state : SegmentState) :
    List Value → SegmentState → Prop := fun actual current => actual = arguments ∧ current = state
/-- A prefix consumes `cost` fuel and leaves the same continuation at `finish`, for every
    continuation fuel. This preserves successful results and located faults alike. -/
def SegmentRun (program : CIL.Program) (method start finish cost : Nat)
    (arguments : List Value) (before after : SegmentState) : Prop :=
  ∀ fuel, run program (fuel + cost) method start arguments before.frame before.stack
    before.memory = run program fuel method finish arguments after.frame after.stack after.memory

/-- Every input satisfying `pre` has an intermediate state satisfying `post` and an exact
    run-to-run fuel equation. Preconditions may depend on the unchanged method arguments. -/
def Segment (program : CIL.Program) (method start finish : Nat)
    (pre post : List Value → SegmentState → Prop) : Prop :=
  ∀ arguments before, pre arguments before →
    ∃ cost after, post arguments after ∧
      SegmentRun program method start finish cost arguments before after

namespace SegmentRun

/-- An empty prefix retains the whole state and costs no fuel. -/
theorem refl (program : CIL.Program) (method pc : Nat) (arguments : List Value)
    (state : SegmentState) : SegmentRun program method pc pc 0 arguments state state := by
  intro fuel
  rfl

#print axioms refl

/-- Adjacent prefixes add their fuel costs and retain the exact final continuation. -/
theorem trans {program : CIL.Program} {method start middle finish firstCost secondCost : Nat}
    {arguments : List Value} {before intermediate after : SegmentState}
    (first : SegmentRun program method start middle firstCost arguments before intermediate)
    (second : SegmentRun program method middle finish secondCost arguments intermediate after) :
    SegmentRun program method start finish (firstCost + secondCost) arguments before after := by
  intro fuel
  rw [show fuel + (firstCost + secondCost) = (fuel + secondCost) + firstCost by omega]
  exact (first (fuel + secondCost)).trans (second fuel)

#print axioms trans

end SegmentRun

namespace Segment

/-- A checked boundary equation yields a contract with exact input and output states. -/
theorem ofRun {program : CIL.Program} {method start finish cost : Nat}
    {arguments : List Value} {before after : SegmentState}
    (execution : SegmentRun program method start finish cost arguments before after) :
    Segment program method start finish (before.exact arguments) (after.exact arguments) := by
  intro actual current valid
  rcases valid with ⟨rfl, rfl⟩
  exact ⟨cost, after, ⟨rfl, rfl⟩, execution⟩

#print axioms ofRun
/-- An empty segment preserves any assertion. -/
theorem refl (program : CIL.Program) (method pc : Nat)
    (predicate : List Value → SegmentState → Prop) :
    Segment program method pc pc predicate predicate := by
  intro arguments state valid
  exact ⟨0, state, valid, SegmentRun.refl program method pc arguments state⟩

#print axioms refl

/-- Sequential composition uses the first segment's postcondition as the second's precondition. -/
theorem trans {program : CIL.Program} {method start middle finish : Nat}
    {pre intermediate post : List Value → SegmentState → Prop}
    (first : Segment program method start middle pre intermediate)
    (second : Segment program method middle finish intermediate post) :
    Segment program method start finish pre post := by
  intro arguments before valid
  obtain ⟨firstCost, middleState, middleValid, firstRun⟩ := first arguments before valid
  obtain ⟨secondCost, after, afterValid, secondRun⟩ := second arguments middleState middleValid
  exact ⟨firstCost + secondCost, after, afterValid, firstRun.trans secondRun⟩

#print axioms trans

/-- Strengthening the precondition and weakening the postcondition retains the same witnesses. -/
theorem consequence {program : CIL.Program} {method start finish : Nat}
    {pre post stronger weaker : List Value → SegmentState → Prop}
    (contract : Segment program method start finish pre post)
    (input : ∀ arguments state, stronger arguments state → pre arguments state)
    (output : ∀ arguments state, post arguments state → weaker arguments state) :
    Segment program method start finish stronger weaker := by
  intro arguments before valid
  obtain ⟨cost, after, result, execution⟩ := contract arguments before (input _ _ valid)
  exact ⟨cost, after, output _ _ result, execution⟩

#print axioms consequence

/-- A successful continuation after a segment yields the same result before the segment.
    This bridges composable boundary contracts to existential-fuel consumer proofs. -/
theorem run_exists {program : CIL.Program} {method start finish : Nat}
    {pre post : List Value → SegmentState → Prop}
    (contract : Segment program method start finish pre post)
    (arguments : List Value) (before : SegmentState) (valid : pre arguments before)
    (result : Memory → List Value → Prop)
    (continuation : ∀ after, post arguments after → ∃ fuel memory returned,
      run program fuel method finish arguments after.frame after.stack after.memory =
        .ok (memory, returned) ∧ result memory returned) :
    ∃ fuel memory returned,
      run program fuel method start arguments before.frame before.stack before.memory =
        .ok (memory, returned) ∧ result memory returned := by
  obtain ⟨cost, after, afterValid, execution⟩ := contract arguments before valid
  obtain ⟨fuel, memory, returned, finished, correct⟩ := continuation after afterValid
  exact ⟨fuel + cost, memory, returned, (execution fuel).trans finished, correct⟩

#print axioms run_exists
end Segment

/-- Prove a supplied segment boundary equation with the checked instruction stepper. The
    witness, postcondition and fuel cost remain explicit proof obligations. -/
macro "cil_segment_steps" "[" facts:term,* "]" : tactic =>
  `(tactic| cil_strict (focus (intro fuel; cil_checked_steps [$facts,*]; done)))

/-- Prove an exact-state segment contract with a stated fuel cost and checked placements. -/
macro "cil_segment " cost:num " [" facts:term,* "]" : tactic =>
  `(tactic| cil_strict (focus (
    apply Segment.ofRun (cost := $cost)
    cil_segment_steps [$facts,*])))

end CIL.Safety
