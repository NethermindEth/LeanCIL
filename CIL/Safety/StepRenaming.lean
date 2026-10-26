import CIL.Safety.FixedStepRenaming
import CIL.Safety.NumericStepRenaming
import CIL.Safety.BoundaryStepRenaming
import CIL.Safety.OtherStepRenaming
import CIL.Safety.LocalStepRenaming
import CIL.Safety.AllocatingStepRenaming
import CIL.Safety.ConstructorStepRenaming

/-!+# Concrete checked-step allocation simulation

The dispatcher theorem assembles checked operation proofs and supplies the transport required
by recursive execution. No consumer supplies or assumes a step simulation obligation.
-/

namespace CIL.Safety.StepRenaming

/-- Nonlocal nonallocating instructions retain their exact opcode under local relocation. -/
private theorem fixedOperation (indices : LocalIndexMap) (operation : CIL.Op)
    (fixed : fixedStepFamily operation ≠ .excluded) : indices.operation operation = operation := by
  cases operation <;> try rfl
  all_goals exact False.elim (fixed rfl)
#print axioms fixedOperation

/-- Every observable checked instruction transports its frame and allocation correspondence. -/
theorem stepTransport : StepTransport := by
  intro indices mapping scopes sourceBody targetBody operation pc arguments stack sourceFrame
    targetFrame source target metadata memories frames sourceFormed targetFormed staticBounds
    argumentBounds bounds observable
  cases family : fixedStepFamily operation with
  | reference =>
    rw [fixedOperation indices operation (by rw [family]; intro impossible; cases impossible)]
    exact ⟨mapping, .refl mapping, memories.stepReference frames sourceFormed sourceBody targetBody
      metadata operation family pc arguments stack bounds observable⟩
  | numeric =>
    rw [fixedOperation indices operation (by rw [family]; intro impossible; cases impossible)]
    exact ⟨mapping, .refl mapping, memories.stepNumeric frames sourceFormed sourceBody targetBody
      metadata operation family pc arguments stack bounds observable⟩
  | boundary =>
    rw [fixedOperation indices operation (by rw [family]; intro impossible; cases impossible)]
    exact ⟨mapping, .refl mapping, memories.stepBoundary frames sourceFormed sourceBody targetBody
      metadata operation family pc arguments stack bounds argumentBounds observable⟩
  | other =>
    rw [fixedOperation indices operation (by rw [family]; intro impossible; cases impossible)]
    exact ⟨mapping, .refl mapping, memories.stepOther frames sourceFormed sourceBody targetBody
      metadata operation family pc arguments stack bounds observable⟩
  | excluded =>
    cases operation <;> try cases family
    all_goals dsimp only [LocalIndexMap.operation]
    all_goals first
    | exact memories.stepMemory frames sourceFormed targetFormed staticBounds sourceBody targetBody
        metadata _ pc arguments stack bounds observable
    | exact memories.stepStackAlloc frames sourceFormed targetFormed staticBounds
        sourceBody targetBody _ pc arguments stack observable
    | exact memories.stepNewVector256 frames sourceFormed targetFormed staticBounds
        sourceBody targetBody _ _ pc arguments stack bounds
    | exact memories.stepNewAggregate frames sourceFormed targetFormed staticBounds
        sourceBody targetBody _ _ pc _ arguments stack bounds
    | exact ⟨mapping, .refl mapping,
        frames.stepLocal memories sourceBody targetBody _ pc _ arguments stack⟩
    | exact ⟨mapping, .refl mapping,
        frames.stepLocalAddress memories sourceBody targetBody _ pc arguments stack⟩
    | exact ⟨mapping, .refl mapping,
        frames.stepVectorLocal memories sourceBody targetBody _ pc arguments stack⟩
    | exact ⟨mapping, .refl mapping,
        frames.stepVectorLocalAddress memories sourceBody targetBody _ pc arguments stack⟩
    | (cases stack with
       | nil =>
         simp only [step, observerCount, unspecifiedOperands, List.take_nil, List.any_nil,
           Bool.false_or, Bool.false_eq_true, ite_false, pureArity, instruction] at observable
         cases observable
       | cons value rest =>
         first
         | exact ⟨mapping, .refl mapping,
             frames.stepSetLocal memories sourceBody targetBody _ pc _ arguments rest value
               (bounds value (List.mem_cons_self ..))⟩
         | exact ⟨mapping, .refl mapping,
             frames.stepSetVectorLocal memories sourceBody targetBody _ pc arguments rest value
               (bounds value (List.mem_cons_self ..))⟩)
#print axioms stepTransport

end CIL.Safety.StepRenaming
