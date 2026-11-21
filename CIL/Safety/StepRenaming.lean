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
private theorem fixedOperation (indices : LocalIndexMap) (operation : CIL.Instruction)
    (fixed : fixedStepFamily operation ≠ .excluded) : indices.operation operation = operation := by
  cases operation <;> try rfl
  all_goals exact False.elim (fixed rfl)
#print axioms fixedOperation

set_option maxHeartbeats 400000 in
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
    case newarr.refl element =>
      exact memories.stepNewarr frames sourceFormed targetFormed staticBounds
        sourceBody targetBody metadata element pc arguments stack bounds observable
    case newobj.refl constructor =>
      exact memories.stepNewobj frames sourceFormed targetFormed staticBounds sourceBody
        targetBody constructor pc metadata arguments stack bounds observable
    case ldobj.refl | stobj.refl | cpobj.refl | initobj.refl | sizeof.refl =>
      refine ⟨mapping, .refl mapping, ?_⟩
      simp only [LocalIndexMap.operation, step, observerCount, indices.unspecifiedOperands mapping,
        Extraction.CallLayouts.valueShape_eq, Method.valueShape, metadata.environment]
        at observable ⊢
      rename_i type
      first
        | (let count := if Extraction.spanLocal type then 0 else 1
           change SuccessOrThrow (if unspecifiedOperands count stack then _ else _) at observable)
        | (let count := 2
           change SuccessOrThrow (if unspecifiedOperands count stack then _ else _) at observable)
        | (let count := 1
           change SuccessOrThrow (if unspecifiedOperands count stack then _ else _) at observable)
        | (let count := 0
           change SuccessOrThrow (if unspecifiedOperands count stack then _ else _) at observable)
      by_cases observed : unspecifiedOperands count stack = true <;>
        simp only [count] at observed observable <;>
        simp only [observed, Bool.false_eq_true, ite_true, ite_false] at observable ⊢
      all_goals try exact .error _
      all_goals try cases width : (sourceBody.environment.valueShape type).size? <;>
        simp only [width] at observable ⊢
      all_goals try exact .error _
      all_goals first
        | exact .ok (.next memories frames)
        | (cases shape : sourceBody.environment.valueShape type <;>
             simp only [shape] at observable ⊢ <;>
             first
             | exact .error _
             | exact frames.initializeSpanHome memories pc stack)
        | (first
            | apply (memories.copyInitializedBytesResult _ sourceFormed stack bounds
                observable.bind_left).bind
            | apply (memories.initializeBytesResult _ sourceFormed stack bounds
                observable.bind_left).bind
            | apply (memories.transferObjectResult _ _ sourceFormed stack bounds
                observable.bind_left).bind
           rintro ⟨_, _⟩ ⟨_, _⟩ ⟨related, rfl⟩
           exact .ok (.next related frames))
        | (apply (frames.viewOperands memories _ stack bounds).bindWithSuccess
           intro viewed otherViewed sourceViewed operandsRelated
           obtain ⟨rfl, viewedBounds⟩ := operandsRelated
           apply (memories.transferObjectResult _ _ sourceFormed viewed viewedBounds
             (observable.bind_right sourceViewed).bind_left).bind
           rintro ⟨_, _⟩ ⟨_, _⟩ ⟨related, rfl⟩
           exact .ok (.next related frames))
    case ldelem_any.refl element =>
      exact ⟨mapping, .refl mapping, memories.stepLdelemAny frames sourceFormed sourceBody
        targetBody metadata element pc arguments stack bounds observable⟩
    case stelem_any.refl element =>
      exact ⟨mapping, .refl mapping, memories.stepStelemAny frames sourceFormed sourceBody
        targetBody metadata element pc arguments stack bounds observable⟩
    case ldelema.refl element readOnly =>
      exact ⟨mapping, .refl mapping, memories.stepLdelema frames sourceFormed sourceBody
        targetBody metadata element readOnly pc arguments stack bounds observable⟩
    case cpblk.refl alignment | initblk.refl alignment =>
      refine ⟨mapping, .refl mapping, ?_⟩
      simp only [LocalIndexMap.operation, step, observerCount, indices.unspecifiedOperands mapping]
        at observable ⊢
      by_cases observed : unspecifiedOperands 3 stack = true <;>
        simp only [observed, Bool.false_eq_true, ite_true, ite_false] at observable ⊢
      · exact .error _
      first
      | apply (memories.blockBytesResult true alignment stack bounds
          observable.bind_left).bind
      | apply (memories.blockBytesResult false alignment stack bounds
          observable.bind_left).bind
      rintro ⟨_, _⟩ ⟨_, _⟩ ⟨related, rfl⟩
      exact .ok (.next related frames)
    case ldstr.refl text =>
      refine ⟨mapping, .refl mapping, ?_⟩
      change SuccessOrThrow (do
        let (memory, values) ← stringLiteralInstruction text stack source
        return FrameAction.next (pc + 1) values sourceFrame memory) at observable
      apply (memories.stringLiteralInstructionResult sourceFormed text stack observable.bind_left).bind
      rintro ⟨_, _⟩ ⟨_, _⟩ ⟨related, rfl⟩
      exact .ok (.next related frames)
    case ldsfld.refl field =>
      exact ⟨mapping, .refl mapping, memories.stepLdsfld frames staticBounds sourceBody
        targetBody metadata field pc arguments stack⟩
    case ldsflda.refl field =>
      exact memories.stepStaticAddress frames sourceFormed targetFormed staticBounds sourceBody
        targetBody metadata _ (fun _ _ _ _ _ _ => rfl) pc arguments stack bounds
        observable
    case ldtoken.refl operand =>
      cases operand with
      | type type => exact ⟨mapping, .refl mapping, .ok (.next memories frames)⟩
      | field field =>
        exact memories.stepStaticAddress frames sourceFormed targetFormed staticBounds sourceBody
          targetBody metadata _ (fun _ _ _ _ _ _ => rfl) pc arguments stack bounds observable
    case stsfld.refl field =>
      refine ⟨mapping, .refl mapping, ?_⟩
      dsimp only [LocalIndexMap.operation]
      rw [step_stsfld_eq, step_stsfld_eq, indices.unspecifiedOperands mapping]
      split <;> exact .error _
    case ldfld.refl field =>
      exact memories.stepFieldLoad frames sourceFormed sourceBody targetBody metadata field pc
        arguments stack bounds observable
    case stfld.refl field =>
      exact memories.stepFieldStore frames sourceFormed sourceBody targetBody metadata field pc
        arguments stack bounds observable
    case ldflda.refl field =>
      exact memories.stepFieldAddress frames sourceFormed sourceBody targetBody metadata field pc
        arguments stack bounds observable
    all_goals dsimp only [LocalIndexMap.operation]
    all_goals first
    | exact memories.stepMemory frames sourceFormed sourceBody targetBody _ pc arguments stack
        bounds observable
    | exact memories.stepLocalloc frames sourceFormed targetFormed staticBounds
        sourceBody targetBody metadata.declared pc arguments stack observable
    | exact ⟨mapping, .refl mapping,
        frames.stepLdloc memories sourceBody targetBody _ pc arguments stack⟩
    | exact ⟨mapping, .refl mapping,
        frames.stepLdloca memories sourceBody targetBody _ pc arguments stack⟩
    | (cases stack with
       | nil =>
         simp only [step, observerCount, unspecifiedOperands, List.take_nil, List.any_nil,
           Bool.false_eq_true, ite_false, pureArity, instruction] at observable
         cases observable
       | cons value rest =>
         exact ⟨mapping, .refl mapping,
           frames.stepStloc memories sourceBody targetBody _ pc arguments rest value
             (bounds value (List.mem_cons_self ..))⟩)
#print axioms stepTransport

end CIL.Safety.StepRenaming
