import CIL.Safety.StepTransport
import CIL.Safety.StepComposition
import CIL.Safety.StaticInstructionRenaming
import CIL.Safety.StackAllocationRenaming

/-!
# Checked allocating instruction steps

Static storage and dynamic stack storage extend allocation maps while keeping retained frames,
operand checks and named exceptions consistent with the actual checked dispatcher.
The memory case reuses the checked step equation instead of simplifying the full dispatcher.
-/

namespace CIL.Safety

/-- Static dispatch depends on extraction-bound descriptors, not unrelated method metadata. -/
theorem staticInstruction_metadata {sourceBody targetBody : CIL.Method}
    (metadata : StepMetadata sourceBody targetBody) (pc : Nat) (operation : CIL.MemoryOp)
    (stack : List Value) (memory : Memory) :
    staticInstruction targetBody pc operation stack memory =
      staticInstruction sourceBody pc operation stack memory := by
  unfold staticInstruction
  rw [metadata.staticSites]
#print axioms staticInstruction_metadata

/-- Checked static-memory steps extend the map only when their actual operation allocates. -/
theorem Memory.Renamed.stepMemory {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceBody targetBody : CIL.Method) (metadata : StepMetadata sourceBody targetBody)
    (operation : CIL.MemoryOp) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.memory operation) pc arguments sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody (.memory operation) pc arguments sourceFrame stack source)
        (step targetBody (.memory operation) pc (arguments.map mapping.value)
          targetFrame (stack.map mapping.value) target) := by
  simp only [step_memory_eq, mapping.unspecifiedOperands] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false,
      staticInstruction_metadata metadata] at observable ⊢
    obtain ⟨later, extension, operations⟩ := related.staticInstructionResult sourceFormed
      targetFormed staticBounds sourceBody pc operation stack bounds observable.bind_left
    refine ⟨later, extension, ?_⟩
    apply operations.bind
    intro first second result
    rcases first with ⟨sourceAfter, values⟩
    rcases second with ⟨targetAfter, targetValues⟩
    rcases result with ⟨memories, rfl⟩
    exact .ok (.next memories (frames.extend extension (fun _ _ scope => scope)))
#print axioms Memory.Renamed.stepMemory

/-- Stack allocation faults are resource or memory failures, never named CLR exceptions. -/
theorem allocateStack_not_thrown (memory : Memory) (frame : Frame) (size : Nat)
    (initLocals : Bool) (exception : String) :
    allocateStack memory frame size initLocals ≠ .error (.thrown exception) := by
  intro raised
  unfold allocateStack allocateHome checkedAt at raised
  repeat' first
    | cases raised
    | split at raised
    | simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at raised
  all_goals rename_i found
  all_goals split at found <;> cases found
  all_goals rename_i found
  all_goals split at found <;> cases found
#print axioms allocateStack_not_thrown

/-- Actual dynamic stack steps extend ownership and preserve exact quota and initialization rules.
    -/
theorem Memory.Renamed.stepStackAlloc {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceBody targetBody : CIL.Method) (initLocals : Bool) (pc : Nat)
    (arguments stack : List Value)
    (observable : SuccessOrThrow
      (step sourceBody (.stackAlloc initLocals) pc arguments sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody (.stackAlloc initLocals) pc arguments sourceFrame stack source)
        (step targetBody (.stackAlloc initLocals) pc (arguments.map mapping.value)
          targetFrame (stack.map mapping.value) target) := by
  simp only [step, Bool.or_false, mapping.unspecifiedOperands] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    split at observable <;> try contradiction
    · rename_i size same
      cases same
      simp only [List.map_cons, List.map_nil, AllocationRenaming.value]
      cases size <;> simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at observable ⊢
      all_goals try cases observable
      all_goals rename_i bits
      all_goals
        cases allocated : CIL.Safety.allocateStack source sourceFrame bits.toNat initLocals with
        | error fault =>
          cases fault <;> simp only [allocated, SuccessOrThrow] at observable
          rename_i exception
          exact False.elim (allocateStack_not_thrown source sourceFrame _ initLocals
            exception allocated)
        | ok result =>
          obtain ⟨reference, finalFrame, finalMemory⟩ := result
          obtain ⟨later, targetReference, targetFinal, targetAfter, extension, targetAllocated,
            referenceEqual, finalFrames, memories⟩ :=
            related.allocateStack frames sourceFormed targetFormed staticBounds _ initLocals
              reference allocated
          subst targetReference
          refine ⟨later, extension, ?_⟩
          simp only [targetAllocated]
          exact .ok (.next memories finalFrames)
    · simp only [pureArity, instruction] at observable
      split at observable <;> cases observable
#print axioms Memory.Renamed.stepStackAlloc

end CIL.Safety
