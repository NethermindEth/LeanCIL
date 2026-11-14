import CIL.Safety.ActionRenaming
import CIL.Safety.LocalStoreRenaming
import CIL.Safety.PureStepRenaming
import CIL.Safety.MemoryInstructionRenaming
import CIL.Safety.SpanConstructionLemmas

/-!
# Relocated local steps

Local loads, stores and addresses use the retained declaration index and preserve the active
frame correspondence, including missing-slot rejection.
-/

namespace CIL.Safety

/-- Initializing a span local preserves its relocated slot and backing allocation identity. -/
theorem Frame.Renamed.stepInitializeSpanLocal {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} {sourceFrame targetFrame : Frame}
    (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (position pc : Nat) (constructor : CIL.SpanConstructor) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.initializeSpanLocal position constructor) pc arguments
        sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.initializeSpanLocal position constructor) pc arguments
        sourceFrame stack source)
      (step targetBody (.initializeSpanLocal (indices.index position) constructor) pc
        (arguments.map mapping.value) targetFrame (stack.map mapping.value) target) := by
  simp only [step, observerCount, Bool.or_false, mapping.unspecifiedOperands] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    have slots := frames.locals.getElem?_all position
    generalize sourceFound : sourceFrame.locals[position]? = sourceSlot at slots observable ⊢
    generalize targetFound : targetFrame.locals[indices.index position]? = targetSlot at slots ⊢
    cases slots with
    | none => exact .error .invalidState
    | @some slot otherSlot slots =>
      rcases slots with ⟨bounded, rfl⟩
      apply (memories.memoryInstructionResult _ formed stack bounds observable.bind_left).bindWithSuccess
      intro result otherResult constructed results
      obtain ⟨after, values⟩ := result
      obtain ⟨otherAfter, otherValues⟩ := otherResult
      obtain ⟨related, rfl⟩ := results
      cases values with
      | nil => exact .error .invalidState
      | cons value rest =>
        obtain ⟨sameMemory, valid⟩ :=
          spanConstructor_result constructor source after stack value rest constructed
        subst after
        have valueBound : value.Below mapping.sourceLimit := by
          rw [memories.sourceLimit]
          exact valid.below formed
        apply (related.storeLocal slot value bounded valueBound).bindWithSuccess
        intro result otherResult stored results
        obtain ⟨slotAfter, sourceAfter⟩ := result
        obtain ⟨otherSlotAfter, targetAfter⟩ := otherResult
        rcases results with ⟨slotsEqual, related⟩
        change otherSlotAfter = mapping.localSlot slotAfter at slotsEqual
        subst otherSlotAfter
        have positionBound : position < indices.sourceLength := by
          rw [← frames.locals.lengths.1]
          exact (List.getElem?_eq_some_iff.mp sourceFound).1
        exact .ok (.next related (frames.setLocal position positionBound slotAfter
          (storeLocal_below bounded valueBound stored)))

#print axioms Frame.Renamed.stepInitializeSpanLocal

/-- A local load reads the same bounded slot through its relocated operand. -/
theorem Frame.Renamed.stepLocal {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (position pc : Nat) (arguments stack : List Value) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.local position) pc arguments sourceFrame stack source)
      (step targetBody (.local (indices.index position)) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
    Bool.false_or, Bool.false_eq_true, ite_false]
  have slots := frames.locals.getElem?_all position
  generalize sourceFound : sourceFrame.locals[position]? = sourceSlot at slots ⊢
  generalize targetFound : targetFrame.locals[indices.index position]? = targetSlot at slots ⊢
  cases slots with
  | none => exact .error .invalidState
  | @some slot otherSlot slots =>
    rcases slots with ⟨bounded, rfl⟩
    apply (memories.loadLocal slot bounded).bindWithSuccess
    intro value otherValue loaded same
    subst otherValue
    exact .ok (.next memories frames)
#print axioms Frame.Renamed.stepLocal

/-- A local address uses its retained byte home or span view at the relocated operand. -/
theorem Frame.Renamed.stepLocalAddress {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (position pc : Nat)
    (arguments stack : List Value) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.localAddr position) pc arguments sourceFrame stack source)
      (step targetBody (.localAddr (indices.index position)) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
    Bool.false_or, Bool.false_eq_true, ite_false]
  have slots := frames.locals.getElem?_all position
  generalize sourceFound : sourceFrame.locals[position]? = sourceSlot at slots ⊢
  generalize targetFound : targetFrame.locals[indices.index position]? = targetSlot at slots ⊢
  cases slots with
  | none => exact .error .invalidState
  | @some slot otherSlot slots =>
    rcases slots with ⟨bounded, rfl⟩
    apply (memories.localAddress slot bounded).bindWithSuccess
    intro value otherValue loaded same
    subst otherValue
    exact .ok (.next memories frames)
#print axioms Frame.Renamed.stepLocalAddress

/-- A local store updates the corresponding slot without exposing private dead homes. -/
theorem Frame.Renamed.stepSetLocal {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (position pc : Nat)
    (arguments rest : List Value) (value : Value) (valueBound : value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.setLocal position) pc arguments sourceFrame (value :: rest) source)
      (step targetBody (.setLocal (indices.index position)) pc
        (arguments.map mapping.value) targetFrame ((value :: rest).map mapping.value) target) := by
  simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
    Bool.false_or, Bool.false_eq_true, ite_false, List.map_cons]
  have slots := frames.locals.getElem?_all position
  generalize sourceFound : sourceFrame.locals[position]? = sourceSlot at slots ⊢
  generalize targetFound : targetFrame.locals[indices.index position]? = targetSlot at slots ⊢
  cases slots with
  | none => exact .error .invalidState
  | @some slot otherSlot slots =>
    rcases slots with ⟨bounded, rfl⟩
    apply (memories.storeLocal slot value bounded valueBound).bindWithSuccess
    intro result otherResult stored results
    obtain ⟨slotAfter, sourceAfter⟩ := result
    obtain ⟨otherSlotAfter, targetAfter⟩ := otherResult
    rcases results with ⟨slotsEqual, memories⟩
    change otherSlotAfter = mapping.localSlot slotAfter at slotsEqual
    subst otherSlotAfter
    have positionBound : position < indices.sourceLength := by
      rw [← frames.locals.lengths.1]
      exact (List.getElem?_eq_some_iff.mp sourceFound).1
    have updated := frames.setLocal position positionBound slotAfter
      (storeLocal_below bounded valueBound stored)
    exact .ok (.next memories updated)
#print axioms Frame.Renamed.stepSetLocal

end CIL.Safety
