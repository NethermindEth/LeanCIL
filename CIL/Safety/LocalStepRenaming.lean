import CIL.Safety.ActionRenaming
import CIL.Safety.LocalStoreRenaming
import CIL.Safety.PureStepRenaming

/-!
# Relocated local steps

Local loads, stores and addresses use the retained declaration index and preserve the active
frame correspondence, including missing-slot rejection.
-/

namespace CIL.Safety

/-- A local load reads the same bounded slot through its relocated operand. -/
theorem Frame.Renamed.stepLocal {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (position pc : Nat) (narrow : Option CIL.NarrowKind)
    (arguments stack : List Value) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.local position narrow) pc arguments sourceFrame stack source)
      (step targetBody (.local (indices.index position) narrow) pc (arguments.map mapping.value)
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

/-- A local address uses its retained byte home at the relocated operand. -/
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
    (sourceBody targetBody : CIL.Method) (position pc : Nat) (narrow : Option CIL.NarrowKind)
    (arguments rest : List Value) (value : Value) (valueBound : value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.setLocal position narrow) pc arguments sourceFrame (value :: rest) source)
      (step targetBody (.setLocal (indices.index position) narrow) pc
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

/-- Vector local loads use the same relocation as ordinary local loads. -/
theorem Frame.Renamed.stepVectorLocal {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (position pc : Nat) (arguments stack : List Value) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.vectorLocal position) pc arguments sourceFrame stack source)
      (step targetBody (.vectorLocal (indices.index position)) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) :=
  frames.stepLocal memories sourceBody targetBody position pc none arguments stack
#print axioms Frame.Renamed.stepVectorLocal

/-- Vector local addresses retain the same relocated byte-home address. -/
theorem Frame.Renamed.stepVectorLocalAddress {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} {sourceFrame targetFrame : Frame}
    (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (position pc : Nat) (arguments stack : List Value) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.vectorLocalAddr position) pc arguments sourceFrame stack source)
      (step targetBody (.vectorLocalAddr (indices.index position)) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) :=
  frames.stepLocalAddress memories sourceBody targetBody position pc arguments stack
#print axioms Frame.Renamed.stepVectorLocalAddress

/-- Vector local stores update the retained slot through the same index map. -/
theorem Frame.Renamed.stepSetVectorLocal {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (position pc : Nat) (arguments rest : List Value)
    (value : Value) (valueBound : value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.setVectorLocal position) pc arguments sourceFrame (value :: rest) source)
      (step targetBody (.setVectorLocal (indices.index position)) pc
        (arguments.map mapping.value) targetFrame ((value :: rest).map mapping.value) target) :=
  frames.stepSetLocal memories sourceBody targetBody position pc none arguments rest value
    valueBound
#print axioms Frame.Renamed.stepSetVectorLocal

end CIL.Safety
