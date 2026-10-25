import CIL.Safety.FixedStepHelpers

/-! Fixed-allocation reference step simulation uses the checked primitive correspondences. -/

namespace CIL.Safety

/-- Subtraction preserves reference offsets, differences and scalar fallback results. -/
theorem Memory.Renamed.stepSubtract {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (operation : CIL.Op)
    (family : fixedStepFamily operation = .subtract) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  allocation_fixed_step skip
#print axioms Memory.Renamed.stepSubtract


/-- Reference comparisons preserve their scalar truth values. -/
theorem Memory.Renamed.stepCompare {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (operation : CIL.Op)
    (family : fixedStepFamily operation = .compare) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  allocation_fixed_step skip
#print axioms Memory.Renamed.stepCompare


/-- Unsigned reference comparisons preserve their branch destinations. -/
theorem Memory.Renamed.stepUnsignedBranch {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (operation : CIL.Op)
    (family : fixedStepFamily operation = .unsignedBranch) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  allocation_fixed_step skip
#print axioms Memory.Renamed.stepUnsignedBranch


/-- Equality and null tests preserve their branch destinations. -/
theorem Memory.Renamed.stepEqualityBranch {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (operation : CIL.Op)
    (family : fixedStepFamily operation = .equalityBranch) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  allocation_fixed_step skip
#print axioms Memory.Renamed.stepEqualityBranch

end CIL.Safety
