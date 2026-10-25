import CIL.Safety.FixedStepHelpers

/-! Other nonallocating steps reuse the checked ordinary dispatcher fallback. -/

namespace CIL.Safety

/-- The remaining nonallocating operations preserve checked results and control flow. -/
theorem Memory.Renamed.stepOther {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (operation : CIL.Op)
    (family : fixedStepFamily operation = .other) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  allocation_fixed_step skip
#print axioms Memory.Renamed.stepOther

end CIL.Safety
