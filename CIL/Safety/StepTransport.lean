import CIL.Safety.ActionRenaming
import CIL.Safety.MemoryInstructionRenaming

/-!
# The one-step allocation-renaming obligation

Execution composition consumes this checked-step interface. The concrete dispatcher proof
supplies it independently of recursive runs or consumer postconditions.
-/

namespace CIL.Safety

/-- Execution metadata unaffected by deleting and relocating local declarations. -/
structure StepMetadata (source target : CIL.Method) : Prop where
  profile : target.profile = source.profile
  returnsValue : target.returnsValue = source.returnsValue
  staticSites : target.staticSites = source.staticSites

/-- One observable checked step transports frames, values and fresh allocation correspondence. -/
def StepTransport : Prop :=
  ∀ (indices : LocalIndexMap) (mapping : AllocationRenaming) (scopes : Nat → Nat → Prop)
    (sourceBody targetBody : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (arguments stack : List Value) (sourceFrame targetFrame : Frame) (source target : Memory),
    StepMetadata sourceBody targetBody →
    Memory.Renamed mapping scopes source target →
    Frame.Renamed indices mapping scopes sourceFrame targetFrame →
    source.WellFormed → target.WellFormed →
    (∀ binding ∈ source.staticBindings, binding.2.allocation < mapping.sourceLimit) →
    (∀ value ∈ arguments, value.Below mapping.sourceLimit) →
    (∀ value ∈ stack, value.Below mapping.sourceLimit) →
    SuccessOrThrow (step sourceBody operation pc arguments sourceFrame stack source) →
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody operation pc arguments sourceFrame stack source)
        (step targetBody (indices.operation operation) pc (arguments.map mapping.value)
          targetFrame (stack.map mapping.value) target)

end CIL.Safety
