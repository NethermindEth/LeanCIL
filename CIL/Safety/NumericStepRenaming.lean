import CIL.Safety.FixedStepHelpers

/-! Checked numeric operations preserve scalar results under allocation renaming. -/

namespace CIL.Safety

/-- Numeric operations preserve checked scalar results and exact diagnostics. -/
theorem Memory.Renamed.stepNumeric {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (operation : CIL.Op)
    (family : fixedStepFamily operation = .numeric) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  allocation_fixed_step (
  all_goals try simp only [List.length_map, ← List.map_take, ← List.map_drop,
    ← List.map_reverse, List.map_cons, AllocationRenaming.value]
  all_goals repeat first
    | exact .error _
    | exact .ok (.next related frames)
    | (apply (ResultRenamed.arithmetic mapping _).bind
       intro first second same
       subst second)
    | (apply (mapping.scalarOperands _).bind
       intro first second same
       subst second)
    | (apply (mapping.checkedIntrinsic _ _).bind
       intro first second same
       subst second)
    | (apply (related.checkedValue _ (by trivial)).bind
       intro first second same
       subst second
       exact .ok (.next related frames))
    | (apply (related.scalarChecks _).bind
       intro first second same
       subst second
       simp only [← List.map_append]
       exact .ok (.next related frames))
    | (split <;> try simp only [*, Bool.false_eq_true, ite_false])
  skip)
#print axioms Memory.Renamed.stepNumeric

end CIL.Safety
