import CIL.Safety.FixedStepHelpers

/-! Argument loads, calls and returns preserve checked values and control flow. -/

namespace CIL.Safety

/-- Argument loads, calls and returns preserve their checked values and control flow. -/
theorem Memory.Renamed.stepBoundary {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (operation : CIL.Op)
    (family : fixedStepFamily operation = .boundary) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (argumentBounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  allocation_fixed_step (
    first
    | (case h_53 =>
        rename_i _ _ position
        rw [List.getElem?_map]
        cases found : arguments[position]? with
        | none => exact .error .invalidState
        | some value =>
          apply (related.checkedValue value
            (argumentBounds value (List.mem_of_getElem? found))).bind
          intro first second same
          subst second
          exact .ok (.next related frames))
    | (case h_54 =>
        rename_i _ _ position kind
        rw [List.getElem?_map]
        cases found : arguments[position]? with
        | none => exact .error .invalidState
        | some value =>
          cases value <;> try exact .error .invalidState
          rename_i scalar
          cases scalar <;> try exact .error .invalidState
          apply (related.checkedValue _ (by trivial)).bind
          intro first second same
          subst second
          exact .ok (.next related frames))
    | (apply (frames.argumentHome _).bind
       intro slot otherSlot slots
       rcases slots with ⟨bounded, rfl⟩
       first
       | (apply (related.loadLocal slot bounded).bind
          intro first second same
          subst second
          exact .ok (.next related frames))
       | (apply (related.localAddress slot bounded).bind
          intro first second same
          subst second
          exact .ok (.next related frames)))
    | (try simp only [List.map_nil, List.length_map, ← List.map_take, ← List.map_drop,
         ← List.map_reverse, metadata.returnsValue]
       repeat first
       | exact .error _
       | exact .ok (.returned related)
       | exact .ok (.call related)
       | exact .ok (.tailCall related)
       | (apply (related.checkedValues _ (by assumption)).bind
          intro first second same
          subst second)
       | (apply (related.checkedValues _ (by
            intro value member
            exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))).bind
          intro first second same
          subst second)
       | (apply (related.checkedValues _ (by
            intro value member
            exact bounds value (List.mem_reverse.mp member))).bind
          intro first second same
          subst second)
       | (apply (related.scalarChecks _).bind
          intro first second same
          subst second)
       | (split <;> try simp only [*, Bool.false_eq_true, ite_false])
       skip))
#print axioms Memory.Renamed.stepBoundary

end CIL.Safety
