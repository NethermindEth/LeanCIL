import CIL.Safety.FixedStepHelpers

/-! Argument loads, calls and returns preserve checked values and control flow. -/

namespace CIL.Safety

/-- Allocation renaming preserves exactly the null managed reference. -/
private theorem managedReference_null_iff (mapping : AllocationRenaming)
    (reference : ManagedReference) :
    mapping.managedReference reference = .null ↔ reference = .null := by
  cases reference <;> simp [AllocationRenaming.managedReference]
#print axioms managedReference_null_iff

/-- Managed metadata identities are stable while checked argument references are renamed. -/
theorem Memory.Renamed.managedStep {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (operation : CIL.ManagedOp) (pc : Nat) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (managedStep operation pc sourceFrame stack source)
      (managedStep operation pc targetFrame (stack.map mapping.value) target) := by
  unfold CIL.Safety.managedStep
  split
  all_goals try simp only [List.map_cons, AllocationRenaming.value]
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals try simp only [List.length_map, ← List.map_take, ← List.map_reverse, ← List.map_drop]
  all_goals repeat' first
    | exact .error _
    | exact .ok (.next related frames)
    | exact .ok (.call related)
    | exact .ok (.tailCall related)
    | (apply (related.checkedValues _ (by
        intro value member
        exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))).bind
       intro first second same
       subst second)
    | contradiction
    | (split <;> try simp only [*, List.map_cons, AllocationRenaming.value,
        Bind.bind, Except.bind, Pure.pure, Except.pure])
  all_goals try simp_all only [reduceCtorEq, forall_const, forall_eq', false_implies, true_implies]
  all_goals cases stack with
  | nil => simp_all [AllocationRenaming.value, managedReference_null_iff]
  | cons head rest =>
    cases head <;> simp_all [AllocationRenaming.value, managedReference_null_iff]
    all_goals cases rest with
    | nil => simp_all [AllocationRenaming.value, managedReference_null_iff]
    | cons head rest =>
      cases head <;> simp_all [AllocationRenaming.value, managedReference_null_iff] <;>
        (exfalso; solve_by_elim)
#print axioms Memory.Renamed.managedStep

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
    | exact related.managedStep frames _ _ _ bounds
    | (case h_54 =>
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
    | (case h_55 =>
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
