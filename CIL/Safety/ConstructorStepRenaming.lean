import CIL.Safety.StepTransport
import CIL.Safety.CheckedValueRenaming
import CIL.Safety.CheckedReferenceBounds
import CIL.Safety.ValueMemoryRenaming
import CIL.Safety.FrameHomeRenaming
import CIL.Safety.LocalStoreRenaming

/-!+# Constructor temporary storage under allocation renaming

Constructor storage extends the current correspondence before the child invocation. The caller
retains ownership and both initial argument lists refer to the same mapped older allocations.
-/

namespace CIL.Safety

/-- A failed checked prefix reports the corresponding fault before any allocation occurs. -/
private theorem renamed_failure {mapping : AllocationRenaming} {relation : α → β → Prop}
    {fault : ExecutionFault} {target : ExecutionResult β}
    (related : ResultRenamed mapping relation (.error fault) target) :
    target = .error (mapping.fault fault) := by cases related; rfl
#print axioms renamed_failure

/-- A vector constructor reserves corresponding initialized storage owned by the caller. -/
theorem Memory.Renamed.stepNewVector256 {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceBody targetBody : CIL.Method) (callee argc pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody (.newVector256 callee argc) pc arguments sourceFrame stack source)
        (step targetBody (.newVector256 callee argc) pc (arguments.map mapping.value)
          targetFrame (stack.map mapping.value) target) := by
  simp only [step, mapping.unspecifiedOperands, Bool.or_false, List.length_map,
    ← List.map_take, ← List.map_drop, ← List.map_reverse]
  split
  · exact ⟨mapping, .refl mapping, .error _⟩
  · split
    · exact ⟨mapping, .refl mapping, .error _⟩
    · have checks := related.checkedValues (stack.take argc).reverse (by
        intro value member
        exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))
      cases checked : (stack.take argc).reverse.mapM (CIL.Safety.checkedValue source) with
      | error fault =>
        rw [checked] at checks
        rw [renamed_failure checks]
        exact ⟨mapping, .refl mapping, .error fault⟩
      | ok operands =>
        have operandBounds : ∀ value ∈ operands, value.Below mapping.sourceLimit := by
          intro value member
          rw [related.sourceLimit]
          exact ((checkedValues_valid _ _ _ checked).2 value member).below sourceFormed
        rw [checked] at checks
        obtain ⟨targetOperands, targetChecked, rfl⟩ := checks.success
        obtain ⟨sourceHome, targetHome, sourceMade, targetMade, homes⟩ :=
          related.allocateHome sourceFormed targetFormed staticBounds sourceFrame.activation
            targetFrame.activation (localWidth .vector256) 1 frames.activation
            (by decide) (by decide)
        have freshBound : source.nextIdentity < mapping.allocate.sourceLimit := by
          rw [← related.sourceLimit]
          exact Nat.lt_succ_self _
        have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
          rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
        have owned := (frames.extend mapping.allocate_extends (fun _ _ scope => scope)).addOwned
          source.nextIdentity freshBound 0
        simp only [Nat.add_zero, freshImage] at owned
        have stored := homes.storeValue (.address ⟨source.nextIdentity, 0⟩) freshBound (.v256 0)
        simp only [AllocationRenaming.managedReference, AllocationRenaming.reference,
          freshImage] at stored
        refine ⟨mapping.allocate, mapping.allocate_extends, ?_⟩
        simp only [targetChecked, sourceMade, targetMade, Bind.bind, Except.bind]
        apply stored.bind
        intro sourceStored targetStored memories
        have operandsSame := mapping.allocate_extends.values operands operandBounds
        have restSame := mapping.allocate_extends.values (stack.drop argc) (by
          intro value member
          exact bounds value (List.mem_of_mem_drop member))
        rw [← operandsSame, ← restSame]
        simpa only [List.map_cons, AllocationRenaming.value,
          AllocationRenaming.managedReference, AllocationRenaming.reference, freshImage,
          Pure.pure, Except.pure] using
          ResultRenamed.ok (FrameAction.Renamed.construct (callee := callee)
            (arguments := .reference (.address ⟨source.nextIdentity, 0⟩) :: operands)
            (rest := stack.drop argc) (temporary := ⟨source.nextIdentity, 0⟩)
            (kind := .vector256) memories owned freshBound)
#print axioms Memory.Renamed.stepNewVector256

/-- An aggregate constructor reserves corresponding initialized storage owned by the caller. -/
theorem Memory.Renamed.stepNewAggregate {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceBody targetBody : CIL.Method) (callee argc pc : Nat) (size : Fin (2 ^ 64))
    (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody (.newAggregate callee argc size) pc arguments sourceFrame stack source)
        (step targetBody (.newAggregate callee argc size) pc (arguments.map mapping.value)
          targetFrame (stack.map mapping.value) target) := by
  simp only [step, mapping.unspecifiedOperands, Bool.or_false, List.length_map,
    ← List.map_take, ← List.map_drop, ← List.map_reverse]
  split
  · exact ⟨mapping, .refl mapping, .error _⟩
  · split
    · exact ⟨mapping, .refl mapping, .error _⟩
    · have checks := related.checkedValues (stack.take argc).reverse (by
        intro value member
        exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))
      cases checked : (stack.take argc).reverse.mapM (CIL.Safety.checkedValue source) with
      | error fault =>
        rw [checked] at checks
        rw [renamed_failure checks]
        exact ⟨mapping, .refl mapping, .error fault⟩
      | ok operands =>
        have operandBounds : ∀ value ∈ operands, value.Below mapping.sourceLimit := by
          intro value member
          rw [related.sourceLimit]
          exact ((checkedValues_valid _ _ _ checked).2 value member).below sourceFormed
        rw [checked] at checks
        obtain ⟨targetOperands, targetChecked, rfl⟩ := checks.success
        obtain ⟨sourceHome, targetHome, sourceMade, targetMade, homes⟩ :=
          related.allocateHome sourceFormed targetFormed staticBounds sourceFrame.activation
            targetFrame.activation size 1 frames.activation size.isLt (by decide)
        have freshBound : source.nextIdentity < mapping.allocate.sourceLimit := by
          rw [← related.sourceLimit]
          exact Nat.lt_succ_self _
        have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
          rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
        have owned := (frames.extend mapping.allocate_extends (fun _ _ scope => scope)).addOwned
          source.nextIdentity freshBound 0
        simp only [Nat.add_zero, freshImage] at owned
        have stored := homes.storeLocal (.bytes (.aggregate size) ⟨source.nextIdentity, 0⟩)
          (.scalar (.aggregate (List.replicate size 0))) freshBound (by trivial)
        simp only [AllocationRenaming.localSlot, AllocationRenaming.value,
          AllocationRenaming.reference, freshImage] at stored
        refine ⟨mapping.allocate, mapping.allocate_extends, ?_⟩
        simp only [targetChecked, sourceMade, targetMade, Bind.bind, Except.bind]
        apply stored.bind
        intro sourceResult targetResult results
        rcases sourceResult with ⟨sourceSlot, sourceStored⟩
        rcases targetResult with ⟨targetSlot, targetStored⟩
        have memories := results.2
        have operandsSame := mapping.allocate_extends.values operands operandBounds
        have restSame := mapping.allocate_extends.values (stack.drop argc) (by
          intro value member
          exact bounds value (List.mem_of_mem_drop member))
        rw [← operandsSame, ← restSame]
        simpa only [List.map_cons, AllocationRenaming.value,
          AllocationRenaming.managedReference, AllocationRenaming.reference, freshImage,
          Pure.pure, Except.pure] using
          ResultRenamed.ok (FrameAction.Renamed.construct (callee := callee)
            (arguments := .reference (.address ⟨source.nextIdentity, 0⟩) :: operands)
            (rest := stack.drop argc) (temporary := ⟨source.nextIdentity, 0⟩)
            (kind := .aggregate size) memories owned freshBound)
#print axioms Memory.Renamed.stepNewAggregate

end CIL.Safety
