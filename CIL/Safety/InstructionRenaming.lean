import CIL.Safety.MemoryInstructionRenaming

/-!
# Ordinary instruction simulation under allocation renaming

Typed fields, aggregates, lanes and stack operations preserve successful values and named
exceptions while accessing corresponding allocation identities.
Primitive matching tries writes before reads to avoid reducing a write while rejecting a read lemma.
-/

namespace CIL.Safety

set_option maxHeartbeats 600000 in
/-- Ordinary instructions preserve mapped successful values and named CLR exceptions. -/
theorem Memory.Renamed.instructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (operation : CIL.Op)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (instruction operation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (instruction operation stack source)
      (instruction operation (stack.map mapping.value) target) := by
  unfold CIL.Safety.instruction at observable ⊢
  rw [mapping.unspecifiedOperands]
  split at observable
  · cases observable
  · rename_i guard
    rw [ite_eq_right guard, ite_eq_right guard]
    split at observable
    all_goals try simp (config := { singlePass := true }) only
      [List.map_cons, AllocationRenaming.value]
    all_goals try dsimp +instances only [AllocationRenaming.arrayView, AllocationRenaming.spanView]
    all_goals try exact related.memoryInstructionResult _ formed _ bounds observable
    all_goals try solve | repeat first | contradiction | cases observable | split at observable
    all_goals clear observable
    all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below,
      ManagedReference.Below] at bounds
    all_goals repeat' rcases bounds with ⟨_, bounds⟩
    all_goals have imageEquality : ∀ left right, left < mapping.sourceLimit →
        right < mapping.sourceLimit → (mapping.image left = mapping.image right ↔ left = right) :=
      fun left right leftBound rightBound =>
        ⟨mapping.injective left right leftBound rightBound, congrArg mapping.image⟩
    all_goals try simp only [related.dereference _ (by assumption)]
    all_goals repeat first
      | exact .ok ⟨related, rfl⟩
      | exact .error _
      | (apply (related.formValue _ (by assumption)).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply (related.storeValue _ (by assumption) _).bindWithSuccess
         intro first second sourceStep memoryRelated
         exact .ok ⟨memoryRelated, rfl⟩)
      | (apply (related.loadValue _ (by assumption) _ _).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply (mapping.bitcastValue _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply (mapping.referenceAt _).bindWithSuccess
         intro first second sourceStep same
         have addressBound := referenceAt_below (by assumption) sourceStep
         subst second)
      | (apply (related.checkedAdd _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         have addressBound : first.allocation < mapping.sourceLimit := by
           rw [related.sourceLimit]
           exact formed.form_below (checked_add_result_valid _ _ _ _ _ _ _ sourceStep)
         subst second)
      | (apply (related.checkedWrite _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep memoryRelated
         exact .ok ⟨memoryRelated, rfl⟩)
      | (apply (related.checkedRead _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.checkedAccess _ (by assumption) _ _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.loadSnapshot _ (by assumption) _).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply (related.checkedWriteSnapshot _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep memoryRelated
         exact .ok ⟨memoryRelated, rfl⟩)
      | (apply (related.checkedDereference _ (by assumption) _ _).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply ((ResultEquivalent.eq_refl _).checkedAt _ _).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | dsimp +instances only [AllocationRenaming.reference]
      | simp only [mapping.isNull, imageEquality]
      | (split <;> try simp only [*, AllocationRenaming.managedReference,
          Bind.bind, Except.bind])
#print axioms Memory.Renamed.instructionResult

end CIL.Safety
