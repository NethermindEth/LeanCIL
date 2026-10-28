import CIL.Safety.CheckedValueRenaming
import CIL.Safety.ViewPositionRenaming
import CIL.Safety.ValueMemoryRenaming
import CIL.Safety.ReferenceRenaming
import CIL.Safety.CheckedReferenceBounds

/-!
# Memory instruction simulation

Successful memory instructions transport their checked effects and evaluation stacks across
an allocation renaming. Local-home insertion does not change scalar computation or access checks.
-/

namespace CIL.Safety

/-- An observable checked outcome is successful or raises a named CLR exception. -/
def SuccessOrThrow : ExecutionResult α → Prop
  | .ok _ => True
  | .error (.thrown _) => True
  | .error _ => False

/-- A successful or throwing sequence cannot start with an unobservable failure. -/
theorem SuccessOrThrow.bind_left {first : ExecutionResult α}
    {next : α → ExecutionResult β} (observable : SuccessOrThrow (first >>= next)) :
    SuccessOrThrow first := by
  cases first with
  | ok value => trivial
  | error fault => cases fault <;> exact observable
#print axioms SuccessOrThrow.bind_left

/-- A memory instruction's successful effect is preserved on the corresponding allocations. -/
theorem Memory.Renamed.memoryInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (operation : CIL.MemoryOp)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (memoryInstruction operation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (memoryInstruction operation stack source)
      (memoryInstruction operation (stack.map mapping.value) target) := by
  unfold CIL.Safety.memoryInstruction at observable ⊢
  rw [mapping.unspecifiedOperands]
  split at observable
  · cases observable
  · simp only [Bool.false_eq_true, ite_false, *]
    split at observable
    all_goals try simp only [List.map_cons, AllocationRenaming.value]
    all_goals try dsimp +instances only [AllocationRenaming.arrayView, AllocationRenaming.spanView]
    all_goals try solve | repeat first | contradiction | cases observable | split at observable
    all_goals clear observable
    all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
    all_goals repeat' rcases bounds with ⟨_, bounds⟩
    all_goals have imageEquality : ∀ left right, left < mapping.sourceLimit →
        right < mapping.sourceLimit → (mapping.image left = mapping.image right ↔ left = right) :=
      fun left right leftBound rightBound =>
        ⟨mapping.injective left right leftBound rightBound, congrArg mapping.image⟩
    all_goals repeat first
      | exact .ok ⟨related, rfl⟩
      | exact .error _
      | (apply (related.referenceDifference _ _ (by assumption) (by assumption)).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
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
      | (apply ((related.spanSlice _ (by assumption) _ _).checkedAt _ _).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply ((related.spanElement _ (by assumption) _).checkedAt _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (mapping.referenceAt _).bindWithSuccess
         intro first second sourceStep same
         have addressBound := referenceAt_below (by assumption) sourceStep
         subst second)
      | (apply (related.checkedAdd _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply (related.checkedRead _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.checkedAccess _ (by assumption) _ _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.checkedWrite _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep memoryRelated
         exact .ok ⟨memoryRelated, rfl⟩)
      | (apply (related.checkedSpan _ (by assumption) _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.checkedArray _ (by assumption) _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.arrayElement _ (by assumption) _ _).bindWithSuccess
         intro first second sourceStep same
         have addressBound : first.allocation < mapping.sourceLimit := by
           rw [related.sourceLimit]
           exact (checkedArrayElement_valid _ _ _ _ _ sourceStep).below formed
         subst second)
      | dsimp +instances only [AllocationRenaming.reference]
      | simp only [mapping.isNull, imageEquality]
      | (split <;> try simp only [*, mapping.isNull, AllocationRenaming.managedReference,
          Bind.bind, Except.bind])

#print axioms Memory.Renamed.memoryInstructionResult

end CIL.Safety
