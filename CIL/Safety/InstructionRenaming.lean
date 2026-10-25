import CIL.Safety.MemoryInstructionRenaming

/-!
# Ordinary instruction simulation under allocation renaming

Typed fields, aggregates, lanes and stack operations preserve successful values and named
exceptions while accessing corresponding allocation identities.
-/

namespace CIL.Safety

/-- Instruction families keep the checked simulation proofs independently small. -/
private inductive InstructionFamily where
  | storage | fields | other

/-- Storage and field operations require distinct checked intermediate addresses. -/
private def instructionFamily : CIL.Op → InstructionFamily
  | .loadAggregate _ | .copyObject _ | .storeAggregate _ | .initAggregate _
  | .loadScalar .. | .storeScalar _ => .storage
  | .fieldAt .. | .fieldAddress _ | .setFieldAt .. | .aggregateFieldAt ..
  | .setAggregateFieldAt .. => .fields
  | _ => .other

set_option hygiene false in
/-- Composes checked primitive correspondences within one ordinary instruction family. -/
local macro "instruction_renaming" : tactic => `(tactic| (
  unfold CIL.Safety.instruction at observable ⊢
  rw [mapping.unspecifiedOperands]
  split at observable
  · cases observable
  · simp only [Bool.false_eq_true, ite_false, *]
    split at observable
    all_goals try solve | cases family
    all_goals try simp only [List.map_cons, AllocationRenaming.value]
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
      | (apply (related.checkedRead _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.checkedAccess _ (by assumption) _ _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.checkedWrite _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep memoryRelated
         exact .ok ⟨memoryRelated, rfl⟩)
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
      | (split <;> try simp only [*, mapping.isNull, AllocationRenaming.managedReference,
          Bind.bind, Except.bind])
))

/-- storage instructions preserve mapped successful values and named exceptions. -/
private theorem instruction_storage {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (operation : CIL.Op)
    (family : instructionFamily operation = .storage)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (instruction operation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (instruction operation stack source)
      (instruction operation (stack.map mapping.value) target) := by
  instruction_renaming
#print axioms instruction_storage

/-- fields instructions preserve mapped successful values and named exceptions. -/
private theorem instruction_fields {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (operation : CIL.Op)
    (family : instructionFamily operation = .fields)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (instruction operation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (instruction operation stack source)
      (instruction operation (stack.map mapping.value) target) := by
  instruction_renaming
#print axioms instruction_fields

/-- other instructions preserve mapped successful values and named exceptions. -/
private theorem instruction_other {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (operation : CIL.Op)
    (family : instructionFamily operation = .other)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (instruction operation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (instruction operation stack source)
      (instruction operation (stack.map mapping.value) target) := by
  instruction_renaming
#print axioms instruction_other

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
  cases family : instructionFamily operation with
  | storage => exact instruction_storage related operation family formed stack bounds observable
  | fields => exact instruction_fields related operation family formed stack bounds observable
  | other => exact instruction_other related operation family formed stack bounds observable
#print axioms Memory.Renamed.instructionResult

end CIL.Safety
