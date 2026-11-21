import CIL.Safety.MemoryInstructionRenaming
import CIL.Safety.NativeMethodTableRenaming

/-!
# Ordinary instruction simulation under allocation renaming

Typed fields, aggregates, lanes, native table loads and stack operations preserve successful
values and named exceptions while accessing corresponding allocation identities.
Primitive matching tries writes before reads to avoid reducing a write while rejecting a read lemma.
-/

namespace CIL.Safety

-- Stack lists are renamed by the local map of the frame that holds them.
variable {indices : LocalIndexMap}

/-- Observable execution through a native table requires a successful checked memory step. -/
theorem checkedNative_bind {mapping : AllocationRenaming} {relation : β → γ → Prop}
    (source target : Checked α) (sourceNext : α → ExecutionResult β)
    (targetNext : α → ExecutionResult γ)
    (preserved : ∀ value, source = .ok value → target = .ok value)
    (observable : SuccessOrThrow (checkedAt .null nativeMethodWidth source >>= sourceNext))
    (next : ∀ value, source = .ok value → SuccessOrThrow (sourceNext value) →
      ResultRenamed mapping relation (sourceNext value) (targetNext value)) :
    ResultRenamed mapping relation (checkedAt .null nativeMethodWidth source >>= sourceNext)
      (checkedAt .null nativeMethodWidth target >>= targetNext) := by
  cases checked : source with
  | error fault =>
    simp [checked, checkedAt, Except.mapError, Bind.bind, Except.bind, SuccessOrThrow]
      at observable
  | ok value =>
    simp only [checked, checkedAt, Except.mapError, Bind.bind, Except.bind] at observable ⊢
    rw [preserved value checked]
    exact next value checked observable
#print axioms checkedNative_bind

/-- A method table's length reads no memory, so renaming leaves it and its faults unchanged. -/
theorem methodTableLength_renamed (mapping : AllocationRenaming)
    (table : CIL.MethodTable) :
    ResultRenamed mapping Eq (methodTableLength table) (methodTableLength table) := by
  unfold methodTableLength
  cases table.targets with
  | none => exact .error _
  | some targets =>
    by_cases large : targets.size ≥ 2 ^ 31
    · simp only [large, ite_true, Bind.bind, Except.bind]; exact .error _
    · simp only [large, ite_false, Bind.bind, Except.bind, Pure.pure, Except.pure]; exact .ok rfl
#print axioms methodTableLength_renamed

/-- An observable method table element read selects the same pointer in renamed memory: a
    native backing resolves its stable binding to the renamed allocation. -/
theorem Memory.Renamed.methodTableElement_bind {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {relation : β → γ → Prop}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (table : CIL.MethodTable) (index : CIL.Value)
    (sourceNext : CIL.MethodPointer → ExecutionResult β)
    (targetNext : CIL.MethodPointer → ExecutionResult γ)
    (observable : SuccessOrThrow (methodTableElement table index source >>= sourceNext))
    (next : ∀ pointer, SuccessOrThrow (sourceNext pointer) →
      ResultRenamed mapping relation (sourceNext pointer) (targetNext pointer)) :
    ResultRenamed mapping relation (methodTableElement table index source >>= sourceNext)
      (methodTableElement table index target >>= targetNext) := by
  unfold methodTableElement at observable ⊢
  obtain ⟨signature, targets, backing, entryCount, counted⟩ := table
  cases selected : arrayIndex index with
  | none => simp only [Bind.bind, Except.bind]; exact .error _
  | some position =>
    simp only [selected] at observable ⊢
    cases targets with
    | none => exact .error _
    | some targets =>
      by_cases large : targets.size ≥ 2 ^ 31
      · simp only [large, ite_true, Bind.bind, Except.bind]; exact .error _
      · simp only [large, ite_false, Bind.bind, Except.bind, Pure.pure, Except.pure]
          at observable ⊢
        cases found : targets[position]? with
        | none => simp only; exact .error _
        | some entry =>
          simp only [found] at observable ⊢
          cases backing with
          | none => simp only at observable ⊢; exact next _ observable
          | some backing =>
            simp only at observable ⊢
            exact checkedNative_bind _ _ _ _
              (fun value proof => related.loadNativeTable_success formed _ value proof) observable
              (fun value _ observed => next value observed)
#print axioms Memory.Renamed.methodTableElement_bind

set_option hygiene false in
/-- Closes the renaming of one arm of an element access once its stack is split: each checked
    read, write and table lookup touches the mapped element and relates the memories. -/
local macro "element_result" : tactic => `(tactic| (
    all_goals try simp only [List.map_cons, AllocationRenaming.value, LocalIndexMap.value,
      AllocationRenaming.arrayView, arrayLoad, arrayStore] at observable ⊢
    all_goals try dsimp +instances only [AllocationRenaming.arrayView]
    all_goals try solve | repeat first | contradiction | cases observable | split at observable
    all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below,
      ManagedReference.Below] at bounds
    all_goals repeat' rcases bounds with ⟨_, bounds⟩
    all_goals have imageEquality : ∀ left right, left < mapping.sourceLimit →
        right < mapping.sourceLimit → (mapping.image left = mapping.image right ↔ left = right) :=
      fun left right leftBound rightBound =>
        ⟨mapping.injective left right leftBound rightBound, congrArg mapping.image⟩
    all_goals repeat first
      | exact .ok ⟨related, rfl⟩
      | exact .error _
      | (apply (methodTableLength_renamed mapping _).bind
         intro first second same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply related.methodTableElement_bind formed _ _ _ _ observable
         intro pointer observable
         exact .ok ⟨related, rfl⟩)
      | (apply (related.loadSlot formed _ (by assumption)).bindWithSuccess
         intro first second sourceStep same
         subst second
         push_renamed related)
      | (apply (related.referenceArrayOf _ (by assumption)).bind
         intro first second same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply (related.referenceArraySlot _ (by assumption) _).bindWithSuccess
         intro first second sourceStep same
         have slotBound := referenceArraySlot_below (by assumption) sourceStep
         subst second)
      | (apply (related.storableIn _ _ (by assumption)).bind
         intro first second same
         subst second)
      | (apply (related.storeSlot _ (by assumption) _ (by assumption)).bind
         intro first second memoryRelated
         exact .ok ⟨memoryRelated, rfl⟩)
      | (apply (related.loadValue _ (by assumption) _ _).bindWithSuccess
         intro first second sourceStep same
         subst second
         exact .ok ⟨related, rfl⟩)
      | (apply (related.checkedWrite _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep memoryRelated
         exact .ok ⟨memoryRelated, rfl⟩)
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
          Bind.bind, Except.bind])))

/-- Array lengths, element loads and stores, and handler table reads touch the mapped element
    and relate their memories. -/
theorem Memory.Renamed.elementInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (op : CIL.Instruction)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (elementInstruction op stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (elementInstruction op stack source)
      (elementInstruction op (stack.map (indices.value mapping)) target) := by
  unfold elementInstruction at observable ⊢
  split at observable
  -- Every arm names its stack constructors, so the renamed stack reduces to the same arm.
  element_result
#print axioms Memory.Renamed.elementInstructionResult

/-- A typed element access touches the mapped element by its shape and relates the memories. -/
theorem Memory.Renamed.typedElementInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (shape : CIL.ElementShape)
    (store : Bool) (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (typedElementInstruction shape store stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (typedElementInstruction shape store stack source)
      (typedElementInstruction shape store (stack.map (indices.value mapping)) target) := by
  cases shape with
  | value element =>
    simp only [typedElementInstruction] at observable ⊢
    by_cases composite : element.composite = true
    · simp only [composite, ite_true] at observable ⊢
      exact related.arrayTransferInstructionResult formed element store stack bounds observable
    · simp only [composite, Bool.false_eq_true, ite_false] at observable ⊢
      cases store
      all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at observable ⊢
      · unfold arrayLoad at observable ⊢
        split at observable
        element_result
      · unfold arrayStore at observable ⊢
        split at observable
        element_result
  | method signature =>
    cases store
    all_goals unfold typedElementInstruction at observable ⊢
    all_goals split at observable
    all_goals try simp only [CIL.ElementShape.method.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [List.map_cons, LocalIndexMap.value]
    -- The table's signature test reads no allocation, so both sides take the same branch.
    all_goals try (split at observable <;>
      simp only [*, ite_true, ite_false, Bool.false_eq_true, Bind.bind, Except.bind])
    all_goals element_result
  | reference element => cases store <;> exact .error _
  | unsupported reason => cases store <;> exact .error _
#print axioms Memory.Renamed.typedElementInstructionResult

/-- An element address is the address of the mapped element and relates the memories. -/
theorem Memory.Renamed.elementAddressInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (shape : CIL.ElementShape)
    (readOnly : Bool) (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (elementAddressInstruction shape readOnly stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (elementAddressInstruction shape readOnly stack source)
      (elementAddressInstruction shape readOnly (stack.map (indices.value mapping)) target) := by
  cases shape with
  | value element =>
    simp only [elementAddressInstruction] at observable ⊢
    unfold arrayAddress at observable ⊢
    split at observable
    element_result
  | method signature => exact .error _
  | reference element => exact .error _
  | unsupported reason => exact .error _
#print axioms Memory.Renamed.elementAddressInstructionResult

set_option hygiene false in
/-- Moves checked memory accesses in a matched stack arm through the allocation map. -/
local macro "rename_memory_arm" : tactic => `(tactic| (
    all_goals try simp (config := { singlePass := true }) only
      [List.map_cons, AllocationRenaming.value, LocalIndexMap.value]
    all_goals try dsimp +instances only [AllocationRenaming.arrayView, AllocationRenaming.spanView]
    all_goals try exact related.memoryInstructionResult _ formed _ bounds observable
    all_goals try exact related.elementInstructionResult _ formed _ bounds observable
    all_goals try solve
      | (apply checkedNative_bind _ _ _ _
          (fun value proof => related.loadNativeTable_success formed _ value proof) observable
         intro value found observable
         exact .ok ⟨related, rfl⟩)
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
      | simp only [related.read _ (by assumption)]
      | dsimp +instances only [AllocationRenaming.reference]
      | simp only [mapping.isNull, imageEquality]
      | (split <;> try simp only [*, AllocationRenaming.managedReference,
          Bind.bind, Except.bind])))

/-- Forming a field address at a checked offset respects allocation renaming. -/
theorem Memory.Renamed.structFieldAddressResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (offset : Nat) (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (structFieldAddress offset stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (structFieldAddress offset stack source)
      (structFieldAddress offset (stack.map (indices.value mapping)) target) := by
  unfold structFieldAddress at observable ⊢
  rw [indices.unspecifiedOperands mapping]
  split at observable
  · cases observable
  · rename_i guard
    rw [ite_eq_right guard, ite_eq_right guard]
    split at observable
    rename_memory_arm
#print axioms Memory.Renamed.structFieldAddressResult

/-- Reading from a checked value field respects allocation renaming. -/
theorem Memory.Renamed.loadValueFieldResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (offset width : Nat) (signed : Bool) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (loadValueField offset width signed stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (loadValueField offset width signed stack source)
      (loadValueField offset width signed (stack.map (indices.value mapping)) target) := by
  unfold loadValueField at observable ⊢
  rw [indices.unspecifiedOperands mapping]
  split at observable
  · cases observable
  · rename_i guard
    rw [ite_eq_right guard, ite_eq_right guard]
    split at observable
    rename_memory_arm
#print axioms Memory.Renamed.loadValueFieldResult

/-- Writing to a checked value field respects allocation renaming. -/
theorem Memory.Renamed.storeValueFieldResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (offset width : Nat) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (storeValueField offset width stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (storeValueField offset width stack source)
      (storeValueField offset width (stack.map (indices.value mapping)) target) := by
  unfold storeValueField at observable ⊢
  rw [indices.unspecifiedOperands mapping]
  split at observable
  · cases observable
  · rename_i guard
    rw [ite_eq_right guard, ite_eq_right guard]
    split at observable
    rename_memory_arm
#print axioms Memory.Renamed.storeValueFieldResult

/-- Reading a nested struct retains its byte contents under an allocation renaming. -/
theorem Memory.Renamed.loadAggregateFieldResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (offset size : Nat) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (loadAggregateField offset size stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (loadAggregateField offset size stack source)
      (loadAggregateField offset size (stack.map (indices.value mapping)) target) := by
  unfold loadAggregateField at observable ⊢
  rw [indices.unspecifiedOperands mapping]
  split at observable
  · cases observable
  · rename_i guard
    rw [ite_eq_right guard, ite_eq_right guard]
    split at observable
    rename_memory_arm
#print axioms Memory.Renamed.loadAggregateFieldResult

/-- Writing a nested struct preserves the allocation correspondence of the resulting memories. -/
theorem Memory.Renamed.storeAggregateFieldResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (offset size : Nat) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (storeAggregateField offset size stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (storeAggregateField offset size stack source)
      (storeAggregateField offset size (stack.map (indices.value mapping)) target) := by
  unfold storeAggregateField at observable ⊢
  rw [indices.unspecifiedOperands mapping]
  split at observable
  · cases observable
  · rename_i guard
    rw [ite_eq_right guard, ite_eq_right guard]
    split at observable
    rename_memory_arm
#print axioms Memory.Renamed.storeAggregateFieldResult

/-- A typed transfer maps the references in its operands and preserves initialized and snapshot bytes. -/
theorem Memory.Renamed.transferValuesResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (kind : CIL.TransferKind) (store : Bool)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (transferValues kind store stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (transferValues kind store stack source)
      (transferValues kind store (stack.map (indices.value mapping)) target) := by
  unfold transferValues at observable ⊢
  split at observable
  rename_memory_arm
#print axioms Memory.Renamed.transferValuesResult

/-- Renaming preserves the observation guard and the result of a typed transfer. -/
theorem Memory.Renamed.observedTransferResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (kind : CIL.TransferKind) (store : Bool)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (observedTransfer kind store stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (observedTransfer kind store stack source)
      (observedTransfer kind store (stack.map (indices.value mapping)) target) := by
  by_cases seen : unspecifiedOperands (if store then 2 else 1) stack = true
  · simp only [observedTransfer, seen, ite_true] at observable
    cases observable
  · simp only [observedTransfer, indices.unspecifiedOperands mapping, seen, ite_false] at observable ⊢
    exact related.transferValuesResult kind store formed stack bounds observable
#print axioms Memory.Renamed.observedTransferResult

set_option maxHeartbeats 600000 in
/-- Ordinary instructions preserve mapped successful values and named CLR exceptions. -/
theorem Memory.Renamed.instructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (operation : CIL.Instruction)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (instruction operation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (instruction operation stack source)
      (instruction operation (stack.map (indices.value mapping)) target) := by
  unfold CIL.Safety.instruction at observable ⊢
  rw [indices.unspecifiedOperands mapping]
  split at observable
  · cases observable
  · rename_i guard
    rw [ite_eq_right guard, ite_eq_right guard]
    split at observable
    all_goals try exact related.transferValuesResult _ _ formed _ bounds observable
    rename_memory_arm
#print axioms Memory.Renamed.instructionResult


/-- Typed copying preserves the allocation map on every observable result. -/
theorem Memory.Renamed.copyInitializedBytesResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (size : Nat)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (copyInitializedBytes size stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (copyInitializedBytes size stack source)
      (copyInitializedBytes size (stack.map (indices.value mapping)) target) := by
  unfold copyInitializedBytes at observable ⊢
  split at observable
  rename_memory_arm
#print axioms Memory.Renamed.copyInitializedBytesResult

/-- Zero initialization preserves the allocation map on every observable result. -/
theorem Memory.Renamed.initializeBytesResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (size : Nat)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (initializeBytes size stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (initializeBytes size stack source)
      (initializeBytes size (stack.map (indices.value mapping)) target) := by
  unfold initializeBytes at observable ⊢
  split at observable
  rename_memory_arm
#print axioms Memory.Renamed.initializeBytesResult

/-- An object transfer preserves the allocation map on every observable result. -/
theorem Memory.Renamed.transferObjectResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (shape : CIL.ValueShape) (store : Bool)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (transferObject shape store stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map (indices.value mapping))
      (transferObject shape store stack source)
      (transferObject shape store (stack.map (indices.value mapping)) target) := by
  unfold transferObject at observable ⊢
  split at observable
  all_goals first
    | exact related.observedTransferResult _ _ formed _ bounds observable
    | exact related.memoryInstructionResult _ formed _ bounds observable
    | exact .ok ⟨related, rfl⟩
    | cases observable
    | (split at observable
       all_goals first
         | exact .ok ⟨related, rfl⟩
         | cases observable)
#print axioms Memory.Renamed.transferObjectResult

end CIL.Safety
