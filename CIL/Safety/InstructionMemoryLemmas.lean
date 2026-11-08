import CIL.Safety.Execution
import CIL.Safety.SpanViewLemmas
import CIL.Safety.ArrayViewLemmas

/-!
# Instruction effects and value validity

Facts about the checked interpreter's straight-line instructions. `Value.Valid` says a value
may sit on the stack: a numeric scalar, or a reference that still forms in memory. Every
successful instruction has an `InstructionContract`: its only memory change is one checked
write (an `InstructionEffect`), and it maps valid inputs to valid outputs. Well-formedness
and allocation extension across instructions follow from these.
-/

namespace CIL.Safety

/-- Empty spans retain their element width and capability without reading or changing memory. -/
theorem memoryInstruction_emptySpan (memory : Memory) (stack : List Value)
    (width : Nat) (writable : Bool) (bounded : 0 < width ∧ width < 2^64) :
    memoryInstruction (.spanEmpty width writable) stack memory =
      .ok (memory, .bufferSpan ⟨.null, 0, width, writable⟩ :: stack) := by
  simp [memoryInstruction, otherMemoryInstruction, unspecifiedOperands,
    CIL.MemoryOp.argumentCount, SpanView.validate, bounded, checkedAt]
  rfl
#print axioms memoryInstruction_emptySpan

theorem instructions_append (first second : List CIL.Op) (stack : List Value) (m : Memory) :
    instructions (first ++ second) stack m =
      (instructions first stack m).bind
        (fun (memory, values) => instructions second values memory) := by
  induction first generalizing stack m with
  | nil => rfl
  | cons op first ih =>
    simp only [List.cons_append, instructions]
    cases hi : instruction op stack m with
    | error fault => rfl
    | ok result =>
      rcases result with ⟨memory, values⟩
      exact ih values memory

/-- A fault in a prefix of straight-line code is the fault of the whole sequence. -/
theorem instruction_fault_cannot_be_erased (first second : List CIL.Op) (stack : List Value)
    (m : Memory) (fault : ExecutionFault) (h : instructions first stack m = .error fault) :
    instructions (first ++ second) stack m = .error fault := by
  rw [instructions_append, h]
  rfl

theorem successful_instruction_prefix (first second : List CIL.Op) (stack : List Value)
    (m final : Memory) (values : List Value)
    (h : instructions (first ++ second) stack m = .ok (final, values)) :
    ∃ intermediate stack', instructions first stack m = .ok (intermediate, stack') := by
  rw [instructions_append] at h
  cases hi : instructions first stack m with
  | error fault => simp [hi, Except.bind] at h
  | ok result =>
    rcases result with ⟨memory, stack'⟩
    exact ⟨memory, stack', rfl⟩

/-- Reference validity is independent of readable initialization and access
    width. A span's accessible bytes are checked by the memory operation. -/
def Value.Valid (m : Memory) : Value → Prop
  | .methodPointer _ | .methodTable _ | .object .null => True
  | .object (.address r) => formObject m (.address r) = .ok (.object (.address r))
  | .scalar value => numericValue value = true
  | .bufferSpan view => view.validate m = .ok ()
  | .array view => view.validate m = .ok ()
  | .readOnlyReference .null => True
  | .readOnlyReference (.address r) => form m r = .ok r
  | .reference .null | .span .null _ => True
  | .reference (.address r) | .span (.address r) _ => form m r = .ok r

/-- Every value in the list is valid in `m`. -/
def ValuesValid (m : Memory) (values : List Value) : Prop :=
  ∀ value ∈ values, value.Valid m

theorem ValuesValid.append {m : Memory} {left right : List Value}
    (hl : ValuesValid m left) (hr : ValuesValid m right) : ValuesValid m (left ++ right) := by
  intro value member
  rcases List.mem_append.mp member with member | member
  · exact hl _ member
  · exact hr _ member

theorem ValuesValid.head {m : Memory} {value : Value} {values : List Value}
    (valid : ValuesValid m (value :: values)) : value.Valid m := valid _ (by simp)

theorem ValuesValid.tail {m : Memory} {value : Value} {values : List Value}
    (valid : ValuesValid m (value :: values)) : ValuesValid m values :=
  fun _ member => valid _ (List.mem_cons_of_mem _ member)

theorem ValuesValid.cons {m : Memory} {value : Value} {values : List Value}
    (head : value.Valid m) (tail : ValuesValid m values) : ValuesValid m (value :: values) := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail _ member

theorem form_returns_input (m : Memory) (r result : Reference) (h : form m r = .ok result) :
    result = r := by
  unfold form at h
  cases hl : liveAllocation m r.allocation <;>
    simp only [hl, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · split at h
    · exact Except.ok.inj h |>.symm
    · cases h

theorem formValue_returns_input (m : Memory) (r : ManagedReference) (value : Value)
    (h : formValue m r = .ok value) : value = .reference r := by
  cases r with
  | null => cases h; rfl
  | address r =>
    simp only [formValue] at h
    cases hf : form m r <;>
      simp only [hf, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
        Except.pure] at h
    · cases h
    · rename_i formed
      have same := form_returns_input _ _ _ hf
      cases h
      rw [same]

/-- A formed object reference is returned unchanged. -/
theorem formObject_returns_input {m : Memory} {reference : ManagedReference} {value : Value}
    (formed : formObject m reference = .ok value) : value = .object reference := by
  cases reference with
  | null => cases formed; rfl
  | address r =>
    simp only [formObject, checkedAt, Except.mapError, Bind.bind, Except.bind] at formed
    split at formed
    · cases formed
    · split at formed
      · split at formed
        · cases formed; rfl
        · cases formed
      · cases formed

/-- A formed object reference is a valid stack value. -/
theorem formObject_result_valid {m : Memory} {reference : ManagedReference} {value : Value}
    (formed : formObject m reference = .ok value) : value.Valid m := by
  have same := formObject_returns_input formed
  subst value
  cases reference with
  | null => exact True.intro
  | address r => exact formed

/-- A type test leaves a valid object reference: its formed operand, or null. -/
theorem objectTest_valid {m : Memory} {type : CIL.Extraction.TypeExpr} {throwing : Bool}
    {reference result : ManagedReference}
    (tested : objectTest m type throwing reference = .ok result) :
    (Value.object result).Valid m := by
  unfold objectTest at tested
  cases formed : formObject m reference with
  | error fault => simp [formed, Bind.bind, Except.bind] at tested
  | ok value =>
    simp only [formed, Bind.bind, Except.bind] at tested
    cases reference with
    | null => cases tested; exact True.intro
    | address object =>
      simp only at tested
      cases typed : runtimeTypeOf m object with
      | error fault => simp [typed] at tested
      | ok runtime =>
        simp only [typed] at tested
        have valid := formObject_result_valid formed
        rw [formObject_returns_input formed] at valid
        split at tested
        · cases tested; exact valid
        · split at tested
          · cases tested
          · cases tested; exact True.intro
#print axioms objectTest_valid

/-- Object formation needs only the allocation table entry, which extension keeps. -/
theorem formObject_preserved {m result : Memory} {reference : ManagedReference}
    (formed : formObject m reference = .ok (.object reference)) (wellFormed : m.WellFormed)
    (ext : AllocationExtension m result) :
    formObject result reference = .ok (.object reference) := by
  cases reference with
  | null => rfl
  | address r =>
    cases found : m.allocations r.allocation with
    | none =>
      simp [formObject, liveAllocation, found, checkedAt, Except.mapError, Bind.bind,
        Except.bind] at formed
    | some allocation =>
      have kept := ext.lookup r.allocation (wellFormed.allocations _ _ found).1
      rw [found] at kept
      simpa only [formObject, liveAllocation, kept, found] using formed

/-- A formed non-null object reference names an identity already issued. -/
theorem formObject_issued {m : Memory} {reference : Reference} {value : Value}
    (formed : formObject m (.address reference) = .ok value) (wellFormed : m.WellFormed) :
    reference.allocation < m.nextIdentity := by
  cases found : m.allocations reference.allocation with
  | none =>
    simp [formObject, liveAllocation, found, checkedAt, Except.mapError, Bind.bind,
      Except.bind] at formed
  | some allocation => exact (wellFormed.allocations _ _ found).1

/-- A successful slot store checked the slot's write authority and the stored reference, and
    changed only that slot. -/
theorem storeSlot_ok {m result : Memory} {field : Reference} {value : ManagedReference}
    (stored : storeSlot m field value = .ok result) :
    access m field objectFieldSlot ordinaryAccessAlignment true = .ok () ∧
      formObject m value = .ok (.object value) ∧ result = setSlot m field value := by
  unfold storeSlot at stored
  cases accessed : access m field objectFieldSlot ordinaryAccessAlignment true <;>
    simp only [accessed, checkedAt, Except.mapError, Bind.bind, Except.bind] at stored
  · cases stored
  · cases formed : formObject m value with
    | error => simp only [formed] at stored; cases stored
    | ok formedValue =>
      simp only [formed, Pure.pure, Except.pure, Except.ok.injEq] at stored
      have same := formObject_returns_input formed
      subst same
      exact ⟨rfl, rfl, stored.symm⟩

/-- A slot store keeps memory well formed: the stored reference formed, so it was issued. -/
theorem storeSlot_preserves_wellFormed {m result : Memory} {field : Reference}
    {value : ManagedReference} (hm : m.WellFormed)
    (stored : storeSlot m field value = .ok result) : result.WellFormed := by
  obtain ⟨-, formed, rfl⟩ := storeSlot_ok stored
  exact setSlot_preserves_wellFormed hm fun reference held => by
    subst held
    exact formObject_issued formed hm

#print axioms formObject_returns_input
#print axioms formObject_result_valid
#print axioms formObject_preserved
/-- A loaded field reference formed, so it is a valid stack value. -/
theorem loadSlot_valid {m : Memory} {field : Reference} {value : Value}
    (loaded : loadSlot m field = .ok value) : value.Valid m := by
  unfold loadSlot at loaded
  cases accessed : access m field objectFieldSlot ordinaryAccessAlignment false <;>
    simp only [accessed, checkedAt, Except.mapError, Bind.bind, Except.bind] at loaded
  · cases loaded
  · exact formObject_result_valid loaded

#print axioms formObject_issued
#print axioms loadSlot_valid
#print axioms storeSlot_ok
#print axioms storeSlot_preserves_wellFormed

/-- An array whose extent was checked in `memory` is a valid stack value there. -/
theorem checkedArray_valid (view : ArrayView) (memory : Memory) (reference : ManagedReference)
    (width : Nat) (done : Unit)
    (formed : checkedAt reference width (view.validate memory) = .ok done) :
    (Value.array view).Valid memory := by
  cases done
  exact checkedAt_ok formed

/-- The array a value-array field holds was validated before it was pushed. -/
theorem arrayOfSlot_valid {m : Memory} {held : ManagedReference} {element : CIL.ArrayElement}
    {value : Value} (loaded : arrayOfSlot m held element = .ok value) : value.Valid m := by
  unfold arrayOfSlot at loaded
  repeat' first
    | solve | cases loaded; apply checkedArray_valid; assumption
    | cases loaded
    | split at loaded
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at loaded

/-- A loaded value-array field is a valid stack value. -/
theorem loadArraySlot_valid {m : Memory} {field : Reference} {element : CIL.ArrayElement}
    {value : Value} (loaded : loadArraySlot m field element = .ok value) : value.Valid m := by
  unfold loadArraySlot at loaded
  cases accessed : access m field objectFieldSlot ordinaryAccessAlignment false <;>
    simp only [accessed, checkedAt, Except.mapError, Bind.bind, Except.bind] at loaded
  · cases loaded
  · exact arrayOfSlot_valid loaded

/-- A non-null reference kept for an array names an allocation, so its identity was issued. -/
theorem arraySlotValue_issued {m : Memory} {view : ArrayView} {element : CIL.ArrayElement}
    {reference : Reference} (valued : arraySlotValue m view element = .ok (.address reference))
    (wellFormed : m.WellFormed) : reference.allocation < m.nextIdentity := by
  unfold arraySlotValue at valued
  split at valued
  · cases valued
  · rename_i address _
    cases found : m.allocations address.allocation with
    | none =>
      simp [liveAllocation, found, checkedAt, Except.mapError, Bind.bind, Except.bind] at valued
    | some allocation =>
      have issued := (wellFormed.allocations _ _ found).1
      simp only [liveAllocation, found, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at valued
      repeat' first
        | solve | cases valued; exact issued
        | cases valued
        | split at valued

/-- A successful value-array field store checked the slot's write authority and the array, and
    changed only that slot. -/
theorem storeArraySlot_ok {m result : Memory} {field : Reference} {view : ArrayView}
    {element : CIL.ArrayElement} (stored : storeArraySlot m field view element = .ok result) :
    access m field objectFieldSlot ordinaryAccessAlignment true = .ok () ∧
      ∃ held, arraySlotValue m view element = .ok held ∧ result = setSlot m field held := by
  unfold storeArraySlot at stored
  cases accessed : access m field objectFieldSlot ordinaryAccessAlignment true <;>
    simp only [accessed, checkedAt, Except.mapError, Bind.bind, Except.bind] at stored
  · cases stored
  · cases valued : arraySlotValue m view element with
    | error => simp only [valued] at stored; cases stored
    | ok held =>
      simp only [valued, Pure.pure, Except.pure, Except.ok.injEq] at stored
      exact ⟨rfl, held, rfl, stored.symm⟩

/-- A value-array field store keeps memory well formed: the kept reference names an allocation. -/
theorem storeArraySlot_preserves_wellFormed {m result : Memory} {field : Reference}
    {view : ArrayView} {element : CIL.ArrayElement} (hm : m.WellFormed)
    (stored : storeArraySlot m field view element = .ok result) : result.WellFormed := by
  obtain ⟨-, held, valued, rfl⟩ := storeArraySlot_ok stored
  exact setSlot_preserves_wellFormed hm fun reference same => by
    subst same
    exact arraySlotValue_issued valued hm

#print axioms checkedArray_valid
#print axioms arrayOfSlot_valid
#print axioms loadArraySlot_valid
#print axioms arraySlotValue_issued
#print axioms storeArraySlot_ok
#print axioms storeArraySlot_preserves_wellFormed

theorem formValue_result_valid (m : Memory) (r : ManagedReference) (value : Value)
    (h : formValue m r = .ok value) : value.Valid m := by
  have same := formValue_returns_input _ _ _ h
  subst value
  cases r with
  | null => exact True.intro
  | address r =>
    cases hf : form m r <;>
      simp only [formValue, hf, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i formed
      have same := form_returns_input _ _ _ hf
      subst formed
      exact hf

/-- Forming a reference also validates the same address with a readonly restriction. -/
theorem formValue_readOnly_valid (m : Memory) (reference : ManagedReference) (value : Value)
    (formed : formValue m reference = .ok value) :
    (Value.readOnlyReference reference).Valid m := by
  have valid := formValue_result_valid m reference value formed
  rw [formValue_returns_input m reference value formed] at valid
  cases reference <;> exact valid

#print axioms formValue_readOnly_valid

/-- `checkedValue` either faults or returns its input, which is then valid. -/
theorem checkedValue_valid (m : Memory) (value result : Value)
    (h : checkedValue m value = .ok result) : result = value ∧ result.Valid m := by
  cases value with
  | methodPointer _ | methodTable _ => cases h; exact ⟨rfl, trivial⟩
  | object r =>
    exact ⟨formObject_returns_input h, formObject_result_valid h⟩
  | scalar value =>
    simp only [checkedValue] at h
    split at h
    · rename_i numeric
      cases h
      exact ⟨rfl, numeric⟩
    · cases h
  | reference r =>
    exact ⟨formValue_returns_input _ _ _ h, formValue_result_valid _ _ _ h⟩
  | bufferSpan view | array view =>
    cases formed : view.validate m <;>
      simp only [checkedValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i validated
      cases validated
      cases h
      exact ⟨rfl, formed⟩
  | readOnlyReference r =>
    cases formed : formValue m r <;>
      simp only [checkedValue, formed, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    · cases h
    · cases h
      have valid := formValue_result_valid _ _ _ formed
      rw [formValue_returns_input _ _ _ formed] at valid
      cases r <;> exact ⟨rfl, valid⟩
  | span r length =>
    simp only [checkedValue] at h
    cases hf : formValue m r <;>
      simp only [hf, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    · cases h
    · have valid := formValue_result_valid _ _ _ hf
      have same := formValue_returns_input _ _ _ hf
      cases h
      rw [same] at valid
      cases r <;> exact ⟨rfl, valid⟩

theorem checkedValue_of_valid (m : Memory) (value : Value) (valid : value.Valid m) :
    checkedValue m value = .ok value := by
  cases value with
  | methodPointer _ | methodTable _ => rfl
  | object r =>
    cases r with
    | null => rfl
    | address r => exact valid
  | scalar value => simp only [Value.Valid] at valid; simp [checkedValue, valid]
  | bufferSpan view | array view =>
    simp only [Value.Valid] at valid
    simp [checkedValue, valid, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  | readOnlyReference r => cases r <;>
      simp_all [Value.Valid, checkedValue, formValue, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  | reference r => cases r <;>
      simp_all [Value.Valid, checkedValue, formValue, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  | span r length => cases r <;>
      simp_all [Value.Valid, checkedValue, formValue, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Valid values stay valid when memory only gains allocations. -/
theorem ValuesValid.preserve {m result : Memory} {values : List Value}
    (valid : ValuesValid m values) (hm : m.WellFormed) (ext : AllocationExtension m result) :
    ValuesValid result values := by
  intro value member
  have hv := valid value member
  cases value with
  | scalar value | methodPointer _ | methodTable _ => exact hv
  | object r =>
    cases r with
    | null => exact True.intro
    | address r => exact formObject_preserved hv hm ext
  | bufferSpan view => exact view.validate_preserved hv hm ext
  | array view => exact view.validate_preserved hv hm ext
  | readOnlyReference r =>
    cases r with
    | null => exact True.intro
    | address r => exact ext.preserves_reference hm r r hv
  | reference r =>
    cases r with
    | null => exact True.intro
    | address r => exact ext.preserves_reference hm r r hv
  | span r length =>
    cases r with
    | null => exact True.intro
    | address r => exact ext.preserves_reference hm r r hv

theorem checkedValues_valid (m : Memory) (values result : List Value)
    (h : values.mapM (checkedValue m) = .ok result) :
    result = values ∧ ValuesValid m result := by
  induction values generalizing result with
  | nil => cases h; exact ⟨rfl, by simp [ValuesValid]⟩
  | cons value values ih =>
    simp only [List.mapM_cons] at h
    cases hc : checkedValue m value <;> simp only [hc, Bind.bind, Except.bind] at h
    · cases h
    · rename_i checked
      have first := checkedValue_valid _ _ _ hc
      cases hr : values.mapM (checkedValue m) <;> simp only [hr, Pure.pure, Except.pure] at h
      · cases h
      · rename_i rest
        have tail := ih rest hr
        cases h
        refine ⟨by rw [first.1, tail.1], ?_⟩
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact first.2
        · exact tail.2 _ member

#print axioms checkedValue_valid
#print axioms checkedValue_of_valid
#print axioms ValuesValid.preserve
#print axioms checkedValues_valid

/-- Values valid in `memory` pass the argument and result checks unchanged. -/
theorem checkedValues_of_valid {memory : Memory} {values : List Value}
    (valid : ValuesValid memory values) : values.mapM (checkedValue memory) = .ok values := by
  induction values with
  | nil => rfl
  | cons value rest restChecked =>
    have head := checkedValue_of_valid memory value (valid value (List.mem_cons_self ..))
    have tail := restChecked fun other member => valid other (List.mem_cons_of_mem _ member)
    simp only [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms checkedValues_of_valid

theorem loadValue_scalar_valid (m : Memory) (r : ManagedReference) (width : Nat)
    {signed : Bool} (value : CIL.Value) (h : loadValue m r width signed = .ok value) :
    (Value.scalar value).Valid m := by
  unfold loadValue at h
  repeat' first
    | rfl
    | solve | exact loadSnapshot_numeric (by assumption)
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

/-- Typed transfer reads produce numeric or snapshot values, never managed references. -/
theorem loadTransfer_numeric (memory : Memory) (reference : ManagedReference)
    (kind : CIL.TransferKind) (value : CIL.Value)
    (read : loadTransfer memory reference kind = .ok value) : numericValue value = true := by
  cases kind with
  | scalar width signed =>
    simp only [loadTransfer] at read
    split at read
    · exact loadValue_scalar_valid _ _ _ _ read
    · cases read
  | snapshot shape => exact loadSnapshot_numeric read
#print axioms loadTransfer_numeric

theorem add_result_valid (m : Memory) (r result : Reference) (size : Nat) (offset : BitVec 64)
    (h : add m r size offset = .ok result) : form m result = .ok result := by
  unfold add at h
  cases hf : form m r <;> simp only [hf, Bind.bind, Except.bind] at h
  · cases h
  · have same := form_returns_input _ _ _ h
    rw [← same] at h
    exact h

theorem checked_add_result_valid (m : Memory) (r result : Reference) (size : Nat)
    (offset : BitVec 64) (reference : ManagedReference) (width : Nat)
    (h : checkedAt reference width (add m r size offset) = .ok result) :
    form m result = .ok result := by
  cases ha : add m r size offset <;> simp only [ha, checkedAt, Except.mapError] at h
  · cases h
  · cases h
    exact add_result_valid _ _ _ _ _ ha

/-- The only memory changes made by an ordinary instruction. Successful
    primitive operations retain their checks, independently of input invariants. -/
inductive InstructionEffect : Memory → Memory → Prop where
  | unchanged (m) : InstructionEffect m m
  | write {m result r bytes alignment} (h : write m r bytes alignment = .ok result) :
      InstructionEffect m result
  | snapshot {m result r bytes alignment} (h : writeSnapshot m r bytes alignment = .ok result) :
      InstructionEffect m result
  | slot {m result field value} (h : storeSlot m field value = .ok result) :
      InstructionEffect m result
  | arraySlot {m result field view element}
      (h : storeArraySlot m field view element = .ok result) : InstructionEffect m result

theorem InstructionEffect.wellFormed {m result : Memory} (effect : InstructionEffect m result)
    (hm : m.WellFormed) : result.WellFormed := by
  cases effect with
  | unchanged => exact hm
  | write h => exact write_preserves_wellFormed _ _ _ _ _ hm h
  | snapshot h => exact writeSnapshot_preserves_wellFormed _ _ _ _ _ hm h
  | slot h => exact storeSlot_preserves_wellFormed hm h
  | arraySlot h => exact storeArraySlot_preserves_wellFormed hm h

theorem InstructionEffect.allocations {m result : Memory} (effect : InstructionEffect m result) :
    AllocationExtension m result := by
  cases effect with
  | unchanged => exact .refl _
  | write h => exact write_extends_allocations _ _ _ _ _ h
  | snapshot h => exact writeSnapshot_extends_allocations _ _ _ _ _ h
  | slot h =>
    obtain ⟨-, -, rfl⟩ := storeSlot_ok h
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | arraySlot h =>
    obtain ⟨-, -, -, rfl⟩ := storeArraySlot_ok h
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem storeValue_effect (m result : Memory) (reference : ManagedReference) (value : CIL.Value)
    (h : storeValue m reference value = .ok result) : InstructionEffect m result := by
  unfold storeValue at h
  repeat' first
    | solve | exact .write (checkedAt_ok (by assumption))
    | solve | exact .snapshot (checkedAt_ok (by assumption))
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind] at h

/-- A typed transfer changes memory by one checked write. -/
theorem storeTransfer_effect (memory result : Memory) (reference : ManagedReference)
    (kind : CIL.TransferKind) (value : CIL.Value)
    (stored : storeTransfer memory reference kind value = .ok result) :
    InstructionEffect memory result := by
  unfold storeTransfer at stored
  repeat' first
    | solve | exact .write (checkedAt_ok (by assumption))
    | solve | exact .snapshot (checkedAt_ok (by assumption))
    | cases stored
    | split at stored
    | simp only [Bind.bind, Except.bind] at stored
#print axioms storeTransfer_effect

/-- Memory effects and output validity share the same instruction case analysis.
    Validity remains conditional, so effect clients need no input invariant. -/
structure InstructionContract (m result : Memory) (stack values : List Value) : Prop where
  effect : InstructionEffect m result
  values : m.WellFormed → ValuesValid m stack → ValuesValid result values

/-- A span fill either leaves an empty view unchanged or performs one checked write. -/
theorem spanFill_effect (view : SpanView) (memory result : Memory) (element : List (BitVec 8))
    (filled : view.fill memory element = .ok result) : InstructionEffect memory result := by
  unfold SpanView.fill SpanView.fillWith at filled
  repeat' first
    | exact .write filled
    | solve | cases filled; exact .unchanged _
    | cases filled
    | split at filled
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at filled
#print axioms spanFill_effect

/-- Snapshot filling is one checked snapshot write, or leaves an empty view unchanged. -/
theorem spanFillSnapshot_effect (view : SpanView) (memory result : Memory)
    (element : List (BitVec 8 × Bool))
    (filled : view.fillSnapshot memory element = .ok result) : InstructionEffect memory result := by
  unfold SpanView.fillSnapshot SpanView.fillWith at filled
  repeat' first
    | exact .snapshot filled
    | solve | cases filled; exact .unchanged _
    | cases filled
    | split at filled
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at filled
#print axioms spanFillSnapshot_effect

/-- An instruction whose outputs are valid whenever its inputs are valid afterwards meets its
    contract, since its effect keeps the inputs valid. -/
theorem InstructionContract.of_effect {m result : Memory} {stack values : List Value}
    (effect : InstructionEffect m result)
    (preserve : ValuesValid result stack → ValuesValid result values) :
    InstructionContract m result stack values :=
  ⟨effect, fun hm valid => preserve (valid.preserve hm effect.allocations)⟩

/-- Validation establishes the invariant for a span value pushed by a constructor. -/
theorem checkedSpan_valid (view : SpanView) (memory : Memory) (width : Nat) (done : Unit)
    (formed : checkedAt view.reference width (view.validate memory) = .ok done) :
    (Value.bufferSpan view).Valid memory := by
  cases done
  exact checkedAt_ok formed

/-- Removing write permission does not change a span's checked extent. -/
theorem checkedReadOnlySpan_valid (view : SpanView) (memory : Memory) (width : Nat) (done : Unit)
    (formed : checkedAt view.reference width (view.validate memory) = .ok done) :
    (Value.bufferSpan view.asReadOnly).Valid memory := by
  cases done
  change view.validate memory = .ok ()
  exact checkedAt_ok formed

/-- A sliced value carries the extent checked by slicing. -/
theorem checkedSpanSlice_valid (view result : SpanView) (memory : Memory) (start length : Nat)
    (sliced : checkedAt view.reference 0 (view.slice memory start length) = .ok result) :
    (Value.bufferSpan result).Valid memory :=
  view.slice_valid result memory start length (checkedAt_ok sliced)

/-- Both writable and readonly element references are live checked addresses. -/
theorem checkedSpanElement_valid (view : SpanView) (memory : Memory) (width index : Nat)
    (reference : Reference)
    (found : checkedAt view.reference width (view.element memory index) = .ok reference) :
    (if view.writable then Value.reference (.address reference)
      else .readOnlyReference (.address reference)).Valid memory := by
  have valid := view.element_formed memory index reference (checkedAt_ok found)
  split <;> exact valid

#print axioms checkedSpan_valid
#print axioms checkedReadOnlySpan_valid
#print axioms checkedSpanSlice_valid
#print axioms checkedSpanElement_valid

/-- Reordering integer bytes always produces a defined scalar value. -/
theorem endianValue_numeric (width : Nat) (signed bigEndian : Bool) (input output : CIL.Value)
    (ordered : endianValue width signed bigEndian input = .ok output) :
    numericValue output = true := by
  unfold endianValue at ordered
  repeat' first
    | solve | cases ordered; rfl
    | cases ordered
    | split at ordered
    | simp only [Pure.pure, Except.pure] at ordered
#print axioms endianValue_numeric

/-- Checked array addresses retain a live allocation-relative reference. -/
theorem checkedArrayElement_valid (view : ArrayView) (memory : Memory) (index width : Nat)
    (reference : Reference) (found : arrayElement memory view index width = .ok reference) :
    (Value.reference (.address reference)).Valid memory := by
  unfold arrayElement at found
  repeat' first
    | solve | exact view.element_formed memory index reference (checkedAt_ok found)
    | cases found
    | split at found
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at found

#print axioms checkedArrayElement_valid

/-- A readonly array address retains validity without gaining write permission through the view. -/
theorem checkedArrayAddress_valid (view : ArrayView) (memory : Memory) (index width : Nat)
    (writable : Bool)
    (reference : Reference) (found : arrayElement memory view index width = .ok reference) :
    (if writable then Value.reference (.address reference)
      else .readOnlyReference (.address reference)).Valid memory := by
  cases writable <;> exact checkedArrayElement_valid view memory index width reference found

#print axioms checkedArrayAddress_valid

set_option hygiene false in
/-- Closes one success case of the instruction case analysis with `InstructionContract.of_effect`:
    picks the effect from the hypotheses, then rebuilds the output stack from retained inputs
    and validity lemmas for each pushed value. Used only by the instruction contract proofs. -/
macro "instruction_contract_close" : tactic => `(tactic| (
  refine InstructionContract.of_effect ?_ ?_
  · first
    | exact .unchanged _
    | exact .write (checkedAt_ok (by assumption))
    | exact .snapshot (checkedAt_ok (by assumption))
    | exact .slot (by assumption)
    | exact .arraySlot (by assumption)
    | apply storeValue_effect; assumption
    | exact spanFill_effect _ _ _ _ (checkedAt_ok (by assumption))
    | exact spanFillSnapshot_effect _ _ _ _ (checkedAt_ok (by assumption))
    | apply storeTransfer_effect; assumption
  · intro retained
    repeat' first
      | exact retained
      | exact retained.head
      | exact retained.tail
      | exact retained.tail.tail
      | exact retained.tail.tail.tail
      | solve |
          apply ValuesValid.cons
          · first
            | rfl
            | exact True.intro
            | exact bitcastValue_numeric (by assumption)
            | exact loadSnapshot_numeric (by assumption)
            | exact loadTransfer_numeric _ _ _ _ (by assumption)
            | exact endianValue_numeric _ _ _ _ _ (by assumption)
            | exact retained.head
            | apply loadValue_scalar_valid; assumption
            | apply formValue_result_valid; assumption
            | apply formValue_readOnly_valid; assumption
            | apply loadSlot_valid; assumption
            | apply loadArraySlot_valid; assumption
            | split <;> first
                | apply formValue_result_valid; assumption
                | apply formValue_readOnly_valid; assumption
            | apply checked_add_result_valid; assumption
            | apply checkedSpan_valid; assumption
            | apply checkedReadOnlySpan_valid; assumption
            | apply checkedSpanSlice_valid; assumption
            | apply checkedSpanElement_valid; assumption
            | apply checkedArrayElement_valid; assumption
            | apply checkedArrayAddress_valid; assumption
          · first
            | exact retained
            | exact retained.tail
            | exact retained.tail.tail
            | exact retained.tail.tail.tail))

/-- Copying only changes checked destination bytes and returns a scalar flag or no value. -/
theorem spanCopyInstruction_contract (width : Nat) (tryCopy : Bool) (stack values : List Value)
    (memory result : Memory)
    (copied : spanCopyInstruction width tryCopy stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  cases tryCopy <;> unfold spanCopyInstruction at copied
  all_goals simp only [Bool.false_eq_true, Bool.true_eq, ite_true, ite_false,
    writeIndexed_eq, Bind.bind, Except.bind, Pure.pure, Except.pure] at copied
  all_goals repeat' first
    | solve | cases copied; instruction_contract_close
    | cases copied
    | split at copied
#print axioms spanCopyInstruction_contract

/-- Fill and clear preserve the checked write effect and retain only valid stack values. -/
theorem spanFillInstruction_contract (width : Nat) (clear : Bool) (stack values : List Value)
    (memory result : Memory)
    (filled : spanFillInstruction width clear stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold spanFillInstruction at filled
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at filled
  repeat' first
    | solve | cases filled; instruction_contract_close
    | cases filled
    | split at filled
#print axioms spanFillInstruction_contract

/-- Array filling inherits the checked span write and retained-stack contract. -/
theorem arrayFillInstruction_contract (element : CIL.ArrayElement) (counted : Bool)
    (stack values : List Value)
    (memory result : Memory)
    (filled : arrayFillInstruction element counted stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold arrayFillInstruction at filled
  split at filled <;>
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at filled
  all_goals repeat' first
    | cases filled
    | solve
      | have contract := spanFillInstruction_contract _ _ _ _ _ _ filled
        refine ⟨contract.effect, fun formed valid => contract.values formed ?_⟩
        simp only [ValuesValid, List.mem_cons, forall_eq_or_imp, Value.Valid,
          ArrayView.validate] at valid ⊢
        first
        | exact valid
        | exact ⟨valid.2.2.1, checkedSpanSlice_valid _ _ _ _ _ (by assumption), valid.2.2.2.2⟩
    | split at filled
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at filled
#print axioms arrayFillInstruction_contract

/-- A displaced reference is valid with either write capability. -/
theorem displaceReference_valid {memory : Memory} {reference result : ManagedReference}
    {size : Nat} {displacement : Int}
    (success : displaceReference memory reference size displacement = .ok result) :
    (Value.reference result).Valid memory ∧ (Value.readOnlyReference result).Valid memory := by
  simp only [displaceReference, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  repeat' first
    | split at success
    | solve | cases success
    | solve |
        cases success
        constructor <;> apply checked_add_result_valid <;> assumption
#print axioms displaceReference_valid

/-- Checked reference addition preserves memory and returns only a valid reference. -/
theorem referenceAddInstruction_contract (size : Nat) (signed : Bool)
    (stack values : List Value) (memory result : Memory)
    (executed : referenceAddInstruction size signed stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold referenceAddInstruction at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | solve
      | cases executed
        exact InstructionContract.of_effect (.unchanged _) fun retained =>
          ValuesValid.cons (displaceReference_valid (by assumption)).1 retained.tail.tail
      | cases executed
        exact InstructionContract.of_effect (.unchanged _) fun retained =>
          ValuesValid.cons (displaceReference_valid (by assumption)).2 retained.tail.tail
    | cases executed
    | split at executed
#print axioms referenceAddInstruction_contract

/-- Wide multiplication and out-reference division preserve checked effects and stack validity. -/
theorem wideArithmeticInstruction_contract (operation : CIL.MemoryOp)
    (stack values : List Value) (memory result : Memory)
    (executed : wideArithmeticInstruction operation stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold wideArithmeticInstruction at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | solve | cases executed; instruction_contract_close
    | cases executed
    | split at executed
#print axioms wideArithmeticInstruction_contract

/-- Object field loads and stores preserve checked effects and stack validity. -/
theorem objectFieldInstruction_contract (operation : CIL.MemoryOp)
    (stack values : List Value) (memory result : Memory)
    (executed : objectFieldInstruction operation stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold objectFieldInstruction at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | solve | cases executed; instruction_contract_close
    | cases executed
    | split at executed
#print axioms objectFieldInstruction_contract

set_option maxHeartbeats 800000 in
/-- The remaining memory operations preserve their checked effects and stack validity. -/
private theorem otherMemoryInstruction_contract (operation : CIL.MemoryOp)
    (stack values : List Value) (memory result : Memory)
    (executed : otherMemoryInstruction operation stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold otherMemoryInstruction at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | solve | cases executed; instruction_contract_close
    | cases executed
    | split at executed
#print axioms otherMemoryInstruction_contract

/-- View observations preserve memory and return only valid references or scalar flags. -/
theorem viewObservationInstruction_contract (observation : CIL.ViewObservation)
    (stack values : List Value) (memory result : Memory)
    (observed : viewObservationInstruction observation stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold viewObservationInstruction at observed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at observed
  repeat' first
    | solve | cases observed; instruction_contract_close
    | cases observed
    | split at observed
#print axioms viewObservationInstruction_contract

/-- Endian transfers preserve checked writes and return initialized integer values. -/
theorem binaryTransferInstruction_contract (width : Nat) (signed bigEndian read trying : Bool)
    (stack values : List Value) (memory result : Memory)
    (transferred : binaryTransferInstruction width signed bigEndian read trying stack memory =
      .ok (result, values)) : InstructionContract memory result stack values := by
  unfold binaryTransferInstruction at transferred
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at transferred
  repeat' first
    | solve | cases transferred; instruction_contract_close
    | cases transferred
    | split at transferred
#print axioms binaryTransferInstruction_contract

/-- Single-reference construction preserves memory and validates the resulting view. -/
theorem singleSpanInstruction_contract (width : Nat) (writable : Bool)
    (stack values : List Value) (memory result : Memory)
    (constructed : singleSpanInstruction width writable stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold singleSpanInstruction at constructed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at constructed
  repeat' first
    | solve | cases constructed; instruction_contract_close
    | cases constructed
    | split at constructed
#print axioms singleSpanInstruction_contract

/-- Typed array transfers preserve checked effects and the validity of remaining stack values. -/
theorem arrayTransferInstruction_contract (element : CIL.ArrayElement) (store : Bool)
    (stack values : List Value) (memory result : Memory)
    (transferred : arrayTransferInstruction element store stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold arrayTransferInstruction at transferred
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at transferred
  repeat' first
    | solve | cases transferred; instruction_contract_close
    | cases transferred
    | split at transferred
#print axioms arrayTransferInstruction_contract

/-- Aligned transfers preserve the existing typed write effect and return only valid scalars. -/
theorem pointerTransferInstruction_contract (kind : CIL.TransferKind) (alignment : Nat)
    (store : Bool) (stack values : List Value) (memory result : Memory)
    (transferred : pointerTransferInstruction kind alignment store stack memory =
      .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold pointerTransferInstruction at transferred
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at transferred
  repeat' first
    | solve | cases transferred; instruction_contract_close
    | cases transferred
    | split at transferred
#print axioms pointerTransferInstruction_contract

/-- Vector128 byte loads and stores have the checked load and store effects of `load128` and
    `store128` and return only valid scalars. -/
theorem vector128UnsafeInstruction_contract (store offset : Bool) (stack values : List Value)
    (memory result : Memory)
    (transferred : vector128UnsafeInstruction store offset stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold vector128UnsafeInstruction displaceReference at transferred
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at transferred
  repeat' first
    | solve | cases transferred; instruction_contract_close
    | cases transferred
    | split at transferred
#print axioms vector128UnsafeInstruction_contract

/-- `Vector128.LoadUnsafe(ref source)` is the checked `load128`. -/
theorem vector128Load_eq_load128 (reference : ManagedReference) (rest : List Value)
    (memory : Memory) :
    memoryInstruction (.vector128Unsafe false false) (.reference reference :: rest) memory =
      memoryInstruction .load128 (.reference reference :: rest) memory := by
  simp [memoryInstruction, vector128UnsafeInstruction, otherMemoryInstruction,
    unspecifiedOperands, CIL.MemoryOp.argumentCount, Value.hasUnspecified]
#print axioms vector128Load_eq_load128

/-- `Vector128.LoadUnsafe(ref source, offset)` is `Unsafe.Add` by `offset` bytes, then the
    checked `load128` of the displaced reference. -/
theorem vector128LoadAt_eq_add_load128 (offset : CIL.W64) (reference : ManagedReference)
    (rest : List Value) (memory : Memory) :
    memoryInstruction (.vector128Unsafe false true)
      (.scalar (.i64 offset) :: .reference reference :: rest) memory =
    (memoryInstruction (.add 1 false) (.scalar (.i64 offset) :: .reference reference :: rest)
      memory).bind fun (added, stack) => memoryInstruction .load128 stack added := by
  rcases located : referenceAt reference with _ | address
  · simp [memoryInstruction, vector128UnsafeInstruction, referenceAddInstruction,
      displaceReference, unspecifiedOperands, CIL.MemoryOp.argumentCount, CIL.offsetValue,
      Value.hasUnspecified, CIL.Value.hasUnspecified, located, Bind.bind, Except.bind]
  · rcases moved : checkedAt reference 0 (add memory address 1 offset) with _ | target <;>
    simp [memoryInstruction, vector128UnsafeInstruction, referenceAddInstruction,
      otherMemoryInstruction, displaceReference, unspecifiedOperands, CIL.MemoryOp.argumentCount,
      CIL.offsetValue, Value.hasUnspecified, CIL.Value.hasUnspecified, located, moved, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
#print axioms vector128LoadAt_eq_add_load128

/-- `Vector128.StoreUnsafe(source, ref destination)` is the checked `store128`, which takes
    its operands in the other order. -/
theorem vector128Store_eq_store128 (bits : BitVec 128) (reference : ManagedReference)
    (rest : List Value) (memory : Memory) :
    memoryInstruction (.vector128Unsafe true false)
      (.reference reference :: .scalar (.v128 bits) :: rest) memory =
      memoryInstruction .store128 (.scalar (.v128 bits) :: .reference reference :: rest)
        memory := by
  simp [memoryInstruction, vector128UnsafeInstruction, otherMemoryInstruction,
    unspecifiedOperands, CIL.MemoryOp.argumentCount, Value.hasUnspecified,
    CIL.Value.hasUnspecified]
#print axioms vector128Store_eq_store128

/-- `Vector128.StoreUnsafe(source, ref destination, offset)` is `Unsafe.Add` by `offset`
    bytes, then the checked `store128` through the displaced reference. -/
theorem vector128StoreAt_eq_add_store128 (offset : CIL.W64) (bits : BitVec 128)
    (reference : ManagedReference) (rest : List Value) (memory : Memory) :
    memoryInstruction (.vector128Unsafe true true)
      (.scalar (.i64 offset) :: .reference reference :: .scalar (.v128 bits) :: rest) memory =
    (memoryInstruction (.add 1 false) (.scalar (.i64 offset) :: .reference reference :: rest)
      memory).bind fun (added, stack) => match stack with
        | .reference moved :: rest =>
          memoryInstruction .store128 (.scalar (.v128 bits) :: .reference moved :: rest) added
        | _ => .error .invalidState := by
  rcases located : referenceAt reference with _ | address
  · simp [memoryInstruction, vector128UnsafeInstruction, referenceAddInstruction,
      displaceReference, unspecifiedOperands, CIL.MemoryOp.argumentCount, CIL.offsetValue,
      Value.hasUnspecified, CIL.Value.hasUnspecified, located, Bind.bind, Except.bind]
  · rcases moved : checkedAt reference 0 (add memory address 1 offset) with _ | target <;>
    simp [memoryInstruction, vector128UnsafeInstruction, referenceAddInstruction,
      otherMemoryInstruction, displaceReference, unspecifiedOperands, CIL.MemoryOp.argumentCount,
      CIL.offsetValue, Value.hasUnspecified, CIL.Value.hasUnspecified, located, moved, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
#print axioms vector128StoreAt_eq_add_store128

/-- Checked memory dispatch preserves the effects and stack validity of its selected family. -/
theorem memoryInstruction_contract (operation : CIL.MemoryOp) (stack values : List Value)
    (m result : Memory) (h : memoryInstruction operation stack m = .ok (result, values)) :
    InstructionContract m result stack values := by
  unfold memoryInstruction at h
  split at h
  · cases h
  · split at h
    · exact referenceAddInstruction_contract _ _ _ _ _ _ h
    · exact pointerTransferInstruction_contract _ _ _ _ _ _ _ h
    · exact vector128UnsafeInstruction_contract _ _ _ _ _ _ h
    · exact arrayTransferInstruction_contract _ _ _ _ _ _ h
    · exact binaryTransferInstruction_contract _ _ _ _ _ _ _ _ _ h
    · exact binaryTransferInstruction_contract _ _ _ _ _ _ _ _ _ h
    · exact singleSpanInstruction_contract _ _ _ _ _ _ h
    · exact viewObservationInstruction_contract _ _ _ _ _ h
    · exact spanCopyInstruction_contract _ _ _ _ _ _ h
    · exact spanFillInstruction_contract _ _ _ _ _ _ h
    · exact arrayFillInstruction_contract _ _ _ _ _ _ h
    · exact wideArithmeticInstruction_contract _ _ _ _ _ h
    · exact wideArithmeticInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact objectFieldInstruction_contract _ _ _ _ _ h
    · exact otherMemoryInstruction_contract _ _ _ _ _ h

set_option maxHeartbeats 800000 in
theorem instruction_contract (operation : CIL.Op) (stack values : List Value) (m result : Memory)
    (h : instruction operation stack m = .ok (result, values)) :
    InstructionContract m result stack values := by
  unfold instruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals repeat' first
    | solve | apply memoryInstruction_contract; assumption
    | solve | cases h; instruction_contract_close
    | cases h
    | split at h

theorem memoryInstruction_effect (operation : CIL.MemoryOp) (stack values : List Value)
    (m result : Memory) (h : memoryInstruction operation stack m = .ok (result, values)) :
    InstructionEffect m result := (memoryInstruction_contract _ _ _ _ _ h).effect

theorem instruction_effect (operation : CIL.Op) (stack values : List Value) (m result : Memory)
    (h : instruction operation stack m = .ok (result, values)) : InstructionEffect m result :=
  (instruction_contract _ _ _ _ _ h).effect

theorem checked_write_preserves_wellFormed (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) (reference : ManagedReference) (width : Nat)
    (hm : m.WellFormed)
    (h : checkedAt reference width (write m r bytes alignment) = .ok result) :
    result.WellFormed := by
  exact write_preserves_wellFormed _ _ _ _ _ hm (checkedAt_ok h)

theorem storeValue_preserves_wellFormed (m result : Memory) (reference : ManagedReference)
    (value : CIL.Value) (hm : m.WellFormed)
    (h : storeValue m reference value = .ok result) : result.WellFormed := by
  exact (storeValue_effect _ _ _ _ h).wellFormed hm

#print axioms storeValue_preserves_wellFormed

set_option maxHeartbeats 800000 in
theorem memoryInstruction_preserves_wellFormed (operation : CIL.MemoryOp)
    (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed)
    (h : memoryInstruction operation stack m = .ok (result, values)) : result.WellFormed := by
  exact (memoryInstruction_effect _ _ _ _ _ h).wellFormed hm

#print axioms memoryInstruction_preserves_wellFormed

set_option maxHeartbeats 800000 in
theorem instruction_preserves_wellFormed (operation : CIL.Op) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed)
    (h : instruction operation stack m = .ok (result, values)) : result.WellFormed := by
  exact (instruction_effect _ _ _ _ _ h).wellFormed hm

#print axioms instruction_preserves_wellFormed

end CIL.Safety
