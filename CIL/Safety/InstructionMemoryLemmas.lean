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
  | .methodPointer _ | .methodTable _ => True
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

theorem InstructionEffect.wellFormed {m result : Memory} (effect : InstructionEffect m result)
    (hm : m.WellFormed) : result.WellFormed := by
  cases effect with
  | unchanged => exact hm
  | write h => exact write_preserves_wellFormed _ _ _ _ _ hm h
  | snapshot h => exact writeSnapshot_preserves_wellFormed _ _ _ _ _ hm h

theorem InstructionEffect.allocations {m result : Memory} (effect : InstructionEffect m result) :
    AllocationExtension m result := by
  cases effect with
  | unchanged => exact .refl _
  | write h => exact write_extends_allocations _ _ _ _ _ h
  | snapshot h => exact writeSnapshot_extends_allocations _ _ _ _ _ h

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
  unfold SpanView.fill at filled
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
  unfold SpanView.fillSnapshot at filled
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

/-- Checked memory dispatch preserves the effects and stack validity of its selected family. -/
theorem memoryInstruction_contract (operation : CIL.MemoryOp) (stack values : List Value)
    (m result : Memory) (h : memoryInstruction operation stack m = .ok (result, values)) :
    InstructionContract m result stack values := by
  unfold memoryInstruction at h
  split at h
  · cases h
  · split at h
    · exact arrayTransferInstruction_contract _ _ _ _ _ _ h
    · exact binaryTransferInstruction_contract _ _ _ _ _ _ _ _ _ h
    · exact binaryTransferInstruction_contract _ _ _ _ _ _ _ _ _ h
    · exact singleSpanInstruction_contract _ _ _ _ _ _ h
    · exact viewObservationInstruction_contract _ _ _ _ _ h
    · exact spanCopyInstruction_contract _ _ _ _ _ _ h
    · exact spanFillInstruction_contract _ _ _ _ _ _ h
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
