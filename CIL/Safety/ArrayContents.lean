import CIL.Safety.SpanContents
import CIL.Safety.ArrayViewLemmas
import CIL.Safety.StepComposition
import CIL.Safety.BufferContents

/-!
# Reading a supplied array

An array argument is an `ArrayView` whose bytes are the span `view.storage`, so the facts a
method needs of its elements are `SpanContents` over that span. `SpanContents.array_load`
turns them into the element reference and loaded value of an in-bound index; a null array
has no elements, so the bound alone rules it out. `step_ldelem_of_element` steps `ldelem`,
`step_ldelem_any_of_element` a typed `ldelem` and `step_ldelema_of_element` an `ldelema` of
the element's shape from those facts, and `step_ldelem_any_of_transfer` a typed `ldelem` of a
struct or vector element from its transfer. `arrayLoad_of_element` and
`arrayAddress_of_element` read a typed `ldelem` and an `ldelema` once they step to
`arrayLoad` and `arrayAddress`;
`arrayElement_formed` lets a method return the element address. A loop indexing the array
names the element it stores to with `arrayElement_of_access` and steps `stelem` with
`step_stelem_narrow_of_write` or `step_stelem_wide_of_write`, or a typed `stelem` with
`step_stelem_any_of_write`, `step_stelem_any_of_wide_write` or `step_stelem_any_of_transfer`,
and reads one that steps to `arrayStore` with `arrayStore_of_write`; `SpanView.length_bounded` of
the storage span lets its signed bound test read as unsigned.
-/

namespace CIL.Safety

/-- A reference-slot store preserves the scalar contents of a span: slots and bytes are
    separate parts of memory. -/
theorem SpanContents.after_setSlot {memory : Memory} {view : SpanView} {width : Nat}
    {values : List (BitVec (8 * width))} (contents : SpanContents memory view width values)
    (field : Reference) (value : ManagedReference) :
    SpanContents (setSlot memory field value) view width values := by
  obtain ⟨typed, length, held⟩ := contents
  refine ⟨typed, length, ?_⟩
  cases address : view.reference <;> simp only [address] at held ⊢
  · exact held
  · exact fun index word found => held index word found

#print axioms SpanContents.after_setSlot

/-- Contents of a view valid in caller memory survive a confined change whose footprint is
    disjoint from the view. Only the caller memory needs to be well formed. -/
theorem SpanContents.after_confined_valid {anchor before after : Memory} {view : SpanView}
    {width : Nat} {values : List (BitVec (8 * width))} {footprint : List (Reference × Nat)}
    (contents : SpanContents before view width values) (valid : view.validate anchor = .ok ())
    (wellFormed : anchor.WellFormed) (older : anchor.nextIdentity ≤ before.nextIdentity)
    (framed : Confined footprint before after)
    (apart : ∀ base, view.reference = .address base →
      ∀ entry ∈ footprint, Apart base (width * values.length) entry) :
    SpanContents after view width values := by
  refine ⟨contents.elementWidth, contents.length, ?_⟩
  have shape := contents.contents
  cases address : view.reference with
  | null => simpa only [address] using shape
  | address base =>
    simp only [address] at shape ⊢
    intro index word found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have old := Nat.lt_of_lt_of_le (SpanView.allocation_below valid wellFormed address) older
    exact (framed.read_eq (base.element width index) old width 1
      (Outside.of_apart fun entry member =>
        (apart base address entry member).sub (element_le bound))).trans (shape index word found)

#print axioms SpanContents.after_confined_valid

/-- An in-bound element of an array holding `values` has an address whose load is that
    element. -/
theorem SpanContents.array_load {memory : Memory} {view : ArrayView} {width : Nat}
    {values : List (BitVec (8 * width))}
    (contents : SpanContents memory view.storage width values)
    (valid : view.validate memory = .ok ()) (scalar : ScalarWidth width) {index : Nat}
    (bound : index < values.length) :
    ∃ reference, arrayElement memory view index width = .ok reference ∧
      loadValue memory (.address reference) width =
        .ok (numericOfWidth width values[index].toNat) := by
  obtain ⟨reference, element, loaded⟩ :=
    contents.load valid scalar (List.getElem?_eq_getElem bound)
  refine ⟨reference, ?_, loaded⟩
  have typed : view.elementType.width = width := contents.elementWidth
  have length : view.length = values.length := contents.length
  have present : (view.reference == .null) = false := by
    have shape := contents.contents
    cases reference : view.reference with
    | null =>
      simp only [ArrayView.storage, reference] at shape
      simp [shape] at bound
    | address _ => rfl
  simp only [ArrayView.validate] at valid
  simp [arrayElement, ArrayView.element, ArrayView.validate, valid, typed, present, length, bound,
    element, checkedAt, Except.mapError, Bind.bind, Except.bind]

#print axioms SpanContents.array_load

/-- A numeric element load whose address and load succeed pushes the loaded value; a typed
    `ldelem` of a numeric element steps to this load. -/
theorem arrayLoad_of_element {memory : Memory} {view : ArrayView} {index : CIL.Value}
    {position width : Nat} {signed : Bool} {reference : Reference} {value : CIL.Value}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position width = .ok reference)
    (loaded : loadValue memory (.address reference) width signed = .ok value) :
    ∀ rest, arrayLoad width signed (.scalar index :: .array view :: rest) memory =
      .ok (memory, .scalar value :: rest) := by
  intro rest
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [arrayLoad, arrayIndex, found, loaded, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms arrayLoad_of_element

/-- `ldelem` of `kind` from an element whose address and load succeed pushes the loaded value. -/
theorem step_ldelem_of_element (kind : CIL.NumericKind) {memory : Memory} {view : ArrayView}
    {index : CIL.Value} {position : Nat} {reference : Reference} {value : CIL.Value}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position kind.width = .ok reference)
    (loaded : loadValue memory (.address reference) kind.width kind.signed = .ok value) :
    ∀ body pc args frame rest,
      step body (.ldelem kind) pc args frame (.scalar index :: .array view :: rest) memory =
        .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro body pc args frame rest
  rw [step_ldelem_eq]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;> cases kind <;>
    simp [instructionStep, instruction, elementInstruction, observerCount, unspecifiedOperands,
      Value.hasUnspecified, CIL.Value.hasUnspecified, arrayLoad, arrayIndex, found, loaded,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_ldelem_of_element

/-- `ldelema` of an element of the array's own element type gives the element's address,
    read-only unless `writable`. -/
theorem arrayAddress_of_element {memory : Memory} {view : ArrayView} {index : CIL.Value}
    {element : CIL.ArrayElement} {position : Nat} {reference : Reference} (writable : Bool)
    (typed : view.elementType = element) (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position element.width = .ok reference) :
    ∀ rest, arrayAddress element writable (.scalar index :: .array view :: rest) memory =
      .ok (memory, (if writable then .reference (.address reference)
        else .readOnlyReference (.address reference)) :: rest) := by
  intro rest
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [arrayAddress, arrayIndex, typed, found, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms arrayAddress_of_element

/-- `ldelema` of a type the method's layouts give the array's own element shape pushes the
    element's address, read-only exactly when the instruction is. -/
theorem step_ldelema_of_element {body : CIL.Method} {type : CIL.Extraction.TypeExpr}
    {memory : Memory} {view : ArrayView} {index : CIL.Value} {element : CIL.ArrayElement}
    {position : Nat} {reference : Reference} (readOnly : Bool)
    (shape : body.elementShape type = .value element) (typed : view.elementType = element)
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position element.width = .ok reference) :
    ∀ pc args frame rest, step body (.ldelema type readOnly) pc args frame
        (.scalar index :: .array view :: rest) memory =
      .ok (.next (pc + 1) ((if readOnly then .readOnlyReference (.address reference)
        else .reference (.address reference)) :: rest) frame memory) := by
  intro pc args frame rest
  rw [step_ldelema_eq, shape]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;> cases readOnly <;>
    simp [unspecifiedOperands, Value.hasUnspecified, CIL.Value.hasUnspecified,
      elementAddressInstruction, arrayAddress, arrayIndex, typed, found, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

#print axioms step_ldelema_of_element

/-- A typed `ldelem` of a type the method's layouts give a numeric element shape pushes the
    value the element's load reads. -/
theorem step_ldelem_any_of_element {body : CIL.Method} {type : CIL.Extraction.TypeExpr}
    {memory : Memory} {view : ArrayView} {index : CIL.Value} {element : CIL.ArrayElement}
    {position : Nat} {reference : Reference} {value : CIL.Value}
    (shape : body.elementShape type = .value element) (numeric : element.composite = false)
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position element.width = .ok reference)
    (loaded : loadValue memory (.address reference) element.width element.signed = .ok value) :
    ∀ pc args frame rest, step body (.ldelem_any type) pc args frame
        (.scalar index :: .array view :: rest) memory =
      .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro pc args frame rest
  rw [step_ldelem_any_eq, shape]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [typedElementInstruction, numeric, unspecifiedOperands, Value.hasUnspecified,
      CIL.Value.hasUnspecified, arrayLoad, arrayIndex, found, loaded, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

#print axioms step_ldelem_any_of_element

/-- A typed `ldelem` of a type the method's layouts give a struct or vector element shape pushes
    the snapshot the element's transfer reads. -/
theorem step_ldelem_any_of_transfer {body : CIL.Method} {type : CIL.Extraction.TypeExpr}
    {memory : Memory} {view : ArrayView} {index : CIL.Value} {element : CIL.ArrayElement}
    {position : Nat} {value : CIL.Value}
    (shape : body.elementShape type = .value element) (composite : element.composite = true)
    (indexed : arrayIndex index = some position)
    (transferred : ∀ rest, arrayTransferInstruction element false
      (.scalar index :: .array view :: rest) memory = .ok (memory, .scalar value :: rest)) :
    ∀ pc args frame rest, step body (.ldelem_any type) pc args frame
        (.scalar index :: .array view :: rest) memory =
      .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro pc args frame rest
  rw [step_ldelem_any_eq, shape]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [typedElementInstruction, composite, unspecifiedOperands, Value.hasUnspecified,
      CIL.Value.hasUnspecified, transferred, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_ldelem_any_of_transfer

/-- An element address an array access returns forms in the same memory, so a method may
    return it. -/
theorem arrayElement_formed {memory : Memory} {view : ArrayView} {index width : Nat}
    {reference : Reference} (found : arrayElement memory view index width = .ok reference) :
    form memory reference = .ok reference := by
  unfold arrayElement at found
  repeat' first
    | exact view.element_formed memory index reference ‹_›
    | cases found
    | split at found
    | simp only [checkedAt, Except.mapError, Bind.bind, Except.bind] at found

#print axioms arrayElement_formed

/-- An in-bound element of a valid array that may be accessed is the array's element at that
    index, so a loop holding write authority over it may store there. -/
theorem arrayElement_of_access {memory : Memory} {view : ArrayView} {base : Reference}
    {index width : Nat} {writing : Bool}
    (valid : view.validate memory = .ok ()) (address : view.reference = .address base)
    (typed : view.elementType.width = width) (bound : index < view.length)
    (target : access memory (base.element width index) width 1 writing = .ok ()) :
    arrayElement memory view index width = .ok (base.element width index) := by
  have formed := access_reference_valid _ _ _ _ _ target
  have moved :
      { base with offset := base.offset + index * width } = base.element width index := by
    simp [Reference.element, Nat.mul_comm]
  have stored : view.storage.reference = .address base := address
  have length : view.storage.length = view.length := rfl
  have sized : view.storage.width = width := typed
  have checked : view.storage.validate memory = .ok () := valid
  have element : view.storage.element memory index = .ok (base.element width index) := by
    simp [SpanView.element, checked, length, bound, stored, sized, moved, formed, Bind.bind,
      Except.bind]
  have present : (view.reference == .null) = false := by simp [address]
  simp [arrayElement, ArrayView.element, ArrayView.validate, checked, typed, present, element,
    bound, checkedAt, Except.mapError, Bind.bind, Except.bind]

#print axioms arrayElement_of_access

/-- A numeric element store of a 1-, 2- or 4-byte word whose write succeeds leaves that write's
    memory; a typed `stelem` of a numeric element steps to this store. -/
theorem arrayStore_of_write {memory after : Memory} {view : ArrayView} {index : CIL.Value}
    {position width : Nat} {reference : Reference} {bits : CIL.W32}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position width = .ok reference)
    (written : write memory reference (numberBytes bits.toNat width) 1 = .ok after)
    (narrow : width = 1 ∨ width = 2 ∨ width = 4 := by decide) :
    ∀ rest, arrayStore width (.scalar (.i32 bits) :: .scalar index :: .array view :: rest) memory =
      .ok (after, rest) := by
  intro rest
  rcases narrow with rfl | rfl | rfl <;>
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [arrayStore, arrayIndex, found, written, checkedAt, Except.mapError, Bind.bind,
      Except.bind, Pure.pure, Except.pure]

#print axioms arrayStore_of_write

/-- A numeric element store of an 8-byte word whose write succeeds leaves that write's memory;
    a typed `stelem` of an 8-byte element steps to this store. -/
theorem arrayStore_i64_of_write {memory after : Memory} {view : ArrayView}
    {index : CIL.Value} {position : Nat} {reference : Reference} {bits : CIL.W64}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position 8 = .ok reference)
    (written : write memory reference (numberBytes bits.toNat 8) 1 = .ok after) :
    ∀ rest, arrayStore 8 (.scalar (.i64 bits) :: .scalar index :: .array view :: rest) memory =
      .ok (after, rest) := by
  intro rest
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [arrayStore, arrayIndex, found, written, checkedAt, Except.mapError, Bind.bind,
      Except.bind, Pure.pure, Except.pure]

#print axioms arrayStore_i64_of_write

/-- `stelem` of a 1-, 2- or 4-byte `kind` into an element whose write succeeds leaves that
    write's memory. -/
theorem step_stelem_narrow_of_write (kind : CIL.NumericKind) {memory after : Memory}
    {view : ArrayView} {index : CIL.Value} {position : Nat} {reference : Reference}
    {bits : CIL.W32}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position kind.width = .ok reference)
    (written : write memory reference (numberBytes bits.toNat kind.width) 1 = .ok after)
    (narrow : kind.width = 1 ∨ kind.width = 2 ∨ kind.width = 4 := by decide) :
    ∀ body pc args frame rest,
      step body (.stelem kind) pc args frame
        (.scalar (.i32 bits) :: .scalar index :: .array view :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_stelem_eq]
  cases kind <;> simp only [CIL.NumericKind.width] at narrow found written <;>
    (try (exfalso; revert narrow; decide)) <;>
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [instructionStep, instruction, elementInstruction, observerCount, unspecifiedOperands,
      Value.hasUnspecified, CIL.Value.hasUnspecified, CIL.NumericKind.width, arrayStore,
      arrayIndex, found, written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
      Except.pure]

#print axioms step_stelem_narrow_of_write

/-- `stelem.i8` or `stelem.i` of an 8-byte word into an element whose write succeeds leaves that
    write's memory. -/
theorem step_stelem_wide_of_write (kind : CIL.NumericKind) {memory after : Memory}
    {view : ArrayView} {index : CIL.Value} {position : Nat} {reference : Reference}
    {bits : CIL.W64}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position 8 = .ok reference)
    (written : write memory reference (numberBytes bits.toNat 8) 1 = .ok after)
    (wide : kind = .i8 ∨ kind = .i := by decide) :
    ∀ body pc args frame rest,
      step body (.stelem kind) pc args frame
        (.scalar (.i64 bits) :: .scalar index :: .array view :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_stelem_eq]
  rcases wide with rfl | rfl <;>
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [instructionStep, instruction, elementInstruction, observerCount, unspecifiedOperands,
      Value.hasUnspecified, CIL.Value.hasUnspecified, CIL.NumericKind.width, arrayStore,
      arrayIndex, found, written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
      Except.pure]

#print axioms step_stelem_wide_of_write

/-- A typed `stelem` of a 1-, 2- or 4-byte word into a numeric element whose write succeeds
    leaves that write's memory. -/
theorem step_stelem_any_of_write {body : CIL.Method} {type : CIL.Extraction.TypeExpr}
    {memory after : Memory} {view : ArrayView} {index : CIL.Value} {element : CIL.ArrayElement}
    {position : Nat} {reference : Reference} {bits : CIL.W32}
    (shape : body.elementShape type = .value element) (numeric : element.composite = false)
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position element.width = .ok reference)
    (written : write memory reference (numberBytes bits.toNat element.width) 1 = .ok after)
    (narrow : element.width = 1 ∨ element.width = 2 ∨ element.width = 4 := by decide) :
    ∀ pc args frame rest, step body (.stelem_any type) pc args frame
        (.scalar (.i32 bits) :: .scalar index :: .array view :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  intro pc args frame rest
  have stored := arrayStore_of_write indexed found written narrow rest
  rw [step_stelem_any_eq, shape]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [typedElementInstruction, numeric, unspecifiedOperands, Value.hasUnspecified,
      CIL.Value.hasUnspecified, stored, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_stelem_any_of_write

/-- A typed `stelem` of an 8-byte word into a numeric element whose write succeeds leaves that
    write's memory. -/
theorem step_stelem_any_of_wide_write {body : CIL.Method} {type : CIL.Extraction.TypeExpr}
    {memory after : Memory} {view : ArrayView} {index : CIL.Value} {element : CIL.ArrayElement}
    {position : Nat} {reference : Reference} {bits : CIL.W64}
    (shape : body.elementShape type = .value element) (numeric : element.composite = false)
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position 8 = .ok reference)
    (written : write memory reference (numberBytes bits.toNat 8) 1 = .ok after)
    (wide : element.width = 8 := by decide) :
    ∀ pc args frame rest, step body (.stelem_any type) pc args frame
        (.scalar (.i64 bits) :: .scalar index :: .array view :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  intro pc args frame rest
  have stored := arrayStore_i64_of_write indexed found written rest
  rw [step_stelem_any_eq, shape]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [typedElementInstruction, numeric, wide, unspecifiedOperands, Value.hasUnspecified,
      CIL.Value.hasUnspecified, stored, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_stelem_any_of_wide_write

/-- A typed `stelem` of a specified value into a struct or vector element whose transfer succeeds
    leaves that transfer's memory. -/
theorem step_stelem_any_of_transfer {body : CIL.Method} {type : CIL.Extraction.TypeExpr}
    {memory after : Memory} {view : ArrayView} {index : CIL.Value} {element : CIL.ArrayElement}
    {position : Nat} {value : CIL.Value}
    (shape : body.elementShape type = .value element) (composite : element.composite = true)
    (indexed : arrayIndex index = some position) (specified : value.hasUnspecified = false)
    (transferred : ∀ rest, arrayTransferInstruction element true
      (.scalar value :: .scalar index :: .array view :: rest) memory = .ok (after, rest)) :
    ∀ pc args frame rest, step body (.stelem_any type) pc args frame
        (.scalar value :: .scalar index :: .array view :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  intro pc args frame rest
  rw [step_stelem_any_eq, shape]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [typedElementInstruction, composite, unspecifiedOperands, Value.hasUnspecified,
      CIL.Value.hasUnspecified, transferred, Bind.bind, Except.bind, Pure.pure, Except.pure] <;>
    exact specified

#print axioms step_stelem_any_of_transfer

/-- `values` are the elements of a span over the whole array in either access mode, which shares
    its storage extent. -/
theorem SpanContents.array_span {memory : Memory} {view : ArrayView} {width : Nat}
    {values : List (BitVec (8 * width))} (contents : SpanContents memory view.storage width values)
    (writable : Bool) : SpanContents memory (view.span writable) width values :=
  ⟨contents.elementWidth, contents.length, contents.contents⟩

#print axioms SpanContents.array_span

/-- A span over the whole of a valid array holding `values` is checked to hold them. -/
theorem CheckedSpan.of_array {memory : Memory} {view : ArrayView} {width : Nat}
    {values : List (BitVec (8 * width))} (valid : view.validate memory = .ok ())
    (contents : SpanContents memory view.storage width values) (writable : Bool) :
    CheckedSpan memory (view.span writable) width writable values :=
  ⟨ArrayView.span_valid writable valid, rfl, contents.array_span writable⟩

#print axioms CheckedSpan.of_array

/-- Converting a valid array of `element`s to a span over all of it pushes that span. -/
theorem step_arraySpan_whole {memory : Memory} {view : ArrayView} {element : CIL.ArrayElement}
    {writable : Bool} (typed : view.elementType = element)
    (valid : view.validate memory = .ok ()) :
    ∀ body pc frame rest,
      modelStep (some (.memory (.arraySpan element writable .whole))) body pc frame
        (.array view :: rest) memory =
        .ok (.next (pc + 1) (.bufferSpan (view.span writable) :: rest) frame memory) := by
  intro body pc frame rest
  subst typed
  have checked : (view.span writable).validate memory = .ok () :=
    ArrayView.span_valid writable valid
  simp only [ArrayView.span] at checked
  rw [modelStep_memory]
  simp [unspecifiedOperands, CIL.MemoryOp.argumentCount, CIL.ArraySpanRange.argumentCount,
    Value.hasUnspecified, staticInstruction, memoryInstruction, otherMemoryInstruction, checked,
    viewOperandCount, viewOperands, spanView,
    ArrayView.span, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_arraySpan_whole

end CIL.Safety
