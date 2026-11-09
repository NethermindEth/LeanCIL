import CIL.Safety.SpanContents
import CIL.Safety.ArrayViewLemmas
import CIL.Safety.StepComposition
import CIL.Safety.BufferContents

/-!
# Reading a supplied array

An array argument is an `ArrayView` whose bytes are the span `view.storage`, so the facts a
method needs of its elements are `SpanContents` over that span. `SpanContents.array_load`
turns them into the element reference and loaded value of an in-bound index; a null array
has no elements, so the bound alone rules it out. `step_arrayLoad_of_element` and
`step_arrayAddress_of_element` step `ldelem` and `ldelema` from those facts, and
`arrayElement_formed` lets a method return the element address. A loop indexing the array
names the element it stores to with `arrayElement_of_access` and steps `stelem` with
`step_arrayStore_of_write`; `SpanView.length_bounded` of the storage span lets its signed bound
test read as unsigned.
-/

namespace CIL.Safety

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

/-- `ldelem` of an element whose address and load succeed pushes the loaded value. -/
theorem step_arrayLoad_of_element {memory : Memory} {view : ArrayView} {index : CIL.Value}
    {position width : Nat} {signed : Bool} {reference : Reference} {value : CIL.Value}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position width = .ok reference)
    (loaded : loadValue memory (.address reference) width signed = .ok value) :
    ∀ body pc args frame rest,
      step body (.memory (.arrayLoad width signed)) pc args frame
        (.scalar index :: .array view :: rest) memory =
        .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro body pc args frame rest
  rw [step_memory_eq]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [unspecifiedOperands, CIL.MemoryOp.argumentCount, Value.hasUnspecified,
      CIL.Value.hasUnspecified, staticInstruction, memoryInstruction, otherMemoryInstruction,
      arrayIndex, found, loaded, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_arrayLoad_of_element

/-- `ldelema` of an element of the array's own element type pushes the element's address. -/
theorem step_arrayAddress_of_element {memory : Memory} {view : ArrayView} {index : CIL.Value}
    {element : CIL.ArrayElement} {position : Nat} {reference : Reference}
    (typed : view.elementType = element) (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position element.width = .ok reference) :
    ∀ body pc args frame rest,
      step body (.memory (.arrayAddress element)) pc args frame
        (.scalar index :: .array view :: rest) memory =
        .ok (.next (pc + 1) (.reference (.address reference) :: rest) frame memory) := by
  intro body pc args frame rest
  rw [step_memory_eq]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [unspecifiedOperands, CIL.MemoryOp.argumentCount, Value.hasUnspecified,
      CIL.Value.hasUnspecified, staticInstruction, memoryInstruction, otherMemoryInstruction,
      arrayIndex, typed, found, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_arrayAddress_of_element

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

/-- `stelem` of a 1-, 2- or 4-byte word into an element whose write succeeds leaves that
    write's memory. -/
theorem step_arrayStore_of_write {memory after : Memory} {view : ArrayView} {index : CIL.Value}
    {position width : Nat} {reference : Reference} {bits : CIL.W32}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position width = .ok reference)
    (written : write memory reference (numberBytes bits.toNat width) 1 = .ok after)
    (narrow : width = 1 ∨ width = 2 ∨ width = 4 := by decide) :
    ∀ body pc args frame rest,
      step body (.memory (.arrayStore width)) pc args frame
        (.scalar (.i32 bits) :: .scalar index :: .array view :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_memory_eq]
  rcases narrow with rfl | rfl | rfl <;>
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [unspecifiedOperands, CIL.MemoryOp.argumentCount, Value.hasUnspecified,
      CIL.Value.hasUnspecified, staticInstruction, memoryInstruction, otherMemoryInstruction,
      arrayIndex, found, written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
      Except.pure]

#print axioms step_arrayStore_of_write

/-- `stelem` of an 8-byte word into an element whose write succeeds leaves that write's
    memory. -/
theorem step_arrayStore_i64_of_write {memory after : Memory} {view : ArrayView}
    {index : CIL.Value} {position : Nat} {reference : Reference} {bits : CIL.W64}
    (indexed : arrayIndex index = some position)
    (found : arrayElement memory view position 8 = .ok reference)
    (written : write memory reference (numberBytes bits.toNat 8) 1 = .ok after) :
    ∀ body pc args frame rest,
      step body (.memory (.arrayStore 8)) pc args frame
        (.scalar (.i64 bits) :: .scalar index :: .array view :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_memory_eq]
  cases index <;> simp only [arrayIndex, reduceCtorEq, Option.some.injEq] at indexed <;>
    subst indexed <;>
    simp [unspecifiedOperands, CIL.MemoryOp.argumentCount, Value.hasUnspecified,
      CIL.Value.hasUnspecified, staticInstruction, memoryInstruction, otherMemoryInstruction,
      arrayIndex, found, written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
      Except.pure]

#print axioms step_arrayStore_i64_of_write

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
    ∀ body pc args frame rest,
      step body (.memory (.arraySpan element writable .whole)) pc args frame
        (.array view :: rest) memory =
        .ok (.next (pc + 1) (.bufferSpan (view.span writable) :: rest) frame memory) := by
  intro body pc args frame rest
  subst typed
  have checked : (view.span writable).validate memory = .ok () :=
    ArrayView.span_valid writable valid
  simp only [ArrayView.span] at checked
  rw [step_memory_eq]
  simp [unspecifiedOperands, CIL.MemoryOp.argumentCount, CIL.ArraySpanRange.argumentCount,
    Value.hasUnspecified, staticInstruction, memoryInstruction, otherMemoryInstruction, checked,
    ArrayView.span, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_arraySpan_whole

end CIL.Safety
