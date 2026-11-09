import CIL.Safety.SpanContents
import CIL.Safety.ArrayViewLemmas
import CIL.Safety.StepComposition

/-!
# Reading a supplied array

An array argument is an `ArrayView` whose bytes are the span `view.storage`, so the facts a
method needs of its elements are `SpanContents` over that span. `SpanContents.array_load`
turns them into the element reference and loaded value of an in-bound index; a null array
has no elements, so the bound alone rules it out. `step_arrayLoad_of_element` and
`step_arrayAddress_of_element` step `ldelem` and `ldelema` from those facts, and
`arrayElement_formed` lets a method return the element address.
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

end CIL.Safety
