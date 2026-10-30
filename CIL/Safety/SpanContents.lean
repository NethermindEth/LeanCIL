import CIL.Safety.BufferContents
import CIL.Safety.SpanSliceProgress

/-!
# Symbolic span contents

`SpanContents memory view width values` ties a span view to the mathematical list it holds,
including null empty views. The element, head and tail lemmas let a loop that reads `view[0]`
and continues with `view.Slice(1)` carry the predicate across an iteration without unfolding
views, slices or byte reads.
-/

namespace CIL.Safety

/-- `view` has element width `width` and holds exactly `values`: a null view holds `[]` and an
    addressed view's elements read back from its base. Grants no write authority and does not
    assert that the view is valid. -/
structure SpanContents (memory : Memory) (view : SpanView) (width : Nat)
    (values : List (BitVec (8 * width))) : Prop where
  elementWidth : view.width = width
  length : view.length = values.length
  contents : match view.reference with
    | .null => values = []
    | .address base => Contents memory base width values

namespace SpanContents

variable {memory : Memory} {view : SpanView} {width : Nat}

/-- Every zero-length view of the element width holds the empty list, null or addressed. -/
theorem nil (sameWidth : view.width = width) (empty : view.length = 0) :
    SpanContents memory view width [] :=
  ⟨sameWidth, empty, by split <;> first | rfl | exact Contents.nil⟩

/-- Element `index` of a valid view is addressable and loads as the element's scalar value. -/
theorem load {values : List (BitVec (8 * width))} (contents : SpanContents memory view width values)
    (valid : view.validate memory = .ok ()) (scalar : ScalarWidth width) {index : Nat}
    {value : BitVec (8 * width)} (found : values[index]? = some value) :
    ∃ reference, view.element memory index = .ok reference ∧
      loadValue memory (.address reference) width = .ok (numericOfWidth width value.toNat) := by
  have shape := contents.contents
  have inside : index < view.length := by
    rw [contents.length]
    exact (List.getElem?_eq_some_iff.mp found).1
  cases address : view.reference with
  | null =>
    simp only [address] at shape
    simp [shape] at found
  | address base =>
    simp only [address] at shape
    have formed := access_reference_valid _ _ _ _ _ (read_access (shape index value found))
    have moved : { base with offset := base.offset + index * view.width } =
        base.element width index := by
      simp [Reference.element, contents.elementWidth, Nat.mul_comm]
    refine ⟨base.element width index, ?_, shape.load scalar found⟩
    simp [SpanView.element, valid, inside, address, moved, formed, Bind.bind, Except.bind]

/-- The first element of a valid nonempty view is addressable and loads as its scalar value. -/
theorem head {value : BitVec (8 * width)} {rest : List (BitVec (8 * width))}
    (contents : SpanContents memory view width (value :: rest))
    (valid : view.validate memory = .ok ()) (scalar : ScalarWidth width) :
    ∃ reference, view.element memory 0 = .ok reference ∧
      loadValue memory (.address reference) width = .ok (numericOfWidth width value.toNat) :=
  contents.load valid scalar rfl

/-- Slicing off the first `count` elements yields a valid view, with the same width and mode,
    that holds the remaining elements. -/
theorem drop {values : List (BitVec (8 * width))} (contents : SpanContents memory view width values)
    (valid : view.validate memory = .ok ()) (count : Nat) (inside : count ≤ values.length) :
    ∃ sliced, view.slice memory count (view.length - count) = .ok sliced ∧
      sliced.validate memory = .ok () ∧ sliced.writable = view.writable ∧
      SpanContents memory sliced width (values.drop count) := by
  obtain ⟨sliced, slicedOK, length, sameWidth, sameMode⟩ :=
    view.slice_succeeds memory count (view.length - count) valid (by rw [contents.length]; omega)
  refine ⟨sliced, slicedOK, view.slice_valid sliced memory _ _ slicedOK, sameMode,
    sameWidth.trans contents.elementWidth, by simp [length, contents.length], ?_⟩
  have shape := contents.contents
  cases address : view.reference with
  | null =>
    simp only [address] at shape
    subst shape
    rw [List.drop_nil]
    split <;> first | rfl | exact Contents.nil
  | address base =>
    simp only [address] at shape
    rw [view.slice_reference sliced memory count _ base address slicedOK]
    simpa [Reference.element, contents.elementWidth, Nat.mul_comm] using shape.drop count

/-- Slicing off the first element of a valid nonempty view yields a valid view, with the same
    width and mode, that holds the remaining elements. -/
theorem tail {value : BitVec (8 * width)} {rest : List (BitVec (8 * width))}
    (contents : SpanContents memory view width (value :: rest))
    (valid : view.validate memory = .ok ()) :
    ∃ sliced, view.slice memory 1 (view.length - 1) = .ok sliced ∧
      sliced.validate memory = .ok () ∧ sliced.writable = view.writable ∧
      SpanContents memory sliced width rest :=
  contents.drop valid 1 (by simp)

end SpanContents

#print axioms SpanContents.nil
#print axioms SpanContents.load
#print axioms SpanContents.head
#print axioms SpanContents.drop
#print axioms SpanContents.tail

end CIL.Safety
