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

/-- An addressed view valid in well-formed memory names an allocation below its watermark. -/
theorem SpanView.allocation_below {view : SpanView} {memory : Memory} {base : Reference}
    (valid : view.validate memory = .ok ()) (wellFormed : memory.WellFormed)
    (address : view.reference = .address base) : base.allocation < memory.nextIdentity := by
  cases present : memory.allocations base.allocation with
  | none =>
    simp only [SpanView.validate, address, liveAllocation, present] at valid
    repeat' first
      | contradiction
      | split at valid
      | simp_all [Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some allocation => exact (wellFormed.1 _ _ present).1
#print axioms SpanView.allocation_below

/-- Validity of a view of caller memory `anchor` is unchanged by anything that keeps the memory
    below `anchor`'s watermark, even between later memories such as a callee's result and the
    caller's frame exit. -/
theorem SpanView.validate_eq_below {view : SpanView} {anchor before after : Memory}
    (valid : view.validate anchor = .ok ()) (wellFormed : anchor.WellFormed)
    (kept : MemoryBelow anchor.nextIdentity before after) :
    view.validate after = view.validate before := by
  cases address : view.reference with
  | null => simp only [SpanView.validate, address]
  | address base =>
    simp only [SpanView.validate, address, liveAllocation,
      kept.allocations _ (SpanView.allocation_below valid wellFormed address)]
#print axioms SpanView.validate_eq_below

/-- A successful slice of well-formed memory succeeds identically in any memory that keeps
    everything below the watermark. -/
theorem SpanView.slice_below (view result : SpanView) {before after : Memory}
    (start length : Nat) (sliced : view.slice before start length = .ok result)
    (wellFormed : before.WellFormed) (kept : MemoryBelow before.nextIdentity before after) :
    view.slice after start length = .ok result := by
  have valid : view.validate before = .ok () := by
    cases formed : view.validate before with
    | error fault =>
      simp [SpanView.slice, formed, Bind.bind, Except.bind] at sliced
    | ok _ => rfl
  unfold SpanView.slice at sliced ⊢
  rw [view.validate_below valid wellFormed kept]
  rw [valid] at sliced
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at sliced ⊢
  split at sliced
  · rename_i bounds
    simp only [bounds, ite_true]
    split at sliced
    · contradiction
    · rename_i formed
      rw [SpanView.validate_below _ formed wellFormed kept]
      exact sliced
  · contradiction
#print axioms SpanView.slice_below

namespace SpanContents

variable {memory : Memory} {view : SpanView} {width : Nat}

/-- Every zero-length view of the element width holds the empty list, null or addressed. -/
theorem nil (sameWidth : view.width = width) (empty : view.length = 0) :
    SpanContents memory view width [] :=
  ⟨sameWidth, empty, by split <;> first | rfl | exact Contents.nil⟩

/-- Element `index` of a valid view is addressable and loads as the element's scalar value. -/
theorem load {values : List (BitVec (8 * width))}
    (contents : SpanContents memory view width values)
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
theorem drop {values : List (BitVec (8 * width))}
    (contents : SpanContents memory view width values)
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

/-- The contents of a view of well-formed memory survive any change that keeps everything below
    the watermark, such as callee frame entry, local stores and frame exit. -/
theorem after_below {before after : Memory} {values : List (BitVec (8 * width))}
    (contents : SpanContents before view width values) (wellFormed : before.WellFormed)
    (kept : MemoryBelow before.nextIdentity before after) :
    SpanContents after view width values := by
  refine ⟨contents.elementWidth, contents.length, ?_⟩
  have shape := contents.contents
  cases address : view.reference with
  | null => simpa only [address] using shape
  | address base =>
    simp only [address] at shape ⊢
    cases values with
    | nil => exact Contents.nil
    | cons value rest =>
      have formed := access_reference_valid _ _ _ _ _ (read_access (shape 0 value rfl))
      obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ formed
      exact shape.after_below kept (by simpa using (wellFormed.1 _ _ present).1)

/-- Contents of a view valid in caller memory `anchor` survive anything that keeps the memory
    below `anchor`'s watermark, so contents a callee leaves in caller storage reach the caller's
    final memory through the caller's own frame exit. -/
theorem after_below_valid {anchor before after : Memory} {values : List (BitVec (8 * width))}
    (contents : SpanContents before view width values) (valid : view.validate anchor = .ok ())
    (wellFormed : anchor.WellFormed) (kept : MemoryBelow anchor.nextIdentity before after) :
    SpanContents after view width values := by
  refine ⟨contents.elementWidth, contents.length, ?_⟩
  have shape := contents.contents
  cases address : view.reference with
  | null => simpa only [address] using shape
  | address base =>
    simp only [address] at shape ⊢
    exact shape.after_below kept (SpanView.allocation_below valid wellFormed address)

end SpanContents

#print axioms SpanContents.nil
#print axioms SpanContents.load
#print axioms SpanContents.head
#print axioms SpanContents.drop
#print axioms SpanContents.tail
#print axioms SpanContents.after_below
#print axioms SpanContents.after_below_valid

end CIL.Safety
