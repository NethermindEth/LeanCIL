import CIL.Safety.LoopCallerFacts

/-!
# Writing through a span in a loop

A loop that stores `view[0]` and continues with `view.Slice(1)` writes caller storage through
a writable span. `SpanWritable` is the authority that takes: write access to every element of
the view, and the view's bytes inside the footprint the method may write. It is stated in the
caller's memory and survives slicing (`SpanWritable.slice`) and every frame memory
(`SpanWritable.within`), so a loop state carries it once, in `WritableSuffix`.
`LoopFrame.write_span_head` performs the store of the first element and keeps the frame facts.
-/

namespace CIL.Safety

/-- Write authority over every element of `view` in `memory`, with the view's bytes inside an
    entry of `footprint`, the caller storage the method may write. A null view has no
    elements. -/
structure SpanWritable (memory : Memory) (footprint : List (Reference × Nat)) (view : SpanView) :
    Prop where
  writable : ∀ base, view.reference = .address base →
    Writable memory base view.width 0 view.length
  inside : ∀ base, view.reference = .address base →
    ∃ entry ∈ footprint, Within (base, view.width * view.length) entry

/-- The caller storage a view addresses: its bytes, or nothing for a null view. -/
def SpanView.footprint (view : SpanView) : List (Reference × Nat) :=
  match view.reference with
  | .null => []
  | .address base => [(base, view.width * view.length)]

/-- Write authority over a view's elements makes it writable within its own footprint. -/
theorem SpanWritable.own {memory : Memory} {view : SpanView}
    (writable : ∀ base, view.reference = .address base →
      Writable memory base view.width 0 view.length) :
    SpanWritable memory view.footprint view :=
  ⟨writable, fun base address =>
    ⟨_, by simp [SpanView.footprint, address], Within.refl _⟩⟩

/-- A slice of a view keeps its authority, over the elements it still addresses. -/
theorem SpanWritable.slice {memory other : Memory} {footprint : List (Reference × Nat)}
    {view sliced : SpanView} {start length : Nat}
    (authority : SpanWritable memory footprint view)
    (cut : view.slice other start length = .ok sliced) :
    SpanWritable memory footprint sliced := by
  obtain ⟨fits, sameLength, sameWidth⟩ := SpanView.slice_shape cut
  have moved : ∀ outer, view.reference = .address outer → sliced.reference =
      .address (outer.element view.width start) := fun outer original => by
    rw [SpanView.slice_reference view sliced other start length outer original cut]
    simp [Reference.element, Nat.mul_comm]
  constructor
  · intro base address
    cases original : view.reference with
    | null =>
      rw [SpanView.slice_reference_null cut original] at address
      cases address
    | address outer =>
      rw [moved outer original] at address
      cases address
      rw [sameLength, sameWidth]
      exact (authority.writable outer original).sub (Nat.zero_le _) (by omega)
  · intro base address
    cases original : view.reference with
    | null =>
      rw [SpanView.slice_reference_null cut original] at address
      cases address
    | address outer =>
      rw [moved outer original] at address
      cases address
      obtain ⟨entry, member, inside⟩ := authority.inside outer original
      refine ⟨entry, member, Within.trans ?_ inside⟩
      rw [sameLength, sameWidth]
      simpa using outer.element_run_within view.width (first := start) (count := length)
        (outer := 0) (total := view.length) (Nat.zero_le _) (by omega)

/-- Authority stated in the caller's memory holds in every memory of a frame entered from it. -/
theorem SpanWritable.within {footprint written : List (Reference × Nat)} {caller current : Memory}
    {kinds : List CIL.LocalKind} {slots : List LocalSlot} {known : Nat → Option CIL.Value}
    {view : SpanView} (authority : SpanWritable caller footprint view)
    (wellFormed : caller.WellFormed) (frame : LoopFrame written caller current kinds slots known) :
    SpanWritable current footprint view :=
  ⟨fun base address => (authority.writable base address).after_confined frame.confined wellFormed,
    authority.inside⟩

/-- A valid writable view of `memory` with `count` elements of width `width`, and authority to
    write each of them within `footprint`: what a loop keeps about the suffix it has not
    written yet. Its bytes need not be readable or initialized. -/
structure WritableSpan (memory : Memory) (footprint : List (Reference × Nat)) (view : SpanView)
    (width count : Nat) : Prop where
  valid : view.validate memory = .ok ()
  mode : view.writable = true
  elementWidth : view.width = width
  length : view.length = count
  authority : SpanWritable memory footprint view

namespace WritableSpan

variable {memory : Memory} {footprint : List (Reference × Nat)} {view : SpanView}
  {width count : Nat}

/-- The view's own checks, as the stepper's span-local facts consume them. -/
theorem facts (span : WritableSpan memory footprint view width count) :
    view.validate memory = .ok () ∧ view.width = width ∧ view.writable = true :=
  ⟨span.valid, span.elementWidth, span.mode⟩

/-- An empty writable span has length zero, so a `Length != 0` guard fails. -/
theorem length_nil (span : WritableSpan memory footprint view width 0) :
    BitVec.ofNat 32 view.length = 0 := by
  rw [span.length]
  rfl

/-- A nonempty writable span passes the `Length != 0` guard and has a positive length. -/
theorem length_cons {rest : Nat} (span : WritableSpan memory footprint view width (rest + 1)) :
    BitVec.ofNat 32 view.length ≠ 0 ∧ 0 < view.length ∧ 1 ≤ view.length := by
  refine ⟨view.length_word_ne_zero memory span.valid ?_, ?_, ?_⟩ <;> simp [span.length]

/-- A writable span of well-formed caller memory keeps its validity, width and mode in every
    frame memory. -/
theorem valid_within {caller current : Memory} {kinds : List CIL.LocalKind}
    {slots : List LocalSlot} {known : Nat → Option CIL.Value} {written : List (Reference × Nat)}
    (span : WritableSpan caller footprint view width count) (wellFormed : caller.WellFormed)
    (frame : LoopFrame written caller current kinds slots known) :
    view.validate current = .ok () ∧ view.width = width ∧ view.writable = true :=
  ⟨frame.caller_valid wellFormed span.valid, span.elementWidth, span.mode⟩

/-- `Slice(1)` of a nonempty writable span is a writable span of the remaining elements. -/
theorem tail {rest : Nat} (span : WritableSpan memory footprint view width (rest + 1)) :
    ∃ sliced, view.slice memory 1 (view.length - 1) = .ok sliced ∧
      WritableSpan memory footprint sliced width rest := by
  obtain ⟨sliced, cut, length, sameWidth, sameMode⟩ :=
    view.slice_succeeds memory 1 (view.length - 1) span.valid (by rw [span.length]; omega)
  refine ⟨sliced, cut, view.slice_valid sliced memory _ _ cut, sameMode.trans span.mode,
    sameWidth.trans span.elementWidth, by rw [length, span.length]; rfl,
    span.authority.slice cut⟩

/-- An addressed nonempty writable span's first element is its own address. -/
theorem element_head {rest : Nat} (span : WritableSpan memory footprint view width (rest + 1)) :
    ∃ base, view.reference = .address base ∧ view.element memory 0 = .ok base ∧
      Writable memory base width 0 (rest + 1) := by
  have nonempty : 0 < view.length := by simp [span.length]
  cases address : view.reference with
  | null =>
    have valid := span.valid
    simp only [SpanView.validate, address, span.length] at valid
    repeat' first
      | contradiction
      | split at valid
      | simp_all [Bind.bind, Except.bind, Pure.pure, Except.pure]
  | address base =>
    have writable := span.authority.writable base address
    rw [span.elementWidth, span.length] at writable
    have formed := access_reference_valid _ _ _ _ _ (by simpa using writable 0 (by omega))
    refine ⟨base, rfl, ?_, writable⟩
    simp [SpanView.element, span.valid, nonempty, address, formed, Bind.bind, Except.bind]

end WritableSpan

/-- Storing `x` into the first element of a nonempty writable span of caller memory succeeds in
    any frame memory whose footprint holds the span, and keeps the frame facts. The element is
    the view's own address. -/
theorem LoopFrame.write_span_head {footprint : List (Reference × Nat)} {caller current : Memory}
    {kinds : List CIL.LocalKind} {slots : List LocalSlot} {known : Nat → Option CIL.Value}
    {view : SpanView} {width rest : Nat}
    (frame : LoopFrame footprint caller current kinds slots known) (wellFormed : caller.WellFormed)
    (span : WritableSpan caller footprint view width (rest + 1)) (x : BitVec (8 * width)) :
    ∃ item after, view.reference = .address item ∧ view.element current 0 = .ok item ∧
      CIL.Safety.write current item (numberBytes x.toNat width) 1 = .ok after ∧
      LoopFrame footprint caller after kinds slots known := by
  obtain ⟨base, address, found, writable⟩ := span.element_head
  have now : access current base width 1 true = .ok () := by
    simpa using (writable.after_confined frame.confined wellFormed) 0 (by omega)
  obtain ⟨after, written⟩ := write_succeeds (bytes := numberBytes x.toNat width)
    (by simpa [numberBytes_length] using now)
  obtain ⟨entry, member, inside⟩ := span.authority.inside base address
  refine ⟨base, after, address, frame.caller_element wellFormed found, written,
    frame.write written ⟨entry, member, Within.trans ?_ inside⟩
      (SpanView.allocation_below span.valid wellFormed address)⟩
  rw [span.elementWidth, span.length]
  simpa [numberBytes_length] using base.element_run_within width (first := 0) (count := 1)
    (outer := 0) (total := rest + 1) (Nat.le_refl _) (by omega)

/-- The state of a loop that writes a span from the front: the remaining view, its length, and
    its checks and authority in `memory`. -/
structure WritableSuffix (memory : Memory) (footprint : List (Reference × Nat)) (width : Nat) where
  view : SpanView
  remaining : Nat
  checked : WritableSpan memory footprint view width remaining

#print axioms SpanView.footprint
#print axioms SpanWritable.own
#print axioms SpanWritable.slice
#print axioms SpanWritable.within
#print axioms WritableSpan.facts
#print axioms WritableSpan.length_nil
#print axioms WritableSpan.length_cons
#print axioms WritableSpan.valid_within
#print axioms WritableSpan.tail
#print axioms WritableSpan.element_head
#print axioms LoopFrame.write_span_head

end CIL.Safety