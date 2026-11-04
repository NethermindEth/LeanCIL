import CIL.Safety.LoopFrames
import CIL.Safety.SpanContents

/-!
# Caller facts in loop frames

A loop frame entered from caller memory changes that memory only inside its footprint and keeps
every allocation the caller made (`LoopFrame.confined`). A fact about caller storage that reads
only allocations therefore holds in every frame memory: a formed reference
(`LoopFrame.caller_form`), an `Unsafe.Add` result (`LoopFrame.caller_add`), a span's validity,
element and slice (`LoopFrame.caller_valid`, `LoopFrame.caller_element`,
`LoopFrame.caller_slice`) and a checked span's own checks (`CheckedSpan.valid_within`). A span's
contents also hold there when the span lies apart from the footprint (`SpanApart`,
`CheckedSpan.within`). The loop tactics of `CIL.Safety.LoopFrameSteps` derive these facts at the
memories they name themselves, so a proof states them once, at the caller's memory.
-/

namespace CIL.Safety

/-- An addressed view's bytes share none with `entry`; a null view has no bytes. -/
def SpanApart (view : SpanView) (entry : Reference × Nat) : Prop :=
  ∀ base, view.reference = .address base → Apart base (view.width * view.length) entry

/-- Proves `∀ entry ∈ footprint, SpanApart view entry` for a literal footprint from a
    `SpanApart view entry` hypothesis per entry; the empty footprint needs none. -/
macro "cil_span_apart" : tactic =>
  `(tactic| ((simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]) <;> (try and_intros) <;> assumption))

/-- A reference forms exactly when its allocation's descriptor says so, whatever else memory
    holds. -/
theorem form_congr {before after : Memory} {reference : Reference}
    (same : after.allocations reference.allocation = before.allocations reference.allocation) :
    form after reference = form before reference := by
  simp only [form, liveAllocation, same]

/-- A reference reached by `Unsafe.Add` forms. -/
theorem add_formed {memory : Memory} {base result : Reference} {width : Nat}
    {offset : BitVec 64} (added : add memory base width offset = .ok result) :
    form memory result = .ok result := by
  unfold add at added
  cases first : form memory base with
  | error fault => simp [first, Bind.bind, Except.bind] at added
  | ok _ =>
    simp only [first, Bind.bind, Except.bind] at added
    have same := form_returns_input _ _ _ added
    subst same
    exact added

/-- A view's validity, elements and slices depend on memory only through the descriptor of the
    allocation it addresses. -/
theorem SpanView.memory_congr {view : SpanView} {before after : Memory}
    (same : ∀ base, view.reference = .address base →
      after.allocations base.allocation = before.allocations base.allocation) :
    view.validate after = view.validate before ∧
      (∀ index, view.element after index = view.element before index) ∧
      ∀ start length, view.slice after start length = view.slice before start length := by
  cases address : view.reference with
  | null =>
    refine ⟨?_, fun index => ?_, fun start length => ?_⟩ <;>
      simp only [SpanView.validate, SpanView.element, SpanView.slice, address]
  | address base =>
    have kept := same base address
    refine ⟨?_, fun index => ?_, fun start length => ?_⟩
    · simp only [SpanView.validate, address, liveAllocation, kept]
    · simp only [SpanView.element, SpanView.validate, address, form, liveAllocation, kept]
    · simp only [SpanView.slice, SpanView.validate, address, liveAllocation, kept]

#print axioms SpanApart
#print axioms form_congr
#print axioms add_formed
#print axioms SpanView.memory_congr

variable {footprint : List (Reference × Nat)} {caller current : Memory}
  {kinds : List CIL.LocalKind} {slots : List LocalSlot} {known : Nat → Option CIL.Value}

/-- Frame memory keeps every allocation the caller made. -/
theorem LoopFrame.extension (frame : LoopFrame footprint caller current kinds slots known) :
    AllocationExtension caller current :=
  ⟨frame.confined.grows, frame.confined.allocations⟩

/-- A reference formed in the caller's memory forms in frame memory. -/
theorem LoopFrame.caller_form (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {base : Reference}
    (valid : CIL.Safety.form caller base = .ok base) :
    CIL.Safety.form current base = .ok base :=
  frame.form valid (wellFormed.form_bound valid)

/-- An `Unsafe.Add` the caller's memory takes gives the same reference in frame memory. -/
theorem LoopFrame.caller_add (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {base result : Reference} {width : Nat}
    {offset : BitVec 64} (added : add caller base width offset = .ok result) :
    add current base width offset = .ok result := by
  have valid : CIL.Safety.form caller base = .ok base := by
    unfold add at added
    cases first : CIL.Safety.form caller base with
    | error fault => simp [first, Bind.bind, Except.bind] at added
    | ok formed => rw [← form_returns_input _ _ _ first]
  have kept := frame.confined.allocations _ (wellFormed.form_bound valid)
  unfold add at added ⊢
  simp only [CIL.Safety.form, liveAllocation, kept] at added ⊢
  exact added

/-- The views of caller memory keep their validity, elements and slices in frame memory. -/
theorem LoopFrame.view_congr (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {view : SpanView} (valid : view.validate caller = .ok ()) :
    view.validate current = view.validate caller ∧
      (∀ index, view.element current index = view.element caller index) ∧
      ∀ start length, view.slice current start length = view.slice caller start length :=
  SpanView.memory_congr fun _ address =>
    frame.confined.allocations _ (SpanView.allocation_below valid wellFormed address)

/-- A view valid in the caller's memory is valid in frame memory. -/
theorem LoopFrame.caller_valid (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {view : SpanView} (valid : view.validate caller = .ok ()) :
    view.validate current = .ok () :=
  view.validate_preserved valid wellFormed frame.extension

/-- An element address of a caller view is the same address in frame memory. -/
theorem LoopFrame.caller_element (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {view : SpanView} {index : Nat} {item : Reference}
    (found : view.element caller index = .ok item) : view.element current index = .ok item := by
  have valid : view.validate caller = .ok () := by
    cases checked : view.validate caller with
    | error fault => simp [SpanView.element, checked, Bind.bind, Except.bind] at found
    | ok _ => rfl
  rw [(frame.view_congr wellFormed valid).2.1 index]
  exact found

/-- A slice of a caller view is the same view in frame memory. -/
theorem LoopFrame.caller_slice (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {view sliced : SpanView} {start length : Nat}
    (cut : view.slice caller start length = .ok sliced) :
    view.slice current start length = .ok sliced := by
  have valid : view.validate caller = .ok () := by
    cases checked : view.validate caller with
    | error fault => simp [SpanView.slice, checked, Bind.bind, Except.bind] at cut
    | ok _ => rfl
  rw [(frame.view_congr wellFormed valid).2.2 start length]
  exact cut

/-- A checked span of well-formed caller memory keeps its validity, width and mode in every
    frame memory, whatever the footprint. -/
theorem CheckedSpan.valid_within {view : SpanView} {width : Nat} {writable : Bool}
    {values : List (BitVec (8 * width))} (span : CheckedSpan caller view width writable values)
    (wellFormed : caller.WellFormed)
    (frame : LoopFrame footprint caller current kinds slots known) :
    view.validate current = .ok () ∧ view.width = width ∧ view.writable = writable :=
  ⟨frame.caller_valid wellFormed span.valid, span.contents.elementWidth, span.mode⟩

/-- A checked span of well-formed caller memory stays checked in the memory of a frame whose
    footprint it lies apart from, so a loop state keeps its span in caller memory and reads it in
    frame memory. The empty footprint needs no apartness. -/
theorem CheckedSpan.within {view : SpanView} {width : Nat} {writable : Bool}
    {values : List (BitVec (8 * width))} (span : CheckedSpan caller view width writable values)
    (wellFormed : caller.WellFormed) (frame : LoopFrame footprint caller current kinds slots known)
    (apart : ∀ entry ∈ footprint, SpanApart view entry := by cil_span_apart) :
    CheckedSpan current view width writable values := by
  refine ⟨frame.caller_valid wellFormed span.valid, span.mode, span.contents.elementWidth,
    span.contents.length, ?_⟩
  have held := span.contents.contents
  revert held
  cases reference : view.reference with
  | null => exact id
  | address base =>
    intro held
    refine held.after_confined frame.confined wellFormed fun entry member => ?_
    simpa [span.contents.length, span.contents.elementWidth] using
      apart entry member base reference

/-- A successful slice starts and ends inside its view and keeps the view's width. -/
theorem SpanView.slice_shape {view sliced : SpanView} {memory : Memory} {start length : Nat}
    (cut : view.slice memory start length = .ok sliced) :
    start + length ≤ view.length ∧ sliced.length = length ∧ sliced.width = view.width := by
  unfold SpanView.slice at cut
  cases valid : view.validate memory with
  | error fault => simp [valid, Bind.bind, Except.bind] at cut
  | ok _ =>
    simp only [valid, Bind.bind, Except.bind, Pure.pure, Except.pure] at cut
    split at cut
    · rename_i fits
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
      split at cut
      · contradiction
      · cases cut
        exact ⟨by omega, rfl, rfl⟩
    · contradiction

/-- Slicing a null view gives a null view. -/
theorem SpanView.slice_reference_null {view sliced : SpanView} {memory : Memory}
    {start length : Nat} (cut : view.slice memory start length = .ok sliced)
    (null : view.reference = .null) : sliced.reference = .null := by
  unfold SpanView.slice at cut
  simp only [null] at cut
  repeat' first
    | (cases cut; rfl)
    | (split at cut <;> try contradiction)
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at cut

/-- A slice of a view apart from `entry` is apart from it. -/
theorem SpanApart.slice {view sliced : SpanView} {entry : Reference × Nat} {memory : Memory}
    {start length : Nat} (apart : SpanApart view entry)
    (cut : view.slice memory start length = .ok sliced) : SpanApart sliced entry := by
  intro base address
  obtain ⟨fits, sameLength, sameWidth⟩ := SpanView.slice_shape cut
  cases original : view.reference with
  | null =>
    have := SpanView.slice_reference_null cut original
    rw [this] at address
    cases address
  | address outer =>
    rw [SpanView.slice_reference view sliced memory start length outer original cut] at address
    cases address
    rw [sameLength, sameWidth]
    have inside : start * view.width + view.width * length ≤ view.width * view.length := by
      rw [Nat.mul_comm start, ← Nat.mul_add]
      exact Nat.mul_le_mul_left _ fits
    exact (apart outer original).sub inside

/-- `Unsafe.Add` of an `int` index below `2^31` into a writable run addresses that element. -/
theorem Writable.add_int {memory : Memory} {base : Reference} {width start count : Nat}
    (writable : Writable memory base width start count) (wellFormed : memory.WellFormed)
    (valid : CIL.Safety.form memory base = .ok base) {index : CIL.W32}
    (small : index.toNat < 2 ^ 31) (low : start ≤ index.toNat)
    (high : index.toNat < start + count) :
    add memory base width (BitVec.ofInt 64 index.toInt) = .ok (base.element width index.toNat) :=
  add_int_element wellFormed valid small (by
    have held := writable (index.toNat - start) (by omega)
    rwa [show start + (index.toNat - start) = index.toNat by omega] at held)

#print axioms Writable.add_int
#print axioms LoopFrame.extension
#print axioms LoopFrame.caller_form
#print axioms LoopFrame.caller_add
#print axioms LoopFrame.view_congr
#print axioms LoopFrame.caller_valid
#print axioms LoopFrame.caller_element
#print axioms LoopFrame.caller_slice
#print axioms CheckedSpan.valid_within
#print axioms CheckedSpan.within
#print axioms SpanView.slice_shape
#print axioms SpanView.slice_reference_null
#print axioms SpanApart.slice

/-- Prove that a caller buffer, or an element of one, lies in an allocation below the caller's
    watermark, from a hypothesis or a `form` fact of the caller's well-formed memory. -/
macro "cil_caller_allocation" : tactic => `(tactic| first
  | ((try simp only [Reference.element_allocation])
     exact Memory.WellFormed.form_bound (by assumption) (by assumption))
  | assumption)

end CIL.Safety
