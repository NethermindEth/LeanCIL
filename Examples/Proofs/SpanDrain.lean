import Extracted
import CIL.Verification
import CIL.Safety.LoopScaffold
import CIL.Safety.LoopVC
import CIL.Safety.SpanSliceProgress
import CIL.StructuralLabels

/-! A span loop over arbitrary caller storage, including an assigned parameter home. -/

open CIL.Safety
namespace ExampleProof

bind_entry entry (memory : Memory) (view : SpanView)
    (valid : view.validate memory = .ok ()) (width : view.width = 4)
    (readOnly : view.writable = false) := Extracted.method0
  with [.bufferSpan view] from memory
  simplifying [valid, width, readOnly]

bind_loop loop := Extracted.method0

/-- A checked readonly integer view in the unchanged caller memory. -/
private def State (memory : Memory) :=
  { view : SpanView // view.validate memory = .ok () ∧ view.width = 4 ∧ view.writable = false }

-- The loop guard observes the current span length.
bind_cutpoint header (memory : Memory) (state : State memory) := Extracted.method0
  at loop.latch matching (fun op => match op with | .brnonzero _ => true | _ => false)
  with (entry.frame memory state.val state.property.1 state.property.2.1 state.property.2.2),
    [.scalar (.i32 (BitVec.ofNat 32 state.val.length))], memory

/-- Every valid readonly integer span is consumed without changing any caller memory. -/
theorem drain (memory : Memory) (view : SpanView) (valid : view.validate memory = .ok ())
    (width : view.width = 4) (readOnly : view.writable = false) :
    ∃ fuel, invoke Extracted.program fuel 0 [.bufferSpan view] memory =
      .ok (memory, [.scalar (.i32 0)]) := by
  refine invoke_loop_returns Extracted.lookup0 (by simp [cil_checked, valid])
    (entry.checked memory view valid width readOnly) (header memory) (fun _ => True)
    (·.val.length) ⟨view, valid, width, readOnly⟩ (by
      cil_loop_steps [header, entry.frame, entry.memory, entry.result, entry.load0, valid, width,
        readOnly]) trivial ?_
  rintro ⟨view, valid, width, readOnly⟩ -
  by_cases empty : view.length = 0
  · left
    cil_loop_finish [header, entry.frame, entry.load0, width, readOnly, valid, empty]
  · obtain ⟨sliced, slicedOK, length, sameWidth, sameMode⟩ :=
      view.slice_succeeds memory 1 (view.length - 1) valid (by omega)
    have formed := view.slice_valid sliced memory 1 (view.length - 1) slicedOK
    cil_loop_continue ⟨sliced, formed, sameWidth.trans width, sameMode.trans readOnly⟩
      [header, entry.frame, entry.load0, entry.store0, width, readOnly, valid,
        view.length_word_ne_zero memory valid empty, slicedOK, formed, sameWidth, sameMode,
        show 1 ≤ view.length by omega]
    · trivial
    · dsimp only; omega
#print axioms drain

/-- The compiled method returns zero for every valid span, with exact memory preservation. -/
theorem correctness : Ensures Extracted.program 0
    (fun args initial => ∃ view : SpanView, args = [.bufferSpan view] ∧
      view.validate initial = .ok () ∧ view.width = 4 ∧ view.writable = false)
    (fun _ initial final values => final = initial ∧ values = [.scalar (.i32 0)]) := by
  rintro args initial ⟨view, rfl, valid, width, readOnly⟩
  obtain ⟨fuel, executed⟩ := drain initial view valid width readOnly
  exact ⟨fuel, initial, [.scalar (.i32 0)], executed, rfl, rfl⟩
#print axioms correctness

end ExampleProof
