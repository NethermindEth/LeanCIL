import Extracted
import CIL.Verification
import CIL.Safety.LoopScaffold
import CIL.Safety.LoopVC
import CIL.Safety.SpanContents
import CIL.StructuralLabels

/-! An arbitrary-length readonly span loop computes a predicate over symbolic buffer contents. -/

open CIL.Safety
namespace ExampleProof

bind_entry entry (memory : Memory) (view : SpanView)
    (valid : view.validate memory = .ok ()) (width : view.width = 4)
    (readOnly : view.writable = false) := Extracted.method0
  with [.bufferSpan view] from memory
  simplifying [valid, width, readOnly]

bind_loop loop := Extracted.method0

-- The loop guard observes the remaining span length.
bind_cutpoint header (memory : Memory) (state : SpanSuffix memory 4 false) :=
  Extracted.method0 at loop.latch matching (fun op => match op with | .brnonzero _ => true | _ => false)
  with (entry.frame memory state.view state.checked.valid state.checked.elementWidth
    state.checked.mode), [.scalar (.i32 (BitVec.ofNat 32 state.view.length))], memory

/-- The compiled loop decides whether every mathematical element is zero, for any valid length. -/
theorem correctness (memory : Memory) (view : SpanView) (values : List CIL.W32)
    (valid : view.validate memory = .ok ()) (readOnly : view.writable = false)
    (contents : SpanContents memory view 4 values) :
    ∃ fuel, invoke Extracted.program fuel 0 [.bufferSpan view] memory =
      .ok (memory, [.scalar (.i32 (if values.all (· == 0) then 1 else 0))]) := by
  refine invoke_loop_returns Extracted.lookup0 (by simp [cil_checked, valid])
    (entry.checked memory view valid contents.elementWidth readOnly) (header memory)
    (fun state => state.values.all (· == 0) = values.all (· == 0)) (·.values.length)
    ⟨view, values, valid, readOnly, contents⟩ (by
      cil_loop_steps [header, entry.frame, entry.memory, entry.result, entry.load0,
        valid, contents.elementWidth, readOnly]) rfl ?_
  rintro ⟨view, remaining, span⟩ invariant
  cases remaining with
  | nil =>
    left
    cil_loop_finish [header, entry.frame, entry.load0, span.facts, span.length_nil,
      invariant.symm]
  | cons value remaining =>
    obtain ⟨item, guard, found, element⟩ := span.head (by decide)
    obtain ⟨sliced, slicedOK, next⟩ := span.tail
    by_cases zero : value = 0
    · cil_loop_continue ⟨sliced, remaining, next⟩ [header, entry.frame, entry.load0,
        entry.store0, span.facts, guard, found, element, numericOfWidth, BitVec.ofNat_toNat,
        zero, slicedOK, next.facts]
      · simpa [zero] using invariant
      · simp
    · left
      cil_loop_finish [header, entry.frame, entry.load0, span.facts, guard, found,
        element, numericOfWidth, BitVec.ofNat_toNat, zero, invariant.symm]
#print axioms correctness

end ExampleProof
