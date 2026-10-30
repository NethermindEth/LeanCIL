import Extracted
import CIL.Verification
import CIL.Safety.LoopScaffold
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

/-- A checked readonly suffix of the caller's symbolic buffer, in unchanged caller memory. -/
private structure State (memory : Memory) where
  view : SpanView
  values : List CIL.W32
  valid : view.validate memory = .ok ()
  readOnly : view.writable = false
  contents : SpanContents memory view 4 values

bind_cutpoint cutpoint (memory : Memory) (state : State memory) := Extracted.method0
  at loop.latch matching (fun op => match op with | .brnonzero _ => true | _ => false)
  with (entry.frame memory state.view state.valid state.contents.elementWidth state.readOnly)

/-- The loop guard observes the remaining span length. -/
private def header (memory : Memory) (state : State memory) : LoopState :=
  cutpoint memory state [.scalar (.i32 (BitVec.ofNat 32 state.view.length))] memory

/-- From any suffix whose predicate is `result`, the loop returns `result` and changes nothing. -/
private theorem terminates (memory : Memory) (args : List Value) (result : Bool)
    (state : State memory) (invariant : state.values.all (· == 0) = result) :
    LoopTerminates Extracted.program 0 args
      (fun final values => final = memory ∧ values = [.scalar (.i32 (if result then 1 else 0))])
      (header memory state) := by
  apply loop_terminates Extracted.program 0 args (header memory)
    (fun state => state.values.all (· == 0) = result) (fun state => state.values.length)
    _ ?_ state invariant
  rintro ⟨view, values, valid, readOnly, contents⟩ invariant
  have width := contents.elementWidth
  cases values with
  | nil =>
    obtain rfl : true = result := invariant
    left
    cil_loop_finish [header, cutpoint, entry.frame, entry.load0, width, readOnly, valid,
      contents.length, leaveFrame, CIL.NarrowKind.extend, ite_true]
  | cons value remaining =>
    obtain ⟨item, found, element⟩ := contents.head valid (by decide)
    obtain ⟨sliced, slicedOK, validNext, sameMode, nextContents⟩ := contents.tail valid
    have nonzero := view.length_word_ne_zero memory valid (by simp [contents.length])
    have facts : 0 < view.length ∧ 1 ≤ view.length := by simp [contents.length]
    by_cases zero : value = 0
    · right
      let next : State memory :=
        ⟨sliced, remaining, validNext, sameMode.trans readOnly, nextContents⟩
      obtain ⟨cost, segment⟩ : LoopReaches Extracted.program 0 args
          (header memory ⟨view, value :: remaining, valid, readOnly, contents⟩)
          (header memory next) := by
        cil_loop_steps [header, cutpoint, entry.frame, entry.load0, entry.store0, width,
          readOnly, valid, nonzero, slicedOK, validNext, next, nextContents.elementWidth,
          sameMode, found, element, numericOfWidth, BitVec.ofNat_toNat, zero, facts]
      exact ⟨next, cost, by simpa [zero] using invariant, by simp [next], segment⟩
    · obtain rfl : false = result := by
        simpa only [List.all_cons, beq_eq_false_iff_ne.mpr zero, Bool.false_and] using invariant
      left
      cil_loop_finish [header, cutpoint, entry.frame, entry.load0, width, readOnly, valid,
        nonzero, found, element, numericOfWidth, BitVec.ofNat_toNat, zero, facts, leaveFrame,
        CIL.NarrowKind.extend, Bool.false_eq_true, ite_false]
#print axioms terminates

/-- The compiled loop decides whether every mathematical element is zero, for any valid length. -/
theorem correctness (memory : Memory) (view : SpanView) (values : List CIL.W32)
    (valid : view.validate memory = .ok ()) (readOnly : view.writable = false)
    (contents : SpanContents memory view 4 values) :
    ∃ fuel, invoke Extracted.program fuel 0 [.bufferSpan view] memory =
      .ok (memory, [.scalar (.i32 (if values.all (· == 0) then 1 else 0))]) := by
  have width := contents.elementWidth
  let state : State memory := ⟨view, values, valid, readOnly, contents⟩
  have path : LoopReaches Extracted.program 0 [.bufferSpan view]
      ⟨0, entry.frame memory view valid width readOnly, [],
        entry.memory memory view valid width readOnly⟩ (header memory state) := by
    cil_loop_steps [header, cutpoint, state, entry.frame, entry.memory, entry.result,
      entry.load0, valid, width, readOnly]
  obtain ⟨fuel, final, returned, executed, sameMemory, sameValues⟩ :=
    loop_reaches_terminates path (terminates memory [.bufferSpan view] _ state rfl)
  subst final returned
  refine ⟨fuel, invoke_of_run Extracted.lookup0 ?_
    (entry.checked memory view valid width readOnly) executed⟩
  simp [cil_checked, valid]
#print axioms correctness

end ExampleProof
