import Extracted
import CIL.Verification
import CIL.Safety.LoopScaffold
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

bind_cutpoint cutpoint (memory : Memory) (state : State memory) := Extracted.method0
  at loop.latch matching (fun op => match op with | .brnonzero _ => true | _ => false)
  with (entry.frame memory state.val state.property.1 state.property.2.1 state.property.2.2)

/-- The loop guard observes the current span length. -/
private def header (memory : Memory) (state : State memory) : LoopState :=
  cutpoint memory state [.scalar (.i32 (BitVec.ofNat 32 state.val.length))] memory

private theorem terminates (memory : Memory) (args : List Value) (state : State memory) :
    LoopTerminates Extracted.program 0 args
      (fun final values => final = memory ∧ values = [.scalar (.i32 0)])
      (header memory state) := by
  apply loop_terminates Extracted.program 0 args (header memory) (fun _ => True)
    (fun state => state.val.length) _ ?_ state trivial
  intro state _
  obtain ⟨view, valid, width, readOnly⟩ := state
  have loaded : loadLocal memory (.span 4 false (some view)) = .ok (.bufferSpan view) := by
    simp [loadLocal, width, readOnly, valid, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  by_cases empty : view.length = 0
  · left
    cil_loop_finish [staticInstruction, memoryInstruction, otherMemoryInstruction, header,
      cutpoint, entry.frame, width, readOnly, valid, Value.hasUnspecified, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, empty, loaded, leaveFrame]
  · right
    obtain ⟨sliced, slicedOK, length, sameWidth, sameMode⟩ :=
      view.slice_succeeds memory 1 (view.length - 1) valid (by omega)
    have formed := view.slice_valid sliced memory 1 (view.length - 1) slicedOK
    have loadedNext : loadLocal memory (.span 4 false (some sliced)) =
        .ok (.bufferSpan sliced) := by
      simp [loadLocal, sameWidth, sameMode, width, readOnly, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have stored : storeLocal memory (.span 4 false (some view)) (.bufferSpan sliced) =
        .ok (.span 4 false (some sliced), memory) := by
      simp [storeLocal, sameWidth, sameMode, width, readOnly, formed, checkedAt,
        Value.hasUnspecified, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    let next : State memory := ⟨sliced, formed, sameWidth.trans width, sameMode.trans readOnly⟩
    have nonzero : BitVec.ofNat 32 view.length ≠ 0 := by
      have bounded := view.length_bounded memory valid
      intro zero
      have := congrArg BitVec.toNat zero
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      exact empty this
    have path : LoopReaches Extracted.program 0 args
        (header memory ⟨view, valid, width, readOnly⟩) (header memory next) := by
      cil_loop_steps [staticInstruction, memoryInstruction, otherMemoryInstruction, header,
        cutpoint, entry.frame, width, readOnly, valid, Value.hasUnspecified, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, nonzero,
        slicedOK, formed, next, sameWidth, sameMode, loaded, loadedNext, stored,
        show 1 ≤ view.length by omega]
    obtain ⟨cost, segment⟩ := path
    exact ⟨next, cost, trivial, by dsimp [next]; omega, segment⟩
#print axioms terminates

/-- Every valid readonly integer span is consumed without changing any caller memory. -/
theorem drain (memory : Memory) (view : SpanView) (valid : view.validate memory = .ok ())
    (width : view.width = 4) (readOnly : view.writable = false) :
    ∃ fuel, invoke Extracted.program fuel 0 [.bufferSpan view] memory =
      .ok (memory, [.scalar (.i32 0)]) := by
  let state : State memory := ⟨view, valid, width, readOnly⟩
  have loaded : loadLocal memory (.span 4 false (some view)) = .ok (.bufferSpan view) := by
    simp [loadLocal, width, readOnly, valid, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have path : LoopReaches Extracted.program 0 [.bufferSpan view]
      ⟨0, entry.frame memory view valid width readOnly, [],
        entry.memory memory view valid width readOnly⟩ (header memory state) := by
    cil_loop_steps [header, cutpoint, state, entry.frame, entry.memory, entry.result,
      loaded, staticInstruction, memoryInstruction, otherMemoryInstruction, valid,
      Value.hasUnspecified, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  obtain ⟨fuel, final, values, executed, sameMemory, returned⟩ :=
    loop_reaches_terminates path (terminates memory [.bufferSpan view] state)
  subst final values
  refine ⟨fuel, invoke_of_run Extracted.lookup0 ?_
    (entry.checked memory view valid width readOnly) executed⟩
  simp [checkedValue, valid, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
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

