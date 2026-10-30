import Extracted
import CIL.Verification
import CIL.Safety.BufferContents
import CIL.Safety.LoopScaffold
import CIL.Safety.SpanSliceProgress
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

/-- The mathematical contents of a readonly uint span, including null empty views. -/
def SpanContents (memory : Memory) (view : SpanView) (values : List CIL.W32) : Prop :=
  view.length = values.length ∧ match view.reference with
    | .null => values = []
    | .address base => Contents memory base 4 values

/-- A suffix of the original symbolic buffer in unchanged caller memory. -/
private structure State (memory : Memory) where
  view : SpanView
  values : List CIL.W32
  valid : view.validate memory = .ok ()
  width : view.width = 4
  readOnly : view.writable = false
  contents : SpanContents memory view values

bind_cutpoint cutpoint (memory : Memory) (state : State memory) := Extracted.method0
  at loop.latch matching (fun op => match op with | .brnonzero _ => true | _ => false)
  with (entry.frame memory state.view state.valid state.width state.readOnly)

/-- The loop guard observes the remaining span length. -/
private def header (memory : Memory) (state : State memory) : LoopState :=
  cutpoint memory state [.scalar (.i32 (BitVec.ofNat 32 state.view.length))] memory

/-- Every finite suffix returns its all-zero predicate without modifying memory. -/
private theorem terminates (memory : Memory) (args : List Value) (result : Bool)
    (state : State memory) (invariant : state.values.all (· == 0) = result) :
    LoopTerminates Extracted.program 0 args
      (fun final values => final = memory ∧ values = [.scalar (.i32 (if result then 1 else 0))])
      (header memory state) := by
  apply loop_terminates Extracted.program 0 args (header memory)
    (fun state => state.values.all (· == 0) = result) (fun state => state.values.length)
    _ ?_ state invariant
  intro state invariant
  obtain ⟨view, values, valid, width, readOnly, length, contents⟩ := state
  cases values with
  | nil =>
    have empty : view.length = 0 := length
    have outcome : result = true := by simpa using invariant.symm
    left
    cil_loop_finish [header, cutpoint, entry.frame, entry.load0, width, readOnly, valid,
      empty, leaveFrame, outcome, CIL.NarrowKind.extend, ite_true]
  | cons value remaining =>
    obtain ⟨base, address, contents⟩ : ∃ base, view.reference = .address base ∧
        Contents memory base 4 (value :: remaining) := by
      cases address : view.reference with
      | null => simp [address] at contents
      | address base => exact ⟨base, rfl, by simpa [address] using contents⟩
    have headRead := contents 0 value rfl
    simp only [Reference.element, Nat.mul_zero, Nat.add_zero] at headRead
    have formed := access_reference_valid _ _ _ _ _ (read_access headRead)
    have item : view.element memory 0 = .ok base := by
      simp [SpanView.element, valid, length, address, formed, Bind.bind, Except.bind]
    have element : loadValue memory (.address base) 4 = .ok (.i32 value) := by
      simpa [Reference.element, numericOfWidth, BitVec.ofNat_toNat] using
        (contents.load (by decide) (index := 0) (x := value) rfl)
    have nonzero : BitVec.ofNat 32 view.length ≠ 0 := by
      have bounded := view.length_bounded memory valid
      intro zero
      have := congrArg BitVec.toNat zero
      change view.length % 2^32 = 0 at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simp only [List.length_cons] at length
      omega
    by_cases zero : value = 0
    · right
      obtain ⟨sliced, slicedOK, nextLength, sameWidth, sameMode⟩ :=
        view.slice_succeeds memory 1 (view.length - 1) valid
          (by simp only [List.length_cons] at length; omega)
      have validNext := view.slice_valid sliced memory 1 (view.length - 1) slicedOK
      have reference :=
        view.slice_reference sliced memory 1 (view.length - 1) base address slicedOK
      have nextContents : SpanContents memory sliced remaining := by
        constructor
        · simpa [length] using nextLength
        · simpa [reference, width, Reference.element] using contents.drop 1
      let next : State memory :=
        ⟨sliced, remaining, validNext, sameWidth.trans width,
          sameMode.trans readOnly, nextContents⟩
      have path : LoopReaches Extracted.program 0 args
          (header memory ⟨view, value :: remaining, valid, width, readOnly, length,
            by simpa [address] using contents⟩)
          (header memory next) := by
        cil_loop_steps [header, cutpoint, entry.frame, entry.load0, entry.store0,
          width, readOnly, valid, nonzero, slicedOK, validNext, next, sameWidth, sameMode,
          item, element, zero, show 0 < view.length by simp [length],
          show 1 ≤ view.length by simp [length]]
      obtain ⟨cost, segment⟩ := path
      exact ⟨next, cost, by simpa [next, zero] using invariant,
        by simp [next], segment⟩
    · have test : (value == 0) = false := beq_eq_false_iff_ne.mpr zero
      have outcome : result = false := by
        change ((value :: remaining).all (· == 0)) = result at invariant
        simp only [List.all_cons, test, Bool.false_and] at invariant
        exact invariant.symm
      left
      cil_loop_finish [header, cutpoint, entry.frame, entry.load0, width, readOnly, valid,
        nonzero, item, element, zero, show 0 < view.length by simp [length], leaveFrame,
        outcome, CIL.NarrowKind.extend, Bool.false_eq_true, ite_false]
#print axioms terminates

/-- The compiled loop decides whether every mathematical element is zero, for any valid length. -/
theorem correctness (memory : Memory) (view : SpanView) (values : List CIL.W32)
    (valid : view.validate memory = .ok ()) (width : view.width = 4)
    (readOnly : view.writable = false) (contents : SpanContents memory view values) :
    ∃ fuel, invoke Extracted.program fuel 0 [.bufferSpan view] memory =
      .ok (memory, [.scalar (.i32 (if values.all (· == 0) then 1 else 0))]) := by
  let state : State memory := ⟨view, values, valid, width, readOnly, contents⟩
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


