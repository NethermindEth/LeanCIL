import Extracted
import CIL.Verification
import CIL.Safety.LoopScaffold
import CIL.Safety.LoopVC
import CIL.Safety.ReturnMemory
import CIL.Safety.SpanContents
import CIL.StructuralLabels

/-! A readonly span fold returns the wrapping sum of arbitrary-length symbolic contents. -/

open CIL.Safety
open CIL (W64)
namespace ExampleProof

bind_entry entry (memory : Memory) (view : SpanView) (wellFormed : memory.WellFormed)
    (valid : view.validate memory = .ok ()) (width : view.width = 8)
    (readOnly : view.writable = false) := Extracted.method0
  with [.bufferSpan view] from memory allocating wellFormed
  simplifying [valid, width, readOnly]

bind_loop loop := Extracted.method0

/-- A suffix of the caller's buffer, the total of the consumed prefix, and frame memory that
    keeps the caller's memory. -/
private structure State (memory : Memory) (home : Reference) where
  view : SpanView
  values : List W64
  total : W64
  current : Memory
  valid : view.validate memory = .ok ()
  readOnly : view.writable = false
  contents : SpanContents memory view 8 values
  kept : MemoryBelow memory.nextIdentity memory current
  loaded : loadLocal current (.bytes .word64 home) = .ok (.scalar (.i64 total))
  writable : access current home 8 1 true = .ok ()

bind_cutpoint cutpoint (memory : Memory) (home : Reference) (state : State memory home) :=
  Extracted.method0 at loop.latch matching
    (fun op => match op with | .brnonzero _ => true | _ => false)
  with (entry.frame memory state.view home)

/-- The loop guard observes the remaining span length. -/
private def header (memory : Memory) (home : Reference) (state : State memory home) : LoopState :=
  cutpoint memory home state [.scalar (.i32 (BitVec.ofNat 32 state.view.length))] state.current

/-- From any suffix whose total plus remaining sum is `result`, the loop returns `result`. -/
private theorem terminates (memory : Memory) (home : Reference) (args : List Value)
    (result : W64) (wellFormed : memory.WellFormed) (fresh : memory.nextIdentity ≤ home.allocation)
    (state : State memory home) (invariant : state.total + state.values.sum = result) :
    LoopTerminates Extracted.program 0 args
      (fun final values => MemoryBelow memory.nextIdentity memory final ∧
        values = [.scalar (.i64 result)])
      (header memory home state) := by
  apply loop_terminates Extracted.program 0 args (header memory home)
    (fun state => state.total + state.values.sum = result) (fun state => state.values.length)
    _ ?_ state invariant
  rintro ⟨view, values, total, current, valid, readOnly, contents, kept, loaded, writable⟩
    invariant
  have width := contents.elementWidth
  have validHere := view.validate_below valid wellFormed kept
  have exit := kept.trans (leaveFrame_preserves_memory_below (entry.frame memory view home)
    current _ fun id member => by simp_all [entry.frame])
  cases values with
  | nil =>
    obtain rfl : total = result := by simpa using invariant
    left
    cil_loop_finish [header, cutpoint, entry.frame, width, readOnly, validHere, loaded,
      contents.length, exit]
    exact loop_terminates_return (op := .ret _) (by rfl) (by rfl) (by cil_checked_step []) rfl
      ⟨exit, rfl⟩
  | cons value remaining =>
    right
    have here := contents.after_below wellFormed kept
    obtain ⟨item, found, element⟩ := here.head validHere (by decide)
    have nonzero := view.length_word_ne_zero memory valid (by simp [contents.length])
    have facts : 0 < view.length ∧ 1 ≤ view.length := by simp [contents.length]
    cil_store_vc updated stored nextLoaded nextWritable := .word64 (.i64 (total + value))
      using writable
    have nextKept := kept.trans
      (store_numeric_local_preserves_memory_below _ _ _ _ _ _ _ fresh stored)
    have validThere := view.validate_below valid wellFormed nextKept
    obtain ⟨sliced, slicedOK, validNext, sameMode, nextContents⟩ := contents.tail valid
    have slicedThere := view.slice_below sliced 1 _ slicedOK wellFormed nextKept
    have validNextThere := sliced.validate_below validNext wellFormed nextKept
    let next : State memory home := ⟨sliced, remaining, total + value, updated, validNext,
      sameMode.trans readOnly, nextContents, nextKept, nextLoaded, nextWritable⟩
    obtain ⟨cost, segment⟩ : LoopReaches Extracted.program 0 args
        (header memory home ⟨view, value :: remaining, total, current, valid, readOnly, contents,
          kept, loaded, writable⟩) (header memory home next) := by
      cil_loop_steps [header, cutpoint, entry.frame, width, readOnly, validHere, validThere, loaded,
        nonzero, found, element, numericOfWidth, BitVec.ofNat_toNat, facts, stored, nextLoaded,
        slicedThere, validNextThere, nextContents.elementWidth, sameMode, next]
    exact ⟨next, cost, by simpa [next, BitVec.add_assoc] using invariant, by simp [next],
      segment⟩
#print axioms terminates

/-- `Sum` returns the wrapping sum of a valid readonly span's contents, for any length, and
    keeps all caller memory. -/
theorem correctness (memory : Memory) (view : SpanView) (values : List W64)
    (wellFormed : memory.WellFormed) (valid : view.validate memory = .ok ())
    (readOnly : view.writable = false) (contents : SpanContents memory view 8 values) :
    ∃ fuel final, invoke Extracted.program fuel 0 [.bufferSpan view] memory =
      .ok (final, [.scalar (.i64 values.sum)]) ∧ MemoryBelow memory.nextIdentity memory final := by
  have width := contents.elementWidth
  obtain ⟨home, entered, setup, numeric, entryMemory⟩ :=
    entry.checked memory view wellFormed valid width readOnly
  cil_store_vc started stored loaded nextWritable := .word64 (.i64 0) using numeric.writable
  have kept := entryMemory.kept.trans
    (store_numeric_local_preserves_memory_below _ _ _ _ _ _ _ numeric.fresh stored)
  let state : State memory home :=
    ⟨view, values, 0, started, valid, readOnly, contents, kept, loaded, nextWritable⟩
  have path : LoopReaches Extracted.program 0 [.bufferSpan view]
      ⟨0, entry.frame memory view home, [], entered⟩ (header memory home state) := by
    cil_loop_steps [header, cutpoint, state, entry.frame, stored, width, readOnly,
      view.validate_below valid wellFormed kept]
  obtain ⟨fuel, final, returned, executed, sameMemory, sameValues⟩ := loop_reaches_terminates path
    (terminates memory home _ values.sum wellFormed numeric.fresh state (by simp [state]))
  subst returned
  exact ⟨fuel, final,
    invoke_of_run Extracted.lookup0 (by simp [cil_checked, valid]) setup executed, sameMemory⟩
#print axioms correctness

end ExampleProof
