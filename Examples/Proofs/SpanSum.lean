import Extracted
import CIL.Verification
import CIL.Safety.LoopScaffold
import CIL.Safety.LoopVC
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

/-- The unconsumed suffix of the caller's span and the total of the consumed prefix, held in the
    frame home, with the frame facts of the current memory. -/
private abbrev State (memory : Memory) (home : Reference) :=
  FrameState [] memory [.word64, .span 8 false] (SpanSuffix memory 8 false × W64)
    (fun state => [.bytes .word64 home, .span 8 false (some state.1.view)])
    fun state => [some (.i64 state.2), none]

-- The loop guard observes the remaining span length.
bind_cutpoint header (memory : Memory) (home : Reference) (state : State memory home) :=
  Extracted.method0 at loop.latch matching (· matches .brnonzero _)
  with entry.frame memory state.values.1.view home,
    [.scalar (.i32 (BitVec.ofNat 32 state.values.1.view.length))], state.memory

/-- `Sum` returns the wrapping sum of a valid readonly span's contents, for any length, and
    keeps all caller memory. -/
theorem correctness (memory : Memory) (view : SpanView) (values : List W64)
    (wellFormed : memory.WellFormed) (valid : view.validate memory = .ok ())
    (readOnly : view.writable = false) (contents : SpanContents memory view 8 values) :
    ∃ fuel final, invoke Extracted.program fuel 0 [.bufferSpan view] memory =
      .ok (final, [.scalar (.i64 values.sum)]) ∧ MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, enter⟩ :=
    entry.checked memory view wellFormed valid contents.elementWidth readOnly
  obtain ⟨started, stored, frame, -⟩ := (enter.frame []).store 0 (.i64 0) rfl
  have span : CheckedSpan memory view 8 false values := ⟨valid, readOnly, contents⟩
  refine invoke_loop_results Extracted.lookup0 (by simp [cil_checked, valid]) enter.setup
    (header memory home) (fun state => state.values.2 + state.values.1.values.sum = values.sum)
    (·.values.1.values.length) ⟨(⟨view, values, span⟩, 0), started, frame⟩
    (by cil_loop_steps) (by simp) ?_
  rintro ⟨⟨⟨view, remaining, span⟩, total⟩, current, frame⟩ invariant
  cases remaining with
  | nil => exact .inl (by cil_loop_finish [invariant.symm])
  | cons value remaining =>
    obtain ⟨item, -, found, element⟩ := (span.within wellFormed frame).head (by decide)
    obtain ⟨updated, stored, nextFrame, -⟩ := frame.store 0 (.i64 (total + value)) rfl
    obtain ⟨sliced, slicedOK, next, -⟩ := span.tail_below wellFormed nextFrame.kept
    cil_loop_continue ⟨(⟨sliced, remaining, next⟩, total + value), updated,
      nextFrame.set_local 1 (.span 8 false (some sliced))⟩
    case invariant => simpa [BitVec.add_assoc] using invariant
    case measure => simp
#print axioms correctness

end ExampleProof
