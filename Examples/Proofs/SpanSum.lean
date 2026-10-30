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

/-- The unconsumed suffix of the caller's span and the total of the consumed prefix, held in a
    frame home of the current memory. -/
private structure State (memory : Memory) (home : Reference) where
  suffix : SpanSuffix memory 8 false
  total : W64
  current : Memory
  frame : EntryMemory memory current
  holds : NumericEntryHome memory current .word64 total.toNat home

-- The loop guard observes the remaining span length.
bind_cutpoint header (memory : Memory) (home : Reference) (state : State memory home) :=
  Extracted.method0 at loop.latch matching (· matches .brnonzero _)
  with entry.frame memory state.suffix.view home,
    [.scalar (.i32 (BitVec.ofNat 32 state.suffix.view.length))], state.current

/-- `Sum` returns the wrapping sum of a valid readonly span's contents, for any length, and
    keeps all caller memory. -/
theorem correctness (memory : Memory) (view : SpanView) (values : List W64)
    (wellFormed : memory.WellFormed) (valid : view.validate memory = .ok ())
    (readOnly : view.writable = false) (contents : SpanContents memory view 8 values) :
    ∃ fuel final, invoke Extracted.program fuel 0 [.bufferSpan view] memory =
      .ok (final, [.scalar (.i64 values.sum)]) ∧ MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, numeric, entryMemory⟩ :=
    entry.checked memory view wellFormed valid contents.elementWidth readOnly
  cil_home_store started stored loaded frame holds := (.i64 0) using entryMemory numeric
  have span : CheckedSpan memory view 8 false values := ⟨valid, readOnly, contents⟩
  refine invoke_loop_results Extracted.lookup0 (by simp [cil_checked, valid]) setup
    (header memory home) (fun state => state.total + state.suffix.values.sum = values.sum)
    (·.suffix.values.length) ⟨⟨view, values, span⟩, 0, started, frame, holds⟩
    (by cil_loop_steps) (by simp) ?_
  rintro ⟨⟨view, remaining, span⟩, total, current, frame, holds⟩ invariant
  cases remaining with
  | nil => exact .inl (by cil_loop_finish [invariant.symm])
  | cons value remaining =>
    obtain ⟨item, -, found, element⟩ := (span.within wellFormed frame).head (by decide)
    cil_home_store updated stored nextLoaded nextFrame nextHolds := (.i64 (total + value))
      using frame holds
    obtain ⟨sliced, slicedOK, next, there⟩ := span.tail_below wellFormed nextFrame.kept
    cil_loop_continue ⟨⟨sliced, remaining, next⟩, total + value, updated, nextFrame, nextHolds⟩
    · simpa [BitVec.add_assoc] using invariant
    · simp
#print axioms correctness

end ExampleProof
