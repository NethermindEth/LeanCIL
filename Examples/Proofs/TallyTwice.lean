import Extracted
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.LoopScaffold

/-! `TallyTwice` counts a struct's `count` field up to its input, adding two to its `sum` field
through `AddTwo` each time, and returns `sum`. The loop tactics gather the struct's field reads,
its home and the call from the frame facts in scope; the proof supplies the invariant, the
measure and the arithmetic. -/

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_method tally tallyBody := "System.UInt32 Examples.Loops::TallyTwice(System.UInt32)"
bind_callee addTwo addTwoBody := "System.UInt32 Examples.Loops::AddTwo(System.UInt32)"
  from tallyBody
bind_call addTwoSite := addTwo from tallyBody

/-- `AddTwo` adds two and touches no memory. -/
def addTwoContract : MethodContract W32 W32 where
  args x := [.scalar (.i32 x)]
  results v := [.scalar (.i32 v)]
  pre _ _ := True
  footprint _ := []
  post x _ _ v := v = x + 2

theorem addTwo_holds : addTwoContract.Holds Extracted.program addTwo := by
  rintro x m -
  dsimp only [addTwoContract]
  refine ⟨8, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
  cil_checked_steps

bind_entry entry (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :=
  tallyBody with [.scalar (.i32 value)] from memory allocating wellFormed
bind_loop loop := tallyBody

/-- The struct local, remembered by its fields `(count, sum)`. -/
private abbrev State (memory : Memory) (home : Reference) :=
  FrameState [] memory [.aggregate 8] (W32 × W32) (fun _ => [.bytes (.aggregate 8) home])
    fun state => [some (.aggregate (Extracted.layout0.encode [.i32 state.1, .i32 state.2]))]

/-- The loop test, with the input and `count` on the stack. -/
bind_cutpoint header (memory : Memory) (value : W32) (home : Reference)
    (state : State memory home) :=
  tallyBody at loop.latch matching (fun op => op matches .bne _) with entry.frame memory home,
    [.scalar (.i32 value), .scalar (.i32 state.values.1)], state.memory

/-- `TallyTwice` returns twice its input and allocates nothing the caller sees. -/
theorem correctness (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke Extracted.program fuel tally [.scalar (.i32 value)] memory =
      .ok (final, [.scalar (.i32 (2 * value))]) ∧
      MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := entry.checked memory value wellFormed
  obtain ⟨zeroed, zeroing, frame, -⟩ :=
    (entryFrame []).zero_aggregate 0 Extracted.layout0 [.i32 0, .i32 0]
  refine invoke_loop_induction tally.found rfl setup (header memory value home)
    (fun state => state.values.2 = 2 * state.values.1)
    (fun state => (value - state.values.1).toNat) ⟨(0, 0), zeroed, frame⟩ (by cil_loop_steps)
    (by simp) ?_
  rintro ⟨⟨count, sum⟩, current, frame⟩ doubled recurse
  dsimp only at doubled
  by_cases done : count = value
  · subst done
    rw [← doubled]
    cil_loop_finish
  · cil_loop_advance [done]
    cil_loop_call addTwo_holds sum at addTwoSite
    · trivial
    rintro final _ ⟨_, invoked⟩ framed ⟨_, rfl, rfl⟩
    dsimp only [addTwoContract] at framed ⊢
    have called := frame.after_confined framed
      (invoke_preserves_wellFormed _ _ _ _ _ _ _ frame.wellFormed invoked) (by simp) (by simp)
    obtain ⟨summed, summing, summedFrame, -⟩ :=
      called.store_field 0 Extracted.layout0_valid 1 (.i32 (sum + 2))
    obtain ⟨counted, counting, countedFrame, -⟩ :=
      summedFrame.store_field 0 Extracted.layout0_valid 0 (.i32 (count + 1))
    refine loop_reaches_terminates (target := header memory value home
      ⟨(count + 1, sum + 2), counted, countedFrame⟩) (by cil_loop_steps) (recurse _ ?_ ?_)
    · show sum + 2 = 2 * (count + 1)
      rw [doubled]
      bv_omega
    · show (value - (count + 1)).toNat < (value - count).toNat
      bv_omega

#print axioms correctness

end ExampleProof
