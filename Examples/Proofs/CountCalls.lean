import Extracted
import Examples.Support
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.NumericLocals
import CIL.Safety.LoopContract

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_method countCalls countBody := "System.UInt32 Examples.Loops::CountCalls(System.UInt32)"
bind_callee decrement decrementBody := "System.UInt32 Examples.Loops::Decrement(System.UInt32)" from countBody
bind_call decrementSite := decrement from countBody

def decrementContract : MethodContract W32 W32 where
  args x := [.scalar (.i32 x)]
  results v := [.scalar (.i32 v)]
  pre _ _ := True
  footprint _ := []
  post x _ _ v := v = x - 1

theorem decrement_holds : decrementContract.Holds Extracted.program decrement := by
  rintro x m -
  dsimp only [decrementContract]
  refine ⟨8, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
  cil_checked_steps

private def frame : Frame := ⟨0, [.bytes .word32 ⟨0, 0⟩, .bytes .word32 ⟨1, 0⟩], [0, 1], []⟩
private def guard : Nat := instructionLocation countBody fun op =>
  match op with | .brnonzero _ => true | _ => false
/-- The loop head holds the remaining count on the stack. -/
private def header (state : W32 × W32 × Memory) : LoopState :=
  ⟨guard, frame, [.scalar (.i32 state.1)], state.2.2⟩
/-- Both locals hold their values and stay writable, and `count + remaining` is the input. -/
private def invariant (value : W32) (state : W32 × W32 × Memory) : Prop :=
  read state.2.2 ⟨0, 0⟩ 4 1 = .ok (numberBytes state.1.toNat 4) ∧
  read state.2.2 ⟨1, 0⟩ 4 1 = .ok (numberBytes state.2.1.toNat 4) ∧
  access state.2.2 ⟨0, 0⟩ 4 1 true = .ok () ∧ access state.2.2 ⟨1, 0⟩ 4 1 true = .ok () ∧
  2 ≤ state.2.2.nextIdentity ∧ state.2.1 + state.1 = value

/-- A word write to one local leaves another local's bytes and write access unchanged. -/
private theorem other_local {m result : Memory} {r q : Reference} {bytes : List (BitVec 8)}
    (wrote : write m r bytes 1 = .ok result) (old : q.allocation < m.nextIdentity)
    (different : q.allocation ≠ r.allocation) :
    read result q 4 1 = read m q 4 1 ∧ access result q 4 1 true = access m q 4 1 true ∧
      m.nextIdentity ≤ result.nextIdentity :=
  have confined := Confined.write wrote (List.mem_singleton_self _)
  ⟨confined.read_eq q old 4 1 fun _ _ entry member => by
      simp only [List.mem_singleton] at member
      subst member
      exact Or.inl different,
    confined.access_write q old 4 1, confined.grows⟩

/-- Uses only `decrementContract` at the call site; the helper body is never unfolded. -/
theorem terminates (holds : decrementContract.Holds Extracted.program decrement)
    (args : List CIL.Safety.Value) (value : W32) (state : W32 × W32 × Memory)
    (valid : invariant value state) :
    LoopTerminates Extracted.program countCalls args (fun _ values => values = [.scalar (.i32 value)])
      (header state) := by
  apply loop_terminates_induction Extracted.program countCalls args header (invariant value)
    (fun s => s.1.toNat) _ ?_ state valid
  rintro ⟨x, count, m⟩ ⟨read0, read1, writable0, writable1, allocated, total⟩ recurse
  dsimp only at read0 read1 writable0 writable1 allocated total recurse
  have loaded0 := load_numeric_local .word32 (.i32 x) x.toNat rfl read0
  have loaded1 := load_numeric_local .word32 (.i32 count) count.toNat rfl read1
  simp only [localResult] at loaded0 loaded1
  by_cases zero : x = 0
  · subst x
    have same : count = value := by simpa using total
    subst same
    cil_loop_finish [frame, header, loaded0, loaded1]
  · have nonzero : x ≠ 0#32 := zero
    cil_loop_advance [frame, header, loaded0, nonzero]
    cil_loop_call holds x at decrementSite [frame, loaded0]
    · trivial
    rintro final _ - framed ⟨_, rfl, rfl⟩
    dsimp only [decrementContract, List.nil_append, List.cons_append, Nat.reduceAdd] at framed ⊢
    -- The callee may change only its empty footprint, so both locals survive the call.
    have outside : ∀ q : Reference, ∀ i < 4, Outside [] q.allocation (q.offset + i) :=
      fun _ _ _ _ member => nomatch member
    have called0 : access final ⟨0, 0⟩ 4 1 true = .ok () :=
      (framed.access_write ⟨0, 0⟩ (show 0 < m.nextIdentity by omega) 4 1).trans writable0
    have called1 : read final ⟨1, 0⟩ 4 1 = .ok (numberBytes count.toNat 4) :=
      (framed.read_eq ⟨1, 0⟩ (show 1 < m.nextIdentity by omega) 4 1 (outside _)).trans read1
    have calledWritable1 : access final ⟨1, 0⟩ 4 1 true = .ok () :=
      (framed.access_write ⟨1, 0⟩ (show 1 < m.nextIdentity by omega) 4 1).trans writable1
    have grown := framed.grows
    obtain ⟨m1, written0, stored0, bytes0⟩ := store_numeric_local .word32 (.i32 (x - 1))
      (x - 1).toNat rfl called0
    simp only [localWidth] at written0 bytes0
    obtain ⟨kept1, keptWritable1, grown1⟩ := other_local written0 (q := ⟨1, 0⟩)
      (show 1 < final.nextIdentity by omega)
      (by decide)
    rw [called1] at kept1
    rw [calledWritable1] at keptWritable1
    have loaded1' := load_numeric_local .word32 (.i32 count) count.toNat rfl kept1
    obtain ⟨m2, written1, stored1, bytes1⟩ := store_numeric_local .word32 (.i32 (count + 1))
      (count + 1).toNat rfl keptWritable1
    simp only [localWidth] at written1 bytes1
    obtain ⟨kept0, keptWritable0, grown2⟩ := other_local written1 (q := ⟨0, 0⟩)
      (show 0 < m1.nextIdentity by omega)
      (by decide)
    rw [bytes0] at kept0
    have loaded0' := load_numeric_local .word32 (.i32 (x - 1)) (x - 1).toNat rfl kept0
    simp only [localResult] at loaded0' loaded1'
    simp only [BitVec.ofNat_eq_ofNat] at stored0 stored1 loaded0'
    obtain ⟨_, ready0⟩ := access_requirements called0
    have stillWritable0 := keptWritable0.trans (ready0.after_write written0).access
    obtain ⟨_, ready1⟩ := access_requirements keptWritable1
    -- The next head is chosen only now, from the memory the contract returned.
    refine loop_reaches_terminates (target := header (x - 1, count + 1, m2)) ?_ (recurse (x - 1, count + 1, m2)
      ⟨kept0, bytes1, stillWritable0, (ready1.after_write written1).access,
        show 2 ≤ m2.nextIdentity by omega, show count + 1 + (x - 1) = value by rw [← total]; bv_omega⟩ ?_)
    · cil_loop_steps [frame, header, stored0, stored1, loaded0', loaded1']
    have positive : 0 < x.toNat := by
      have : x.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
      omega
    show (x - 1).toNat < x.toNat
    rw [BitVec.toNat_sub_of_le]
    · simp; omega
    · change 1 ≤ x.toNat
      omega

/-- `CountCalls` returns its input for every `uint`, given only the helper's contract. -/
theorem count_calls (holds : decrementContract.Holds Extracted.program decrement) :
    CIL.Safety.Ensures Extracted.program countCalls
      (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Examples.empty)
      (fun args _ _ values => values = args) := by
  apply ensures_of_loop
  intro args initial permitted
  obtain ⟨x, rfl, rfl⟩ := permitted
  let entered := ((enterFrame countBody [] Examples.empty).toOption.getD (frame, Examples.empty)).2
  have setup : enterFrame countBody [.scalar (.i32 x)] Examples.empty = .ok (frame, entered) := by
    rfl
  have writable0 : access entered ⟨0, 0⟩ 4 1 true = .ok () := by rfl
  have writable1 : access entered ⟨1, 0⟩ 4 1 true = .ok () := by rfl
  have allocated : entered.nextIdentity = 2 := by rfl
  obtain ⟨m1, written0, stored0, bytes0⟩ := store_numeric_local .word32 (.i32 x) x.toNat rfl writable0
  simp only [localWidth] at written0 bytes0
  obtain ⟨_, ready0⟩ := access_requirements writable0
  obtain ⟨kept1, keptWritable1, grown1⟩ := other_local written0 (q := ⟨1, 0⟩)
    (show 1 < entered.nextIdentity by omega) (by decide)
  rw [writable1] at keptWritable1
  obtain ⟨m2, written1, stored1, bytes1⟩ := store_numeric_local .word32 (.i32 0) 0 rfl keptWritable1
  simp only [localWidth] at written1 bytes1
  obtain ⟨_, ready1⟩ := access_requirements keptWritable1
  obtain ⟨kept0, keptWritable0, grown2⟩ := other_local written1 (q := ⟨0, 0⟩)
    (show 0 < m1.nextIdentity by omega) (by decide)
  rw [bytes0] at kept0
  have loaded0 := load_numeric_local .word32 (.i32 x) x.toNat rfl kept0
  simp only [localResult] at loaded0
  simp only [BitVec.ofNat_eq_ofNat] at stored1
  have entryPath : LoopReaches Extracted.program countCalls [.scalar (.i32 x)]
      ⟨0, frame, [], entered⟩ (header (x, 0, m2)) := by
    cil_loop_steps [frame, header, stored0, stored1, loaded0]
  obtain ⟨fuel, final, values, executed, satisfied⟩ := loop_reaches_terminates entryPath
    (terminates holds [.scalar (.i32 x)] x (x, 0, m2)
      ⟨kept0, bytes1, keptWritable0.trans (ready0.after_write written0).access,
        (ready1.after_write written1).access, show 2 ≤ m2.nextIdentity by omega,
        by simp⟩)
  exact ⟨countBody, frame, entered, countCalls.found, rfl, setup, fuel, final, values, executed, satisfied⟩

theorem correctness : CIL.Safety.Ensures Extracted.program countCalls
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Examples.empty)
    (fun args _ _ values => values = args) :=
  count_calls decrement_holds

#print axioms correctness
end ExampleProof
