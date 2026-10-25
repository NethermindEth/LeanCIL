import Extracted
import Examples.Support
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.NumericLocals
import CIL.Safety.LoopOutcome

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_method countUntil untilBody := "System.UInt32 Examples.Loops::CountUntil(System.UInt32,System.UInt32)"
bind_callee bump bumpBody := "System.UInt32 Examples.Loops::Bump(System.UInt32,System.UInt32)" from untilBody
bind_call bumpSite := bump from untilBody

def bumpContract : OutcomeContract (W32 × W32) W32 where
  args input := [.scalar (.i32 input.1), .scalar (.i32 input.2)]
  results v := [.scalar (.i32 v)]
  pre _ _ := True
  footprint _ := []
  post input _ _ v := v = input.1 + 1
  raises input _ := if input.1 = input.2 then some "System.InvalidOperationException" else none

theorem bump_holds : bumpContract.Holds Extracted.program bump := by
  rintro ⟨count, limit⟩ m -
  by_cases same : count = limit
  · subst same
    simp only [bumpContract, ite_true]
    cil_raise_steps []
  · simp only [bumpContract, same, ite_false]
    refine ⟨8, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
    cil_checked_steps [same]

/-- `CountUntil` raises exactly when the input exceeds the limit, after `limit` successful calls. -/
def untilRaises (value limit : W32) : Option String :=
  if limit.toNat < value.toNat then some "System.InvalidOperationException" else none

private def frame : Frame := ⟨0, [.bytes .word32 ⟨0, 0⟩, .bytes .word32 ⟨1, 0⟩], [0, 1], [], 0⟩
private def guard : Nat := instructionLocation untilBody fun op =>
  match op with | .brnonzero _ => true | _ => false
/-- The loop head holds the remaining count on the stack. -/
private def header (state : W32 × W32 × Memory) : LoopState :=
  ⟨guard, frame, [.scalar (.i32 state.1)], state.2.2⟩
/-- Both locals hold their values and stay writable, `count + remaining` is the input, and `count` has not passed the limit. -/
private def invariant (value limit : W32) (state : W32 × W32 × Memory) : Prop :=
  read state.2.2 ⟨0, 0⟩ 4 1 = .ok (numberBytes state.1.toNat 4) ∧
  read state.2.2 ⟨1, 0⟩ 4 1 = .ok (numberBytes state.2.1.toNat 4) ∧
  access state.2.2 ⟨0, 0⟩ 4 1 true = .ok () ∧ access state.2.2 ⟨1, 0⟩ 4 1 true = .ok () ∧
  2 ≤ state.2.2.nextIdentity ∧ state.2.1.toNat + state.1.toNat = value.toNat ∧ state.2.1.toNat ≤ limit.toNat

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

/-- Uses only `bumpContract` at the call site; the helper body is never unfolded. -/
theorem outcome (holds : bumpContract.Holds Extracted.program bump) (value limit : W32)
    (state : W32 × W32 × Memory) (valid : invariant value limit state) :
    LoopOutcome Extracted.program countUntil [.scalar (.i32 value), .scalar (.i32 limit)]
      (fun _ values => values = [.scalar (.i32 value)]) (untilRaises value limit) (header state) := by
  apply loop_outcome_induction Extracted.program countUntil _ header (invariant value limit)
    (fun s => s.1.toNat) _ _ ?_ state valid
  rintro ⟨x, count, m⟩ ⟨read0, read1, writable0, writable1, allocated, total, bounded⟩ recurse
  dsimp only at read0 read1 writable0 writable1 allocated total bounded recurse
  have loaded0 := load_numeric_local .word32 (.i32 x) x.toNat rfl read0
  have loaded1 := load_numeric_local .word32 (.i32 count) count.toNat rfl read1
  simp only [localResult] at loaded0 loaded1
  by_cases zero : x = 0
  · subst x
    have same : count = value := BitVec.eq_of_toNat_eq (by simpa using total)
    subst same
    -- The remaining count is spent before `count` passes the limit, so the run returns.
    have normal : untilRaises count limit = none := by
      simp only [untilRaises]; split <;> first | rfl | omega
    rw [normal, loop_outcome_none]
    cil_loop_finish [frame, header, loaded0, loaded1]
  · have nonzero : x ≠ 0#32 := zero
    have positive : 0 < x.toNat := by
      have : x.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
      omega
    cil_loop_outcome_advance [frame, header, loaded0, loaded1, nonzero]
    by_cases hit : count = limit
    · subst hit
      -- The call raises with iterations left; no invariant or measure obligation remains.
      rw [show untilRaises value count = some _ from ite_eq_left (by omega)]
      cil_loop_outcome_raise holds (count, count) at bumpSite [frame]
      · trivial
      · simp only [bumpContract, ite_true]
    cil_loop_outcome_call holds (count, limit) at bumpSite [frame]
    · trivial
    · simp only [bumpContract, hit, ite_false]
    rintro final _ - framed ⟨_, rfl, rfl⟩
    dsimp only [bumpContract, List.nil_append, List.cons_append, Nat.reduceAdd] at framed ⊢
    -- The callee may change only its empty footprint, so both locals survive the call.
    have outside : ∀ q : Reference, ∀ i < 4, Outside [] q.allocation (q.offset + i) :=
      fun _ _ _ _ member => nomatch member
    have called1 : access final ⟨1, 0⟩ 4 1 true = .ok () :=
      (framed.access_write ⟨1, 0⟩ (show 1 < m.nextIdentity by omega) 4 1).trans writable1
    have called0 : read final ⟨0, 0⟩ 4 1 = .ok (numberBytes x.toNat 4) :=
      (framed.read_eq ⟨0, 0⟩ (show 0 < m.nextIdentity by omega) 4 1 (outside _)).trans read0
    have calledWritable0 : access final ⟨0, 0⟩ 4 1 true = .ok () :=
      (framed.access_write ⟨0, 0⟩ (show 0 < m.nextIdentity by omega) 4 1).trans writable0
    have grown := framed.grows
    obtain ⟨m1, written1, stored1, bytes1⟩ := store_numeric_local .word32 (.i32 (count + 1))
      (count + 1).toNat rfl called1
    simp only [localWidth] at written1 bytes1
    obtain ⟨kept0, keptWritable0, grown1⟩ := other_local written1 (q := ⟨0, 0⟩)
      (show 0 < final.nextIdentity by omega)
      (by decide)
    rw [called0] at kept0
    rw [calledWritable0] at keptWritable0
    have loaded0' := load_numeric_local .word32 (.i32 x) x.toNat rfl kept0
    obtain ⟨m2, written0, stored0, bytes0⟩ := store_numeric_local .word32 (.i32 (x - 1))
      (x - 1).toNat rfl keptWritable0
    simp only [localWidth] at written0 bytes0
    obtain ⟨kept1, keptWritable1, grown2⟩ := other_local written0 (q := ⟨1, 0⟩)
      (show 1 < m1.nextIdentity by omega)
      (by decide)
    rw [bytes1] at kept1
    have loaded0'' := load_numeric_local .word32 (.i32 (x - 1)) (x - 1).toNat rfl bytes0
    simp only [localResult] at loaded0' loaded0''
    simp only [BitVec.ofNat_eq_ofNat] at stored0 stored1 loaded0''
    obtain ⟨_, ready1⟩ := access_requirements called1
    have stillWritable1 := keptWritable1.trans (ready1.after_write written1).access
    obtain ⟨_, ready0⟩ := access_requirements keptWritable0
    have below : count.toNat < limit.toNat := by
      have : count.toNat ≠ limit.toNat := fun h => hit (BitVec.eq_of_toNat_eq h)
      omega
    have bumped : (count + 1).toNat = count.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    have lowered : (x - 1).toNat = x.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le]
      · simp
      · change 1 ≤ x.toNat
        omega
    -- The next head is chosen only now, from the memory the contract returned.
    refine loop_reaches_outcome (target := header (x - 1, count + 1, m2)) ?_ (recurse (x - 1, count + 1, m2)
      ⟨bytes0, kept1, (ready0.after_write written0).access, stillWritable1,
        show 2 ≤ m2.nextIdentity by omega,
        show (count + 1).toNat + (x - 1).toNat = value.toNat by omega,
        show (count + 1).toNat ≤ limit.toNat by omega⟩ ?_)
    · cil_loop_steps [frame, header, stored0, stored1, loaded0', loaded0'']
    show (x - 1).toNat < x.toNat
    omega

/-- The outcome `CountUntil` reaches from its arguments: `untilRaises` of them, or a normal return. -/
def untilOutcome : List Value → Memory → Option String
  | [.scalar (.i32 value), .scalar (.i32 limit)], _ => untilRaises value limit
  | _, _ => none

/-- For every pair of `uint`s, `CountUntil` returns its input or raises the helper's exception, given only the helper's contract. -/
theorem count_until (holds : bumpContract.Holds Extracted.program bump) :
    EnsuresOutcome Extracted.program countUntil
      (fun args initial => ∃ value limit : W32,
        args = [.scalar (.i32 value), .scalar (.i32 limit)] ∧ initial = Examples.empty)
      (fun args _ _ values => values = args.take 1) untilOutcome := by
  apply ensures_outcome_of_loop
  intro args initial permitted
  obtain ⟨value, limit, rfl, rfl⟩ := permitted
  let entered := ((enterFrame untilBody [] Examples.empty).toOption.getD (frame, Examples.empty)).2
  have setup : enterFrame untilBody [.scalar (.i32 value), .scalar (.i32 limit)] Examples.empty =
      .ok (frame, entered) := by
    rfl
  have writable0 : access entered ⟨0, 0⟩ 4 1 true = .ok () := by rfl
  have writable1 : access entered ⟨1, 0⟩ 4 1 true = .ok () := by rfl
  have allocated : entered.nextIdentity = 2 := by rfl
  obtain ⟨m1, written0, stored0, bytes0⟩ := store_numeric_local .word32 (.i32 value) value.toNat rfl writable0
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
  have loaded0 := load_numeric_local .word32 (.i32 value) value.toNat rfl kept0
  simp only [localResult] at loaded0
  simp only [BitVec.ofNat_eq_ofNat] at stored1
  have entryPath : LoopReaches Extracted.program countUntil [.scalar (.i32 value), .scalar (.i32 limit)]
      ⟨0, frame, [], entered⟩ (header (value, 0, m2)) := by
    cil_loop_steps [frame, header, stored0, stored1, loaded0]
  exact ⟨untilBody, frame, entered, countUntil.found, rfl, setup, loop_reaches_outcome entryPath
    (outcome holds value limit (value, 0, m2)
      ⟨kept0, bytes1, keptWritable0.trans (ready0.after_write written0).access,
        (ready1.after_write written1).access, show 2 ≤ m2.nextIdentity by omega,
        by simp, by simp⟩)⟩

theorem correctness : EnsuresOutcome Extracted.program countUntil
    (fun args initial => ∃ value limit : W32,
      args = [.scalar (.i32 value), .scalar (.i32 limit)] ∧ initial = Examples.empty)
    (fun args _ _ values => values = args.take 1) untilOutcome :=
  count_until bump_holds

#print axioms correctness
end ExampleProof
