import Extracted
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.NumericLocals
import CIL.Safety.LoopOutcome
import CIL.Safety.LoopScaffold

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_method countUntil untilBody :=
  "System.UInt32 Examples.Loops::CountUntil(System.UInt32,System.UInt32)"
bind_callee bump bumpBody :=
  "System.UInt32 Examples.Loops::Bump(System.UInt32,System.UInt32)" from untilBody
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

bind_entry entry (value limit : W32) := untilBody
  with [.scalar (.i32 value), .scalar (.i32 limit)] from Memory.empty
  allocating Memory.empty_wellFormed
private def guard : Nat := instructionLocation untilBody fun op =>
  match op with | .brnonzero _ => true | _ => false
/-- The remaining count and the successful calls so far, held by the frame's two locals. -/
private abbrev State (remaining counted : Reference) :=
  FrameState [] Memory.empty [.word32, .word32] (W32 × W32)
    (fun _ => [.bytes .word32 remaining, .bytes .word32 counted])
    fun values => [some (.i32 values.1), some (.i32 values.2)]
/-- The loop head holds the remaining count on the stack. -/
private def header (remaining counted : Reference) (state : State remaining counted) : LoopState :=
  ⟨guard, entry.frame remaining counted, [.scalar (.i32 state.values.1)], state.memory⟩
/-- `count + remaining` is the input, and `count` has not passed the limit. -/
private def invariant {remaining counted : Reference} (value limit : W32)
    (state : State remaining counted) : Prop :=
  state.values.2.toNat + state.values.1.toNat = value.toNat ∧
    state.values.2.toNat ≤ limit.toNat

/-- Uses only `bumpContract` at the call site; the helper body is never unfolded. -/
theorem outcome (holds : bumpContract.Holds Extracted.program bump) (value limit : W32)
    {remaining counted : Reference} (state : State remaining counted)
    (valid : invariant value limit state) :
    LoopOutcome Extracted.program countUntil [.scalar (.i32 value), .scalar (.i32 limit)]
      (fun _ values => values = [.scalar (.i32 value)]) (untilRaises value limit)
      (header remaining counted state) := by
  apply loop_outcome_induction Extracted.program countUntil _ (header remaining counted)
    (invariant value limit) (fun s => s.values.1.toNat) _ _ ?_ state valid
  rintro ⟨⟨x, count⟩, m, frame⟩ ⟨total, bounded⟩ recurse
  dsimp only [invariant] at total bounded recurse
  have loaded0 := frame.load 0
  have loaded1 := frame.load 1
  by_cases zero : x = 0
  · subst x
    have same : count = value := BitVec.eq_of_toNat_eq (by simpa using total)
    subst same
    -- The remaining count is spent before `count` passes the limit, so the run returns.
    have normal : untilRaises count limit = none := by
      simp only [untilRaises]; split <;> first | rfl | omega
    rw [normal, loop_outcome_none]
    cil_loop_finish [entry.frame, header, loaded0, loaded1]
  · have nonzero : x ≠ 0#32 := zero
    have positive : 0 < x.toNat := by
      have : x.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
      omega
    cil_loop_outcome_advance [entry.frame, header, loaded0, loaded1, nonzero]
    by_cases hit : count = limit
    · subst hit
      -- The call raises with iterations left; no invariant or measure obligation remains.
      rw [show untilRaises value count = some _ from ite_eq_left (by omega)]
      cil_loop_outcome_raise holds (count, count) at bumpSite [entry.frame]
      case precondition => trivial
      case raises => simp only [bumpContract, ite_true]
    cil_loop_outcome_call holds (count, limit) at bumpSite [entry.frame]
    case precondition => trivial
    case raises => simp only [bumpContract, hit, ite_false]
    rintro final _ ⟨_, invoked⟩ framed ⟨_, rfl, rfl⟩
    dsimp only [bumpContract, List.nil_append, List.cons_append, Nat.reduceAdd] at framed ⊢
    -- The callee may change only its empty footprint, so both locals survive the call.
    have called := frame.after_confined framed
      (invoke_preserves_wellFormed _ _ _ _ _ _ _ frame.wellFormed invoked) (by simp) (by simp)
    obtain ⟨m1, stored1, frame1, -⟩ := called.store 1 (.i32 (count + 1)) rfl
    obtain ⟨m2, stored0, frame2, -⟩ := frame1.store 0 (.i32 (x - 1)) rfl
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
    refine loop_reaches_outcome (target := header remaining counted ⟨(x - 1, count + 1), m2,
      frame2⟩) ?_ (recurse ⟨(x - 1, count + 1), m2, frame2⟩
        ⟨show (count + 1).toNat + (x - 1).toNat = value.toNat by omega,
          show (count + 1).toNat ≤ limit.toNat by omega⟩ ?_)
    · cil_loop_steps [entry.frame, header, stored0, stored1, frame1.load 0, frame2.load 0]
    show (x - 1).toNat < x.toNat
    omega

/-- The outcome `CountUntil` reaches from its arguments: `untilRaises` of them, or a normal
return. -/
def untilOutcome : List Value → Memory → Option String
  | [.scalar (.i32 value), .scalar (.i32 limit)], _ => untilRaises value limit
  | _, _ => none

/-- For every pair of `uint`s, `CountUntil` returns its input or raises the helper's exception,
given only the helper's contract. -/
theorem count_until (holds : bumpContract.Holds Extracted.program bump) :
    EnsuresOutcome Extracted.program countUntil
      (fun args initial => ∃ value limit : W32,
        args = [.scalar (.i32 value), .scalar (.i32 limit)] ∧ initial = Memory.empty)
      (fun args _ _ values => values = args.take 1) untilOutcome := by
  apply ensures_outcome_of_loop
  intro args initial permitted
  obtain ⟨value, limit, rfl, rfl⟩ := permitted
  obtain ⟨remaining, counted, entered, setup, -, -, -, entryFrame⟩ := entry.checked value limit
  obtain ⟨m1, stored0, frame1, -⟩ := (entryFrame []).store 0 (.i32 value) rfl
  obtain ⟨m2, stored1, frame2, -⟩ := frame1.store 1 (.i32 0) rfl
  have entryPath : LoopReaches Extracted.program countUntil
      [.scalar (.i32 value), .scalar (.i32 limit)] ⟨0, entry.frame remaining counted, [], entered⟩
      (header remaining counted ⟨(value, 0), m2, frame2⟩) := by
    cil_loop_steps [entry.frame, header, stored0, stored1, frame1.load 0, frame2.load 0]
  exact ⟨untilBody, entry.frame remaining counted, entered, countUntil.found, rfl, setup,
    loop_reaches_outcome entryPath (outcome holds value limit ⟨(value, 0), m2, frame2⟩
      ⟨by simp, by simp⟩)⟩

theorem correctness : EnsuresOutcome Extracted.program countUntil
    (fun args initial => ∃ value limit : W32,
      args = [.scalar (.i32 value), .scalar (.i32 limit)] ∧ initial = Memory.empty)
    (fun args _ _ values => values = args.take 1) untilOutcome :=
  count_until bump_holds

#print axioms correctness
end ExampleProof
