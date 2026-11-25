import CIL.Safety.DecodedSegment
import CIL.Safety.StepComposition

/-! A loop summary from an invariant and a decreasing measure, and the refutation of a summary
for a loop that never exits. -/

namespace Tests.LoopSummary
open CIL.Safety
open CIL (W32)

/-- `while (v != 0) v--; return v;` on the evaluation stack, with the loop head at pc 0. -/
@[cil_code] def countdown : CIL.Method := {
  returnsValue := true, locals := [], code := [.dup, .brfalse 5, .ldc_i4 1, .sub, .br 0, .ret] }

/-- A loop that branches to itself. -/
@[cil_code] def spin : CIL.Method := { returnsValue := false, locals := [], code := [.br 0] }

/-- The loop is entered with one 32-bit counter on the stack. -/
def entered (_ : List Value) (state : SegmentState) : Prop :=
  ∃ value : W32, state.stack = [.scalar (.i32 value)]

/-- Each cutpoint keeps the entry frame and memory and holds one counter. -/
def counting (_ : List Value) (origin current : SegmentState) : Prop :=
  current.frame = origin.frame ∧ current.memory = origin.memory ∧
    ∃ value : W32, current.stack = [.scalar (.i32 value)]

/-- The counter left on the stack. -/
def remaining (_ : List Value) (_ current : SegmentState) : Nat :=
  match current.stack with
  | [.scalar (.i32 value)] => value.toNat
  | _ => 0

/-- The loop exits with a zero counter and the entry frame and memory. -/
def finished (_ : List Value) (origin after : SegmentState) : Prop :=
  after = { origin with stack := [.scalar (.i32 0)] }

/-- A zero counter leaves the loop at the return. -/
private theorem exits (args : List Value) (frame : Frame) (memory : Memory) :
    SegmentRun [countdown] 0 0 5 2 args ⟨frame, [.scalar (.i32 0)], memory⟩
      ⟨frame, [.scalar (.i32 0)], memory⟩ := by
  intro fuel
  rfl

/-- A nonzero counter is decremented and control returns to the loop head. -/
private theorem iterates (args : List Value) (frame : Frame) (memory : Memory) (value : W32)
    (nonzero : value ≠ 0) :
    SegmentRun [countdown] 0 0 0 5 args ⟨frame, [.scalar (.i32 value)], memory⟩
      ⟨frame, [.scalar (.i32 (value - 1))], memory⟩ := by
  intro fuel
  have branch : step countdown (.brfalse 5) 1 args frame
      [.scalar (.i32 value), .scalar (.i32 value)] memory =
      .ok (.next 2 [.scalar (.i32 value)] frame memory) := by
    have reduce : step countdown (.brfalse 5) 1 args frame
        [.scalar (.i32 value), .scalar (.i32 value)] memory =
        .ok (.next (if value != 0 then 2 else 5) [.scalar (.i32 value)] frame memory) := rfl
    have taken : (value != 0) = true := by simpa using nonzero
    rw [reduce]
    simp only [taken, ite_true]
  exact (run_next (fuel := fuel + 4) rfl rfl rfl).trans
    ((run_next (fuel := fuel + 3) rfl rfl branch).trans
    ((run_next (fuel := fuel + 2) rfl rfl rfl).trans
    ((run_next (fuel := fuel + 1) rfl rfl rfl).trans (run_next rfl rfl rfl))))

/-- The countdown reaches its return with a zero counter for every entry counter. -/
theorem countdown_terminates :
    (SegmentContract.continuing 5 entered finished (fun _ _ => [])).Holds [countdown] 0 0 := by
  apply SegmentContract.Holds.loop (invariant := counting) (measure := remaining)
  · rintro origin args ⟨frame, stack, memory⟩ ⟨_, rfl, rfl, value, rfl⟩
    by_cases zero : value = 0
    · subst zero
      exact ⟨.reaches 5 ⟨origin.frame, [.scalar (.i32 0)], origin.memory⟩,
        ⟨2, by decide, (exits args _ _).reaches⟩, Confined.refl _ _, .inl ⟨rfl, rfl⟩⟩
    · refine ⟨.reaches 0 ⟨origin.frame, [.scalar (.i32 (value - 1))], origin.memory⟩,
        ⟨5, by decide, (iterates args _ _ value zero).reaches⟩, Confined.refl _ _,
        .inr ⟨rfl, ⟨rfl, rfl, _, rfl⟩, ?_⟩⟩
      simp only [remaining]
      have positive : 0 < value.toNat := by
        rcases Nat.eq_zero_or_pos value.toNat with same | positive
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using same)) zero
        · exact positive
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact positive)]
      simp
      omega
  · rintro args ⟨frame, stack, memory⟩ ⟨value, rfl⟩
    exact ⟨rfl, rfl, value, rfl⟩

#print axioms countdown_terminates

/-- The countdown changes no caller memory: a read of earlier memory returns the same bytes and
    every earlier allocation is still live when the loop exits. -/
theorem countdown_preserves_reads (args : List Value) (before : SegmentState) (value : W32)
    (counter : before.stack = [.scalar (.i32 value)]) (formed : before.memory.WellFormed)
    {reference : Reference} {width alignment : Nat} {bytes : List (BitVec 8)}
    (loaded : read before.memory reference width alignment = .ok bytes) :
    ∃ after, (SegmentExit.reaches 5 after).Exhibited [countdown] 0 0 args before ∧
      after.memory.allocations = before.memory.allocations ∧
      read after.memory reference width alignment = .ok bytes := by
  obtain ⟨exit, ran, post, kept⟩ := countdown_terminates.preserves (arguments := args)
    ⟨value, counter⟩ formed loaded (fun _ none => nomatch none)
  cases exit with
  | reaches pc after =>
    obtain ⟨rfl, rfl⟩ := post
    obtain ⟨_, _, same⟩ := kept _ rfl
    exact ⟨_, ran, rfl, same⟩
  | returns | faults | diverges => exact post.elim

#print axioms countdown_preserves_reads

/-- Without a decreasing measure no summary can be given: the self-loop never reaches pc 1. -/
theorem spin_has_no_exit_summary :
    ¬ (SegmentContract.continuing 1 (fun _ _ => True) (fun _ _ _ => True)
      (fun _ _ => [])).Holds [spin] 0 0 := by
  intro holds
  obtain ⟨exit, ran, _, post⟩ := holds [] ⟨⟨0, [], [], 0, []⟩, [], Memory.empty⟩ trivial
  cases exit with
  | reaches pc after =>
    obtain ⟨rfl, -⟩ := post
    obtain ⟨_, _, reached⟩ := ran
    have looping : SegmentExit.Exhibited [spin] 0 0 [] ⟨⟨0, [], [], 0, []⟩, [], Memory.empty⟩
        .diverges :=
      SegmentExit.diverges_of_recurrent (invariant := fun pc state =>
          pc = 0 ∧ state = ⟨⟨0, [], [], 0, []⟩, [], Memory.empty⟩)
        (fun pc state ⟨atHead, same⟩ => ⟨0, state, 1, by decide, by
          subst atHead; subst same
          exact SegmentRun.reaches fun fuel => rfl, rfl, same⟩) ⟨rfl, rfl⟩
    have stuck : run [spin] 1 0 1 [] after.frame after.stack after.memory =
        .error ⟨0, 1, .invalidState⟩ := rfl
    obtain ⟨more, early⟩ := reached.continues 1 _ (by simp [Stable]) stuck
    obtain ⟨fault, exhausted, ran⟩ := looping more
    rw [early] at ran
    cases ran
    exact absurd exhausted (by decide)
  | returns | faults | diverges => exact post

#print axioms spin_has_no_exit_summary

end Tests.LoopSummary
