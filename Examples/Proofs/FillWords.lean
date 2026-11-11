import Extracted
import CIL.Verification
import CIL.StructuralLabels
import CIL.Safety.LoopScaffold

/-! `FillWords` writes `count` words through a caller reference. The loop invariant states only
    the filled prefix; the loop state carries the frame facts, which the loop tactics keep. -/

open CIL.Safety
open CIL (W32 W64)
namespace ExampleProof

bind_entry entry (initial : Memory) (base : Reference) (v : W64) (n : W32)
    (formed : initial.WellFormed) := Extracted.method0
  with [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)] from initial
  allocating formed
bind_loop loop := Extracted.method0

/-- The index, held by the frame's only local, with the frame facts for the words written. -/
private abbrev State (initial : Memory) (base home : Reference) (n : W32) :=
  FrameState [(base, 8 * n.toNat)] initial [.word32] W32 (fun _ => [.bytes .word32 home])
    fun k => [some (.i32 k)]

/-- The loop test, which compares the index, below the count, against the count. -/
bind_cutpoint header (initial : Memory) (base home : Reference) (n : W32)
    (state : State initial base home n) :=
  Extracted.method0 at loop.latch matching (· matches .blt _)
  with entry.frame initial home, [.scalar (.i32 n), .scalar (.i32 state.values)], state.memory

/-- The first `k` words are filled and the rest stay writable. -/
private def invariant (initial : Memory) (base home : Reference) (v : W64) (n : W32)
    (state : State initial base home n) : Prop :=
  Filled state.memory base 8 (List.replicate state.values.toNat (v : BitVec (8 * 8)))
    (n.toNat - state.values.toNat) ∧ state.values.toNat ≤ n.toNat

/-- `FillWords` fills `count` words from write authority alone and changes no other caller byte. -/
theorem fill_words (initial : Memory) (base : Reference) (v : W64) (n : W32)
    (formed : initial.WellFormed) (valid : form initial base = .ok base) (small : n.toNat < 2^31)
    (writable : Writable initial base 8 0 n.toNat) :
    ∃ fuel final, invoke Extracted.program fuel 0
        [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)] initial = .ok (final, []) ∧
      Contents final base 8 (List.replicate n.toNat (v : BitVec (8 * 8))) ∧
      Confined [(base, 8 * n.toNat)] initial final := by
  obtain ⟨home, entered, enter⟩ := entry.checked initial base v n formed
  have old := formed.form_bound valid
  refine invoke_loop_induction (by rfl) ?_ enter.setup (header initial base home n)
    (invariant initial base home v n) (fun s => n.toNat - s.values.toNat) (fun start => ?_) ?_
  · cil_checked_side [valid]
  · cil_loop_recurse start 0
    case invariant => exact ⟨by simpa using Filled.start writable, by simp⟩
  rintro ⟨k, m, frame⟩ ⟨filled, bounded⟩ recurse
  dsimp only at filled bounded
  by_cases exit : k.toNat = n.toNat
  · obtain rfl : k = n := BitVec.eq_of_toNat_eq exit
    have stays : ¬ k.toInt < k.toInt := Int.lt_irrefl _
    cil_loop_finish [stays]
  · have lower : k.toNat < n.toNat := by omega
    obtain ⟨m1, target, stored, pushed⟩ := filled.write_next (by omega) (v : BitVec (8 * 8))
    simp only [List.length_replicate] at target stored
    have baseForm := frame.form valid old
    have frame1 := frame.write_element stored (List.mem_singleton_self _) lower old
    cil_loop_recurse recurse (k + 1) [int_lt small lower,
      add_int_element frame.wellFormed baseForm (by omega) target, step_store64_of_write stored]
    all_goals simp only [invariant, toNat_succ lower]
    case invariant =>
      rw [List.replicate_succ', show n.toNat - (k.toNat + 1) = n.toNat - k.toNat - 1 by omega]
      exact ⟨pushed, by omega⟩
    case measure => omega

/-- Every nonnegative count fills exactly that many words, whatever the buffer held before. -/
theorem correctness : Ensures Extracted.program 0
    (fun args initial => ∃ base v n,
      args = [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)] ∧
      initial.WellFormed ∧ form initial base = .ok base ∧ n.toNat < 2^31 ∧
      Writable initial base 8 0 n.toNat)
    (fun args initial final values => values = [] ∧ ∀ base v n,
      args = [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)] →
      Contents final base 8 (List.replicate n.toNat (v : BitVec (8 * 8))) ∧
        Confined [(base, 8 * n.toNat)] initial final) := by
  rintro args initial ⟨base, v, n, rfl, formed, valid, small, writable⟩
  have execution := fill_words initial base v n formed valid small writable
  rw [exists_comm] at execution
  simp only [exists_and_right] at execution
  obtain ⟨final, executed, contents, framed⟩ := execution
  apply WP.exists_execution
  refine WP.consequence (post := fun result => result = (final, [])) ?_ ?_
  · exact WP.exact_iff.mpr executed
  rintro result rfl
  refine ⟨rfl, ?_⟩
  intro other value count same
  simp only [List.cons.injEq, Value.reference.injEq, ManagedReference.address.injEq,
    Value.scalar.injEq, CIL.Value.i64.injEq, CIL.Value.i32.injEq, and_true] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact ⟨contents, framed⟩

#print axioms fill_words
#print axioms correctness

end ExampleProof
