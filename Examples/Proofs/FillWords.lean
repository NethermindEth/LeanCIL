import Extracted
import CIL.Verification
import CIL.Safety.LoopScaffold
import CIL.Safety.LoopFrames

/-! `FillWords` writes `count` words through a caller reference. The loop invariant states only
    the filled prefix; the loop state carries the frame facts, proved at each step. -/

open CIL.Safety
open CIL (W32 W64)
namespace ExampleProof

/-- The loop guard compares the index, below the count, against the count. -/
private def guard : Nat := instructionLocation Extracted.method0 fun op =>
  match op with | .blt _ => true | _ => false

bind_entry entry (initial : Memory) (base : Reference) (v : W64) (n : W32)
    (formed : initial.WellFormed) := Extracted.method0
  with [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)] from initial
  allocating formed

/-- The index, held by the frame's only local, with the frame facts for the words written. -/
private abbrev State (initial : Memory) (base home : Reference) (n : W32) :=
  FrameState [(base, 8 * n.toNat)] initial [.word32] [.bytes .word32 home] W32 fun k => [.i32 k]

private def header (initial : Memory) (base home : Reference) (n : W32)
    (state : State initial base home n) : LoopState :=
  ⟨guard, entry.frame initial home, [.scalar (.i32 n), .scalar (.i32 state.values)], state.memory⟩

/-- The first `k` words are filled and the rest stay writable. -/
private def invariant (initial : Memory) (base home : Reference) (v : W64) (n : W32)
    (state : State initial base home n) : Prop :=
  Filled state.memory base 8 (List.replicate state.values.toNat (v : BitVec (8 * 8)))
    (n.toNat - state.values.toNat) ∧ state.values.toNat ≤ n.toNat

/-- `FillWords` fills `count` words from write authority alone and changes no other caller byte. -/
theorem fill_words (initial : Memory) (base : Reference) (v : W64) (n : W32) (formed : initial.WellFormed)
    (valid : form initial base = .ok base) (small : n.toNat < 2^31) (writable : Writable initial base 8 0 n.toNat) :
    ∃ fuel final, invoke Extracted.program fuel 0 [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)]
        initial = .ok (final, []) ∧
      Contents final base 8 (List.replicate n.toNat (v : BitVec (8 * 8))) ∧
      Confined [(base, 8 * n.toNat)] initial final := by
  obtain ⟨home, entered, setup, -, entryMemory, entryFrame⟩ :=
    entry.checked initial base v n formed
  have old := formed.form_bound valid
  obtain ⟨m0, stored0, frame0, below0⟩ := (entryFrame [(base, 8 * n.toNat)]).store 0 (.i32 0) rfl
  have loaded0 := frame0.load 0
  have room := (writable.after_below entryMemory.kept old).after_below below0 old
  refine invoke_loop_results (by rfl) ?_ setup (header initial base home n)
    (invariant initial base home v n) (fun s => n.toNat - s.values.toNat) ⟨0, m0, frame0⟩
    (by cil_loop_steps [entry.frame, header, guard, stored0, loaded0])
    ⟨by simpa using Filled.start room, by simp⟩ ?_
  · simp [checkedValue, formValue, checkedAt, valid, numericValue, Except.mapError, Bind.bind,
      Except.bind, Pure.pure, Except.pure, List.mapM_cons, List.mapM_nil]
  rintro ⟨k, m, frame⟩ ⟨filled, bounded⟩
  dsimp only at filled bounded
  have loaded := frame.load 0
  by_cases exit : k.toNat = n.toNat
  · left
    obtain rfl : k = n := BitVec.eq_of_toNat_eq exit
    obtain ⟨framed, below⟩ := frame.leave setup
    have stays : ¬ k.toInt < k.toInt := Int.lt_irrefl _
    cil_loop_finish [entry.frame, header, guard, loaded, stays]
    exact loop_terminates_return (op := .ret none) (by first | (simp only [cil_code]; rfl) | rfl)
      (by first | (simp only [cil_code]; rfl) | rfl)
      (by cil_checked_step [CIL.truth]) rfl ⟨⟨filled.1.after_below below old, framed⟩, rfl⟩
  · have lower : k.toNat < n.toNat := by omega
    obtain ⟨m1, target, stored, pushed⟩ := filled.write_next (by omega) (v : BitVec (8 * 8))
    simp only [List.length_replicate] at target stored
    have baseForm := frame.form valid old
    have frame1 := frame.write_element stored (List.mem_singleton_self _) lower old
    obtain ⟨m2, stored2, frame2, below2⟩ := frame1.store 0 (.i32 (k + 1)) rfl
    cil_loop_continue ⟨k + 1, m2, frame2⟩ [header, guard, int_lt small lower, baseForm,
      add_int_element frame.wellFormed baseForm (by omega) target, step_store64_of_write stored,
      loaded, frame1.load 0, stored2, frame2.load 0, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    all_goals simp only [invariant, toNat_succ lower]
    · rw [List.replicate_succ', show n.toNat - (k.toNat + 1) = n.toNat - k.toNat - 1 by omega]
      exact ⟨pushed.after_below below2 old, by omega⟩
    · omega

/-- Every nonnegative count fills exactly that many words, whatever the buffer held before. -/
theorem correctness : Ensures Extracted.program 0
    (fun args initial => ∃ base v n, args = [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)] ∧
      initial.WellFormed ∧ form initial base = .ok base ∧ n.toNat < 2^31 ∧ Writable initial base 8 0 n.toNat)
    (fun args initial final values => values = [] ∧ ∀ base v n,
      args = [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)] →
      Contents final base 8 (List.replicate n.toNat (v : BitVec (8 * 8))) ∧
        Confined [(base, 8 * n.toNat)] initial final) := by
  rintro args initial ⟨base, v, n, rfl, formed, valid, small, writable⟩
  obtain ⟨fuel, final, executed, contents, framed⟩ := fill_words initial base v n formed valid small writable
  refine ⟨fuel, final, [], executed, rfl, ?_⟩
  intro other value count same
  simp only [List.cons.injEq, Value.reference.injEq, ManagedReference.address.injEq, Value.scalar.injEq,
    CIL.Value.i64.injEq, CIL.Value.i32.injEq, and_true] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact ⟨contents, framed⟩

#print axioms correctness

end ExampleProof
