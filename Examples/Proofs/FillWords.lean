import Extracted
import Examples.Support
import CIL.Verification
import CIL.Safety.NumericLocals
import CIL.Safety.LoopAutomation
import CIL.Safety.ReturnMemory
import CIL.Safety.BufferContents

open CIL.Safety
open CIL (W32 W64)
namespace ExampleProof

/-- The loop guard compares the index, below the count, against the count. -/
private def guard : Nat := instructionLocation Extracted.method0 fun op =>
  match op with | .blt _ => true | _ => false

section Loop

variable (initial : Memory) (base home : Reference) (v : W64) (n : W32)

private def frame : Frame := ⟨initial.nextIdentity, [.bytes .word32 home], [home.allocation], []⟩

private def header (state : W32 × Memory) : LoopState :=
  ⟨guard, frame initial home, [.scalar (.i32 n), .scalar (.i32 state.1)], state.2⟩

/-- The index home holds `k`, the first `k` words are filled and the rest stay writable. -/
private def invariant (state : W32 × Memory) : Prop :=
  read state.2 home 4 1 = .ok (numberBytes state.1.toNat 4) ∧
  access state.2 home 4 1 true = .ok () ∧
  Filled state.2 base 8 (List.replicate state.1.toNat (v : BitVec (8 * 8))) (n.toNat - state.1.toNat) ∧
  state.1.toNat ≤ n.toNat ∧ state.2.WellFormed ∧ form state.2 base = .ok base ∧
  Confined [(base, 8 * n.toNat)] initial state.2

end Loop

/-- Writes leave formation unchanged. -/
private theorem form_after_write {m after : Memory} {r q : Reference} {bytes : List (BitVec 8)}
    (written : write m r bytes 1 = .ok after) (valid : form m q = .ok q) : form after q = .ok q := by
  simpa only [form, liveAllocation, write_allocations _ _ _ _ _ written] using valid

/-- A write to the index home, allocated after the caller's memory, is confined to any caller footprint. -/
private theorem home_confined {initial m after : Memory} {home : Reference} {footprint : List (Reference × Nat)}
    {bytes : List (BitVec 8)} (framed : Confined footprint initial m) (fresh : initial.nextIdentity ≤ home.allocation)
    (written : write m home bytes 1 = .ok after) : Confined footprint initial after := by
  have own : Confined ((home, bytes.length) :: footprint) m after :=
    Confined.write written (List.mem_cons_self ..)
  have widened : Confined ((home, bytes.length) :: footprint) initial m :=
    framed.widen fun entry member => List.mem_cons_of_mem _ member
  exact (Confined.forget_fresh (fresh := [(home, bytes.length)]) (widened.trans own)
    (by simpa using fresh))

/-- A nonnegative `int` index is its natural value as a signed native offset. -/
private theorem offset_index {k : W32} (small : k.toNat < 2^31) :
    BitVec.ofInt 64 k.toInt = BitVec.ofNat 64 k.toNat := by
  have : k.toInt = (k.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp [show 2 * k.toNat < 2^32 by omega]
  rw [this, BitVec.ofInt_natCast]

private theorem terminates (initial : Memory) (base home : Reference) (v : W64) (n : W32)
    (args : List CIL.Safety.Value) (fresh : initial.nextIdentity ≤ home.allocation)
    (old : base.allocation < initial.nextIdentity) (small : n.toNat < 2^31)
    (arguments : args = [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)])
    (state : W32 × Memory) (valid : invariant initial base home v n state) :
    LoopTerminates Extracted.program 0 args (fun final values => values = [] ∧
        Contents final base 8 (List.replicate n.toNat (v : BitVec (8 * 8))) ∧
        Confined [(base, 8 * n.toNat)] initial final)
      (header initial home n state) := by
  subst arguments
  apply loop_terminates Extracted.program 0 _ (header initial home n) (invariant initial base home v n)
    (fun s => n.toNat - s.1.toNat) _ ?_ state valid
  rintro ⟨k, m⟩ ⟨readHome, writableHome, filled, bounded, formed, valid, framed⟩
  dsimp only at readHome writableHome filled bounded formed valid framed
  have loaded := load_numeric_local .word32 (.i32 k) k.toNat rfl readHome
  simp only [localResult] at loaded
  have homeApart : home.allocation ≠ base.allocation := Nat.ne_of_gt (Nat.lt_of_lt_of_le old fresh)
  by_cases exit : k.toNat = n.toNat
  · left
    have same : k = n := BitVec.eq_of_toNat_eq exit
    subst same
    have stays : ¬ k.toInt < k.toInt := Int.lt_irrefl _
    have below := leaveFrame_preserves_memory_below (frame initial home) m initial.nextIdentity
      (by intro id member; change id ∈ [home.allocation] at member; rw [List.mem_singleton.mp member]; exact fresh)
    cil_loop_finish [frame, header, guard, loaded, stays]
    refine loop_terminates_return (op := .ret none) (by first | (simp only [cil_code]; rfl) | rfl)
      (by first | (simp only [cil_code]; rfl) | rfl)
      (by cil_checked_step [CIL.truth]) rfl ⟨rfl, filled.1.after_below below old, ?_⟩
    exact framed.then_below below (by rw [leaveFrame_nextIdentity]; exact Nat.le_refl _)
  · right
    have lower : k.toNat < n.toNat := by omega
    have kSmall : k.toNat < 2^31 := by omega
    have inside : k.toInt < n.toInt := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
      simp only [show 2 * k.toNat < 2^32 by omega, show 2 * n.toNat < 2^32 by omega, ite_true]
      omega
    have next : (k + 1).toNat = k.toNat + 1 := by
      have one : (1 : BitVec 32).toNat = 1 := rfl
      simp only [BitVec.toNat_add, one]
      omega
    obtain ⟨contents, writable⟩ := filled
    have room : Writable m base 8 (List.replicate k.toNat (v : BitVec (8 * 8))).length
        ((n.toNat - k.toNat - 1) + 1) := by
      rw [show n.toNat - k.toNat - 1 + 1 = n.toNat - k.toNat by omega]
      exact writable
    have target := room 0 (by omega)
    simp only [List.length_replicate, Nat.add_zero] at target
    have addressed : add m base 8 (BitVec.ofInt 64 k.toInt) = .ok (base.element 8 k.toNat) := by
      rw [offset_index kSmall]
      exact add_element formed valid target
    obtain ⟨m1, written⟩ := room.write_succeeds (v : BitVec (8 * 8))
    have stored : write m (base.element 8 k.toNat) (numberBytes v.toNat 8) 1 = .ok m1 := by
      simpa only [List.length_replicate] using written
    have pushed := Filled.push ⟨contents, room⟩ written
    have homeRead1 := write_preserves_disjoint_read stored readHome (Or.inl homeApart)
    have loaded1 := load_numeric_local .word32 (.i32 k) k.toNat rfl homeRead1
    simp only [localResult] at loaded1
    obtain ⟨_, homeReady⟩ := access_requirements writableHome
    have writableHome1 := (homeReady.after_write stored).access
    obtain ⟨m2, written2, stored2, bytes2⟩ := store_numeric_local .word32 (.i32 (k + 1))
      (k + 1).toNat rfl writableHome1
    simp only [localWidth] at written2 bytes2
    have loaded2 := load_numeric_local .word32 (.i32 (k + 1)) (k + 1).toNat rfl bytes2
    simp only [localResult] at loaded2
    have formed1 := write_preserves_wellFormed _ _ _ _ _ formed stored
    have storedStep := stored2
    have loadedStep := loaded2
    simp only [BitVec.ofNat_eq_ofNat] at storedStep loadedStep
    have addStep (body : CIL.Method) (pc : Nat) (args : List Value) (f : Frame) :
        step body (.memory (.add 8 true)) pc args f [.scalar (.i32 k), .reference (.address base)] m =
          .ok (.next (pc + 1) [.reference (.address (base.element 8 k.toNat))] f m) := by
      simp only [step, staticInstruction, memoryInstruction, CIL.offsetValue, referenceAt, addressed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have storeStep (body : CIL.Method) (pc : Nat) (args : List Value) (f : Frame) :
        step body .store64 pc args f [.scalar (.i64 v), .reference (.address (base.element 8 k.toNat))] m =
          .ok (.next (pc + 1) [] f m1) := by
      simp only [step, pureArity, instruction, storeValue, referenceAt, ordinaryAccessAlignment, stored, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have path : LoopReaches Extracted.program 0
        [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)] (header initial home n (k, m))
        (header initial home n (k + 1, m2)) := by
      -- The checked stepper unfolds `step`, so the two memory instructions are crossed by their own equations.
      cil_loop_steps [frame, header, guard, loaded, inside, valid, formValue, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      refine loop_reaches_next (by first | (simp only [cil_code]; rfl) | rfl)
        (by first | (simp only [cil_code]; rfl) | rfl) (addStep _ _ _ _) ?_
      cil_loop_steps [frame, header, guard]
      refine loop_reaches_next (by first | (simp only [cil_code]; rfl) | rfl)
        (by first | (simp only [cil_code]; rfl) | rfl) (storeStep _ _ _ _) ?_
      cil_loop_steps [frame, header, guard, loaded1, storedStep, loadedStep, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append]
    obtain ⟨cost, segment⟩ := path
    refine ⟨(k + 1, m2), cost, ⟨bytes2, ((homeReady.after_write stored).after_write written2).access, ?_, ?_,
      write_preserves_wellFormed _ _ _ _ _ formed1 written2, form_after_write written2 (form_after_write stored valid),
      ?_⟩, ?_, segment⟩
    · have grown : List.replicate k.toNat (v : BitVec (8 * 8)) ++ [v] = List.replicate (k + 1).toNat v := by
        rw [next, List.replicate_succ']
      rw [grown] at pushed
      dsimp only
      rw [show n.toNat - (k + 1).toNat = n.toNat - k.toNat - 1 by omega]
      exact ⟨pushed.1.after_write_apart written2 (Or.inl (Ne.symm homeApart)), pushed.2.after_write written2⟩
    · dsimp only; omega
    · refine home_confined (framed.trans (Confined.write_within stored ⟨_, List.mem_singleton_self _, ?_⟩)) fresh
        written2
      simpa using base.element_run_within 8 (first := k.toNat) (count := 1) (outer := 0) (total := n.toNat)
        (Nat.zero_le _) (by omega)
    · dsimp only; omega

/-- `FillWords` fills `count` words from write authority alone and changes no other caller byte. -/
theorem fill_words (initial : Memory) (base : Reference) (v : W64) (n : W32) (formed : initial.WellFormed)
    (valid : form initial base = .ok base) (small : n.toNat < 2^31) (writable : Writable initial base 8 0 n.toNat) :
    ∃ fuel final, invoke Extracted.program fuel 0 [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)]
        initial = .ok (final, []) ∧
      Contents final base 8 (List.replicate n.toNat (v : BitVec (8 * 8))) ∧
      Confined [(base, 8 * n.toNat)] initial final := by
  obtain ⟨home, entered, made, _, homeWritable, preserved⟩ :=
    make_numeric_local initial initial.nextIdentity .word32 (.i32 0) 0 formed rfl
  have setup : enterFrame Extracted.method0 [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)]
      initial = .ok (frame initial home, entered) := by
    simp only [enterFrame, Extracted.method0_locals, Extracted.method0_localKinds, Extracted.method0_vectorArgs,
      Extracted.method0_parameterHomes, makeLocals, made, makeArgumentHomes, makeParameterHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.map_nil, List.append_nil]
  have fresh := (makeLocal_fresh _ _ _ _ _ _ _ made).2 home.allocation (by simp)
  have enteredWF := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ formed made
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ valid
  have old : base.allocation < initial.nextIdentity := (formed.1 _ _ present).1
  change access entered home 4 1 true = .ok () at homeWritable
  obtain ⟨m0, written0, stored0, bytes0⟩ := store_numeric_local .word32 (.i32 0) 0 rfl homeWritable
  simp only [localWidth] at written0 bytes0
  have loaded0 := load_numeric_local .word32 (.i32 0) 0 rfl bytes0
  simp only [localResult] at loaded0
  have storedStep := stored0
  have loadedStep := loaded0
  simp only [BitVec.ofNat_eq_ofNat] at storedStep loadedStep
  obtain ⟨_, homeReady⟩ := access_requirements homeWritable
  have enteredForm : form entered base = .ok base := by
    simpa only [form, liveAllocation, preserved.allocations _ old] using valid
  have start : invariant initial base home v n (0, m0) := by
    refine ⟨by simpa using bytes0, (homeReady.after_write written0).access, ?_, by simp,
      write_preserves_wellFormed _ _ _ _ _ enteredWF written0, form_after_write written0 enteredForm, ?_⟩
    · simpa using Filled.start (room := n.toNat) ((writable.after_below preserved old).after_write written0)
    · exact home_confined (Confined.ofMemoryBelow preserved (Nat.le_refl _)
        (Nat.le_of_lt (Nat.lt_of_le_of_lt fresh.1 fresh.2))) fresh.1 written0
  have entry : LoopReaches Extracted.program 0 [.reference (.address base), .scalar (.i64 v), .scalar (.i32 n)]
      ⟨0, frame initial home, [], entered⟩ (header initial home n (0, m0)) := by
    cil_loop_steps [frame, header, guard, storedStep, loadedStep]
  obtain ⟨fuel, final, values, executed, returned, contents, framed⟩ := loop_reaches_terminates entry
    (terminates initial base home v n _ fresh.1 old small rfl (0, m0) start)
  subst returned
  refine ⟨fuel, final, invoke_of_run (by rfl) ?_ setup executed, contents, framed⟩
  simp [checkedValue, formValue, checkedAt, valid, numericValue, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure, List.mapM_cons, List.mapM_nil]

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
