import CIL.Safety.LoopFrames

/-!
# Loop frame tests

The frame facts of a one-local loop frame survive a write to the caller's buffer and a call
confined to it, and the local still loads. A store through the local's own address, and a callee
whose footprint covers that home, are both rejected by the frame lemmas: each needs the write
in caller storage. Such a write can change the local, so the rejection is required: after it
the remembered value no longer holds.
-/

namespace Tests.LoopFrames

open CIL.Safety

variable {caller current after : Memory} {base home : Reference}

/-- The frame of a loop whose index local holds 5, over a caller buffer and the index home. -/
abbrev Indexed (caller current : Memory) (base home : Reference) : Prop :=
  LoopFrame [(base, 8 * 1), (home, 4)] caller current [.word32] [.bytes .word32 home]
    (knownLocals [.i32 5])

/-- A write of the caller's buffer keeps the frame, and the index still loads as 5. -/
theorem buffer_write_kept (frame : Indexed caller current base home)
    (old : base.allocation < caller.nextIdentity) {word : BitVec 64}
    (written : write current (base.element 8 0) (numberBytes word.toNat 8) 1 = .ok after) :
    loadLocal after (.bytes .word32 home) = .ok (.scalar (.i32 5)) :=
  (frame.write_element written (List.mem_cons_self ..) (by decide) old).load 0

/-- Writing 6 over a home remembered as holding 5 breaks its snapshot. -/
theorem overwritten_forgets
    (written : write current home (numberBytes 6 4) 1 = .ok after) :
    ¬ LocalSnapshots after [.bytes .word32 home] (knownLocals [.i32 5]) := by
  intro kept
  obtain ⟨kind, reference, stored, number, slot, fits, result, loaded⟩ := kept 0 _ rfl
  simp only [List.getElem?_cons_zero, Option.some.injEq, LocalSlot.bytes.injEq] at slot
  obtain ⟨rfl, rfl⟩ := slot
  have readback := write_readback _ _ _ _ _ written
  simp only [numberBytes_length, localWidth] at readback loaded
  rw [readback] at loaded
  cases stored <;> simp [localResult, localNumber, CIL.Value.hasUnspecified] at fits result
  subst result
  subst fits
  revert loaded
  simp only [Except.ok.injEq, BitVec.toNat_ofNat]
  decide

/-- A store through the index local's address is in the footprint, but the write lemma needs
    the target in caller storage, which the home is not, while the same lemma takes a store into
    the buffer; the home store does break the index. -/
theorem home_write_rejected {stored : Memory} (frame : Indexed caller current base home)
    (old : base.allocation < caller.nextIdentity)
    (buffered : write current base (numberBytes 7 4) 1 = .ok stored)
    (written : write current home (numberBytes 6 4) 1 = .ok after) :
    Indexed caller stored base home ∧
      ¬ LocalSnapshots after [.bytes .word32 home] (knownLocals [.i32 5]) := by
  fail_if_success
    have := frame.write written ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      by simp [Within, numberBytes_length]⟩ (by have := frame.homes.home_bound 0 _ _ rfl; omega)
  exact ⟨frame.write buffered
      ⟨_, List.mem_cons_self .., by simp [Within, numberBytes_length]⟩ old,
    overwritten_forgets written⟩

/-- A call confined to the caller's buffer keeps the frame, and the index still loads as 5. -/
theorem buffer_call_kept (frame : Indexed caller current base home)
    (old : base.allocation < caller.nextIdentity)
    (called : Confined [(base, 8 * 1)] current after) (formed : after.WellFormed) :
    loadLocal after (.bytes .word32 home) = .ok (.scalar (.i32 5)) :=
  (frame.after_confined called formed
    (fun entry member => ⟨entry, by simp_all, by simp_all [Within]⟩)
    (fun entry member => by simp_all)).load 0

/-- A callee whose footprint covers the index home may change it, as this store does; the call
    lemma needs every callee entry in caller storage, so it does not apply, while it takes a
    callee confined to the buffer. -/
theorem home_call_rejected {returned : Memory} (frame : Indexed caller current base home)
    (old : base.allocation < caller.nextIdentity)
    (bufferCall : Confined [(base, 8 * 1)] current returned)
    (returnedFormed : returned.WellFormed)
    (written : write current home (numberBytes 6 4) 1 = .ok after) :
    Indexed caller returned base home ∧
      ¬ LocalSnapshots after [.bytes .word32 home] (knownLocals [.i32 5]) := by
  have called : Confined [(home, 4)] current after :=
    Confined.write written (by simp [numberBytes_length])
  have formed := write_preserves_wellFormed _ _ _ _ _ frame.wellFormed written
  fail_if_success
    have := frame.after_confined called formed
      (fun entry member => ⟨entry, by simp_all, by simp_all [Within]⟩)
      (fun entry member => by
        have := frame.homes.home_bound 0 _ _ rfl
        simp_all
        omega)
  exact ⟨frame.after_confined bufferCall returnedFormed
      (fun entry member => ⟨entry, by simp_all, by simp_all [Within]⟩)
      (fun entry member => by simp_all),
    overwritten_forgets written⟩

#print axioms buffer_write_kept
#print axioms overwritten_forgets
#print axioms home_write_rejected
#print axioms buffer_call_kept
#print axioms home_call_rejected

end Tests.LoopFrames
