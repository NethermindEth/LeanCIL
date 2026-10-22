import CIL.Safety.MethodContract
import CIL.Safety.ConfinedSnapshots

/-! Footprint reasoning for `Confined` contracts, checked without an extraction. -/
namespace Tests.ConfinedFootprints

open CIL.Safety

/-- Per-word facts close a word footprint of any arity in one `simp` call. -/
theorem outside_three_words {r q s : Reference} {id offset : Nat} (hr : OutsideWord r id offset)
    (hq : OutsideWord q id offset) (hs : OutsideWord s id offset) :
    Outside [(r, 8), (q, 8), (s, 8)] id offset := by
  simpa using ⟨hr, hq, hs⟩

theorem outside_three_words_term {r q s : Reference} {id offset : Nat} (hr : OutsideWord r id offset)
    (hq : OutsideWord q id offset) (hs : OutsideWord s id offset) :
    Outside [(r, 8), (q, 8), (s, 8)] id offset :=
  Outside.word hr (Outside.word hq (Outside.word hs (Outside.nil _ _)))

/-- A byte of any listed word is inside the footprint, wherever the other words lie. -/
theorem inside_listed_word (r q : Reference) (i : Nat) (bound : i < 8) :
    ¬ Outside [(q, 8), (r, 8)] r.allocation (r.offset + i) := by
  simp only [Outside.cons, Outside.nil, and_true]
  omega

/-- Four limb writes stay inside one 32-byte output; the last ends exactly at its boundary. -/
theorem four_limbs_confined {m m1 m2 m3 m4 : Memory} {out : Reference} {w0 w1 w2 w3 : BitVec 64}
    (s0 : write m out (numberBytes w0.toNat 8) 1 = .ok m1)
    (s1 : write m1 ⟨out.allocation, out.offset + 8⟩ (numberBytes w1.toNat 8) 1 = .ok m2)
    (s2 : write m2 ⟨out.allocation, out.offset + 16⟩ (numberBytes w2.toNat 8) 1 = .ok m3)
    (s3 : write m3 ⟨out.allocation, out.offset + 24⟩ (numberBytes w3.toNat 8) 1 = .ok m4) :
    Confined [(out, 32)] m m4 := by
  refine (((Confined.write_within s0 ?_).trans (Confined.write_within s1 ?_)).trans
    (Confined.write_within s2 ?_)).trans (Confined.write_within s3 ?_) <;>
    exact ⟨_, List.mem_singleton_self _, by simp [Within, numberBytes] <;> omega⟩

/-- Overlapping entries need no disjointness: each write lies inside one of them. -/
theorem overlapping_entries_confined {m m1 m2 : Memory} {out : Reference} {w0 w1 : BitVec 64}
    (s0 : write m ⟨out.allocation, out.offset + 4⟩ (numberBytes w0.toNat 8) 1 = .ok m1)
    (s1 : write m1 ⟨out.allocation, out.offset + 12⟩ (numberBytes w1.toNat 8) 1 = .ok m2) :
    Confined [(out, 16), (⟨out.allocation, out.offset + 8⟩, 16)] m m2 :=
  (Confined.write_within s0 ⟨_, List.mem_cons_self .., by simp [Within, numberBytes]⟩).trans
    (Confined.write_within s1 ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      by simp [Within, numberBytes]⟩)

/-- Coverage is exact: one byte past the boundary is not inside the region. -/
theorem past_boundary_not_within (out : Reference) :
    ¬ Within (⟨out.allocation, out.offset + 25⟩, 8) (out, 32) := by
  simp [Within]

/-- A region in another allocation is not coverage, even at identical offsets. -/
theorem other_allocation_not_within {out : Reference} {other : Nat} (different : other ≠ out.allocation) :
    ¬ Within (⟨other, out.offset⟩, 8) (out, 32) := by
  simp [Within, different]

/-- Concrete coverage is decided: the last limb fits, one byte further or another allocation does not. -/
theorem concrete_coverage : Within (⟨0, 24⟩, 8) (⟨0, 0⟩, 32) ∧ ¬ Within (⟨0, 25⟩, 8) (⟨0, 0⟩, 32) ∧
    ¬ Within (⟨1, 0⟩, 8) (⟨0, 0⟩, 32) := by
  decide

/-- A write initializing an old byte outside the footprint refutes confinement. -/
theorem write_escapes {m result : Memory} {r : Reference} {bytes : List (BitVec 8)}
    {footprint : List (Reference × Nat)} {i : Nat} (h : write m r bytes 1 = .ok result) (index : i < bytes.length)
    (old : r.allocation < m.nextIdentity) (fresh : (m.cells r.allocation (r.offset + i)).initialized = false)
    (outside : Outside footprint r.allocation (r.offset + i)) : ¬ Confined footprint m result := by
  intro framed
  have kept := framed.cells _ old _ outside
  rw [write_initializes _ _ _ _ _ _ h index] at kept
  simp [← kept] at fresh

/-- No rule can confine a write one byte past the region when that byte was uninitialized. -/
theorem past_boundary_unconfined {m result : Memory} {out : Reference} {w : BitVec 64}
    (h : write m ⟨out.allocation, out.offset + 25⟩ (numberBytes w.toNat 8) 1 = .ok result)
    (old : out.allocation < m.nextIdentity) (fresh : (m.cells out.allocation (out.offset + 32)).initialized = false) :
    ¬ Confined [(out, 32)] m result :=
  write_escapes (i := 7) h (by simp [numberBytes]) old fresh (by simp)

/-- No rule can count a write to another allocation as inside the region. -/
theorem other_allocation_unconfined {m result : Memory} {out : Reference} {other : Nat} {w : BitVec 64}
    (different : other ≠ out.allocation)
    (h : write m ⟨other, out.offset⟩ (numberBytes w.toNat 8) 1 = .ok result)
    (old : other < m.nextIdentity) (fresh : (m.cells other out.offset).initialized = false) :
    ¬ Confined [(out, 32)] m result :=
  write_escapes (i := 0) h (by simp [numberBytes]) old fresh (by simp [different])

/-- A 32-byte input beside the carry word and a completed result beside the output survive a carry call. -/
theorem carry_call_keeps_snapshots {before after : Memory} {carry output input done : Reference}
    {inputBytes doneBytes : List (BitVec 8)}
    (framed : Confined [(carry, 8), (output, 8)] before after) (formed : before.WellFormed)
    (loadedInput : read before input 32 1 = .ok inputBytes) (loadedDone : read before done 8 1 = .ok doneBytes)
    (inputCarry : input.offset + 32 ≤ carry.offset) (inputOutput : input.allocation ≠ output.allocation)
    (doneCarry : done.allocation ≠ carry.allocation) (doneOutput : done.offset + 8 ≤ output.offset) :
    read after input 32 1 = .ok inputBytes ∧ read after done 8 1 = .ok doneBytes :=
  ⟨framed.read_apart formed loadedInput (by simp [Apart, *]),
    framed.read_apart formed loadedDone (by simp [Apart, *])⟩

/-- Private word homes in other allocations keep their remembered words across the call. -/
theorem carry_call_keeps_words {before after : Memory} {carry output first second : Reference}
    {known : Nat → Option (BitVec 64)}
    (snapshots : WordSnapshots before [.bytes .word64 first, .bytes .word64 second] known)
    (framed : Confined [(carry, 8), (output, 8)] before after) (formed : before.WellFormed)
    (firstApart : ∀ entry ∈ [(carry, 8), (output, 8)], Apart first 8 entry)
    (secondApart : ∀ entry ∈ [(carry, 8), (output, 8)], Apart second 8 entry) :
    WordSnapshots after [.bytes .word64 first, .bytes .word64 second] known :=
  snapshots.after_confined framed formed fun index _ reference _ slot => by
    rcases index with _ | _ | _ <;> simp at slot <;> subst slot <;> assumption

/-- An input allocation the footprint never names keeps every byte. -/
theorem carry_call_keeps_allocation {before after : Memory} {carry output input : Reference}
    (framed : Confined [(carry, 8), (output, 8)] before after) (old : input.allocation < before.nextIdentity)
    (inputCarry : input.allocation ≠ carry.allocation) (inputOutput : input.allocation ≠ output.allocation) :
    (fun offset => after.cells input.allocation offset) = (fun offset => before.cells input.allocation offset) :=
  funext (framed.cells_apart old (by simp [*]))

/-- A snapshot overlapping the footprint by one byte does not meet the preservation premise. -/
theorem overlapping_not_apart (output : Reference) :
    ¬ ∀ entry ∈ [(output, 8)], Apart ⟨output.allocation, output.offset + 7⟩ 8 entry := by
  simp [Apart]
  omega

/-- A confined call can change a snapshot of its own footprint, so only a postcondition may restore it. -/
theorem footprint_snapshot_changes {m result : Memory} {output : Reference} {old new : List (BitVec 8)}
    (h : write m output new 1 = .ok result) (width : new.length = 8) (differ : new ≠ old) :
    Confined [(output, 8)] m result ∧ read result output 8 1 ≠ .ok old := by
  refine ⟨Confined.write h (by simp [width]), fun same => differ ?_⟩
  have readback := write_readback _ _ _ _ _ h
  rw [width, same] at readback
  exact (Except.ok.inj readback).symm

/-- A confined call never makes an uninitialized byte outside its footprint readable. -/
theorem uninitialized_stays_unreadable {before after : Memory} {footprint : List (Reference × Nat)}
    {r : Reference} {width alignment i : Nat} (framed : Confined footprint before after)
    (old : r.allocation < before.nextIdentity) (apart : ∀ entry ∈ footprint, Apart r width entry)
    (index : i < width) (fresh : (before.cells r.allocation (r.offset + i)).initialized = false)
    (bytes : List (BitVec 8)) : read after r width alignment ≠ .ok bytes := by
  intro loaded
  have ready := read_requires_initialization _ _ _ _ _ loaded i (List.mem_range.mpr index)
  rw [framed.cells _ old _ (Outside.of_apart apart i index)] at ready
  simp [ready] at fresh

#print axioms outside_three_words
#print axioms outside_three_words_term
#print axioms inside_listed_word
#print axioms four_limbs_confined
#print axioms overlapping_entries_confined
#print axioms past_boundary_not_within
#print axioms other_allocation_not_within
#print axioms concrete_coverage
#print axioms write_escapes
#print axioms past_boundary_unconfined
#print axioms other_allocation_unconfined
#print axioms carry_call_keeps_snapshots
#print axioms carry_call_keeps_words
#print axioms carry_call_keeps_allocation
#print axioms overlapping_not_apart
#print axioms footprint_snapshot_changes
#print axioms uninitialized_stays_unreadable

end Tests.ConfinedFootprints
