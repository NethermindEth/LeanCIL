import CIL.Safety.MethodContract

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

end Tests.ConfinedFootprints
