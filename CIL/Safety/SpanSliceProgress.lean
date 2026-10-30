import CIL.Safety.SpanViewLemmas

/-! Checked slicing of a valid span succeeds for every contained subrange. -/

namespace CIL.Safety

/-- A formed span has a length representable by the runtime's signed length result. -/
theorem SpanView.length_bounded (view : SpanView) (memory : Memory)
    (valid : view.validate memory = .ok ()) : view.length < 2^31 := by
  by_cases width : 0 < view.width ∧ view.width < 2^64
  · by_cases large : view.length < 2^31
    · exact large
    · simp [SpanView.validate, width, large, Bind.bind, Except.bind, Pure.pure,
      Except.pure] at valid
  · simp [SpanView.validate, width, Bind.bind, Except.bind, Pure.pure, Except.pure] at valid
#print axioms SpanView.length_bounded

/-- The `int` length of a valid nonempty view is nonzero, so a `Length != 0` guard holds. -/
theorem SpanView.length_word_ne_zero (view : SpanView) (memory : Memory)
    (valid : view.validate memory = .ok ()) (nonempty : view.length ≠ 0) :
    BitVec.ofNat 32 view.length ≠ 0 := by
  have bounded := view.length_bounded memory valid
  intro zero
  have truncated := congrArg BitVec.toNat zero
  simp only [BitVec.toNat_ofNat] at truncated
  rw [Nat.mod_eq_of_lt (by omega)] at truncated
  exact nonempty truncated
#print axioms SpanView.length_word_ne_zero

/-- Subranges of a valid view retain its allocation, width and access mode. -/
theorem SpanView.slice_succeeds (view : SpanView) (memory : Memory) (start count : Nat)
    (valid : view.validate memory = .ok ())
    (inside : start + count ≤ view.length) :
    ∃ result, view.slice memory start count = .ok result ∧
      result.length = count ∧ result.width = view.width ∧ result.writable = view.writable := by
  have width : 0 < view.width ∧ view.width < 2^64 := by
    by_cases invalid : 0 < view.width ∧ view.width < 2^64
    · exact invalid
    · simp [SpanView.validate, invalid, Bind.bind, Except.bind, Pure.pure, Except.pure] at valid
  have length := view.length_bounded memory valid
  have startBound : start ≤ view.length := by omega
  have countBound : count ≤ view.length - start := by omega
  have countSmall : count < 2^31 := by omega
  cases reference : view.reference with
  | null =>
    have empty : view.length = 0 := by
      by_cases nonempty : view.length = 0
      · exact nonempty
      · simp [SpanView.validate, width, length, reference, nonempty, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at valid
    have startZero : start = 0 := by omega
    have countZero : count = 0 := by omega
    subst start count
    refine ⟨{ view with length := 0 }, ?_, rfl, rfl, rfl⟩
    simp [SpanView.slice, empty, reference, SpanView.validate, width,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  | address base =>
    cases live : liveAllocation memory base.allocation with
    | error fault =>
      simp [SpanView.validate, width, length, reference, live,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at valid
    | ok allocation =>
      have bounds : (base.offset < nativeLimit ∧
          base.offset + view.length * view.width < nativeLimit) ∧
          base.offset + view.length * view.width ≤ allocation.layout.size := by
        by_cases outside : (base.offset < nativeLimit ∧
            base.offset + view.length * view.width < nativeLimit) ∧
            base.offset + view.length * view.width ≤ allocation.layout.size
        · exact outside
        · simp [SpanView.validate, width, length, reference, live, outside,
          Bind.bind, Except.bind, Pure.pure, Except.pure] at valid
      have apart : ¬ allocation.layout.referenceSlots.any (fun slot =>
          decide (base.offset < slot.1 + slot.2 ∧
            slot.1 < base.offset + view.length * view.width)) = true := by
        intro overlap
        simp [SpanView.validate, width, length, reference, live, bounds, overlap,
          Bind.bind, Except.bind, Pure.pure, Except.pure] at valid
        obtain ⟨⟨offset, size⟩, member, overlaps⟩ := List.any_eq_true.mp overlap
        simp only [decide_eq_true_eq] at overlaps
        have := valid offset size member overlaps.1
        omega
      have subrange := Nat.mul_le_mul_right view.width inside
      rw [Nat.add_mul] at subrange
      have fits : base.offset + start * view.width + count * view.width < nativeLimit ∧
          base.offset + start * view.width + count * view.width ≤ allocation.layout.size := by
        omega
      have offsetSmall : base.offset + start * view.width < nativeLimit := by omega
      have noSlots : ¬ allocation.layout.referenceSlots.any (fun slot =>
          decide (base.offset + start * view.width < slot.1 + slot.2 ∧
            slot.1 < base.offset + start * view.width + count * view.width)) = true := by
        intro overlap
        apply apart
        obtain ⟨slot, member, overlaps⟩ := List.any_eq_true.mp overlap
        apply List.any_eq_true.mpr
        refine ⟨slot, member, ?_⟩
        simp only [decide_eq_true_eq] at overlaps ⊢
        omega
      let result : SpanView := { view with
        reference := .address { base with offset := base.offset + start * view.width }
        length := count }
      have formed : result.validate memory = .ok () := by
        simpa [SpanView.validate, result, width, countSmall, live,
          offsetSmall, fits.1, fits.2, Bind.bind, Except.bind, Pure.pure, Except.pure]
          using noSlots
      refine ⟨result, ?_, rfl, rfl, rfl⟩
      simp only [SpanView.slice, valid, reference, startBound, countBound,
        decide_true, Bool.true_and, ite_true, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
      change (result.validate memory >>= fun _ => Except.ok result) = Except.ok result
      rw [formed]
      rfl

#print axioms SpanView.slice_succeeds

end CIL.Safety
