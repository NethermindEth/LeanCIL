import CIL.Safety.StaticMemoryLemmas
import CIL.Safety.Relocation

/-!
# Typed static spans are aligned

CoreCLR's `RuntimeHelpers.CreateSpan<T>` throws `ArgumentException` unless the field data is
aligned to `sizeof(T)`. The checked interpreter admits `.createSpan width` only over a whole
static allocation whose guaranteed alignment `width` divides, so every successful typed span
starts at an address aligned to its element width under every valid placement.
-/

namespace CIL.Safety

/-- `staticSpanAligned` holds exactly when the element width is positive and divides the
    allocation's guaranteed alignment. -/
theorem staticSpanAligned_divides {allocation : Allocation} {width : Nat}
    (aligned : staticSpanAligned allocation width = true) :
    0 < width ∧ width ∣ allocation.layout.alignment := by
  simp only [staticSpanAligned, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at aligned
  exact ⟨aligned.1, Nat.dvd_of_mod_eq_zero aligned.2⟩

/-- A successful typed static span starts a live allocation whose guaranteed alignment is a
    multiple of the element width. -/
theorem createSpan_aligned {body : CIL.Method} {pc width : Nat} {stack values : List Value}
    {m result : Memory}
    (created : staticInstruction body pc (.createSpan width) stack m = .ok (result, values)) :
    ∃ (reference : Reference) (rest : List Value) (allocation : Allocation),
      stack = .reference (.address reference) :: rest ∧ reference.offset = 0 ∧
      m.allocations reference.allocation = some allocation ∧ allocation.live = true ∧
      0 < width ∧ width ∣ allocation.layout.alignment := by
  unfold staticInstruction at created
  split at created <;> try contradiction
  · rename_i reference rest same
    cases same
    cases live : liveAllocation m reference.allocation with
    | error fault => simp [live, checkedAt, Except.mapError, Bind.bind, Except.bind] at created
    | ok allocation =>
      have present : m.allocations reference.allocation = some allocation ∧
          allocation.live = true := by
        unfold liveAllocation at live
        cases found : m.allocations reference.allocation <;> simp only [found] at live
        · cases live
        · split at live <;> simp_all [Pure.pure, Except.pure]
      simp only [live, checkedAt, Except.mapError, Bind.bind, Except.bind] at created
      split at created
      · rename_i whole
        simp only [Bool.and_eq_true, beq_iff_eq] at whole
        split at created
        · exact ⟨reference, rest, allocation, rfl, whole.1.1.2, present.1, present.2,
            staticSpanAligned_divides (by assumption)⟩
        · cases created
      · cases created
  · unfold memoryInstruction at created
    split at created
    · cases created
    · unfold otherMemoryInstruction at created
      split at created <;> simp_all

/-- Under every valid placement, a successful typed static span's base address is a multiple
    of its element width, which is the condition CoreCLR's `CreateSpan<T>` enforces. -/
theorem createSpan_aligned_at_placement {body : CIL.Method} {pc width : Nat}
    {stack values : List Value} {m result : Memory}
    (created : staticInstruction body pc (.createSpan width) stack m = .ok (result, values))
    (placement : Placement) (placed : placement.Valid m) :
    ∃ (reference : Reference) (rest : List Value),
      stack = .reference (.address reference) :: rest ∧ 0 < width ∧
      (placement reference.allocation + reference.offset) % width = 0 := by
  obtain ⟨reference, rest, allocation, shape, offset, present, live, positive, divides⟩ :=
    createSpan_aligned created
  have base := (placed.1 reference.allocation allocation present live).2.2
  refine ⟨reference, rest, shape, positive, ?_⟩
  rw [offset, Nat.add_zero]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans divides (Nat.dvd_of_mod_eq_zero base))

/-- A width that divides the declared alignment is admitted; a wider element is not. -/
example : staticSpanAligned ⟨.immutableStatic, ⟨32, 4, []⟩, true, [32]⟩ 4 = true := rfl
example : staticSpanAligned ⟨.immutableStatic, ⟨32, 2, []⟩, true, [32]⟩ 4 = false := rfl
example : staticSpanAligned ⟨.immutableStatic, ⟨32, 8, []⟩, true, [32]⟩ 0 = false := rfl

#print axioms staticSpanAligned_divides
#print axioms createSpan_aligned
#print axioms createSpan_aligned_at_placement

end CIL.Safety
