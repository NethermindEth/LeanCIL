import CIL.Safety.LiteralImage

/-! Checked string loads after literal image initialization. -/
namespace Tests.PercentRuntime.Startup
open CIL.Extraction CIL.Safety CIL.Safety.LiteralImage

/-- The loader accepts every representable string from empty caller memory, and the original
    ldstr loads a non-null reference without changing the initialized state. -/
theorem fromEmpty (text : String) (stack : List Value)
    (lengthFits : (CIL.utf16Units text).length ≤ 0x7fffffff) :
    ∃ memory, intern Memory.empty text = .ok (⟨0,0⟩, memory) ∧
      intern memory text = .ok (⟨0,0⟩, memory) ∧ memory.nextIdentity = 1 ∧
      memory.heapBudget = 0 ∧
      stringLiteralInstruction text stack memory =
        .ok (memory, .object (.address ⟨0,0⟩) :: stack) := by
  have fits : (bytesOfString text).length < nativeLimit := by
    rw [storageSize]; unfold nativeLimit; omega
  have valid := validStorage text fits
  simp only [intern, Memory.empty, List.lookup_nil, Nat.not_lt.mpr lengthFits, ↓reduceIte,
    allocate, valid, Bool.not_true, Bool.false_eq_true, Option.isSome_none, bind, Except.bind,
    pure, Except.pure]
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · simp [loaded]
  · simp [stringLiteralInstruction, literalObject, loaded, formObject, liveAllocation, storage,
      checkedAt, Except.mapError, bind, Except.bind, pure, Except.pure]
#print axioms fromEmpty

/-- Loading both constructor literals from empty caller memory aliases equal texts and gives
    distinct texts separate live references. Neither operation consumes the method's heap quota. -/
theorem constructorLiterals (name message : String)
    (nameFits : (CIL.utf16Units name).length ≤ 0x7fffffff)
    (messageFits : (CIL.utf16Units message).length ≤ 0x7fffffff) :
    ∃ first final, intern Memory.empty name = .ok (⟨0, 0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1, 0⟩, final) ∧
      final.heapBudget = 0 ∧
      stringLiteralInstruction name [] final = .ok (final, [.object (.address ⟨0,0⟩)]) ∧
      stringLiteralInstruction message [] final =
        .ok (final, [.object (.address ⟨if name = message then 0 else 1, 0⟩)]) := by
  by_cases same : name = message
  · subst message
    obtain ⟨first, installed, reused, _, budget, loaded⟩ := fromEmpty name [] nameFits
    exact ⟨first, first, installed, by simpa using reused, budget, loaded, by simpa using loaded⟩
  · have valid (text : String) (lengthFits : (CIL.utf16Units text).length ≤ 0x7fffffff) :
        (storage (bytesOfString text)).valid = true := by
      apply validStorage
      rw [storageSize]; unfold nativeLimit; omega
    have unequal := Ne.symm same
    have different : (message == name) = false := by simpa using unequal
    have reverse : (name == message) = false := by simpa using same
    obtain ⟨first, installed, _, _, _, _⟩ := fromEmpty name [] nameFits
    refine ⟨first, ?_⟩
    simp only [installed, true_and]
    simp only [intern, Memory.empty, List.lookup_nil, Nat.not_lt.mpr nameFits, ↓reduceIte,
      allocate, valid name nameFits, Bool.not_true, Bool.false_eq_true, Option.isSome_none,
      bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and] at installed
    subst first
    simp [-List.length_flatMap, intern, loaded, List.lookup, different, same,
      Nat.not_lt.mpr messageFits, allocate,
      valid message messageFits, bind, Except.bind, pure, Except.pure]
    simp [stringLiteralInstruction, literalObject, List.lookup, formObject, liveAllocation,
      storage, checkedAt, Except.mapError, reverse, bind, Except.bind, pure, Except.pure]
#print axioms constructorLiterals
end Tests.PercentRuntime.Startup
