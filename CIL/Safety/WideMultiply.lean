import CIL.Safety.WordMemory

namespace CIL.Safety

/-- Exact unsigned 128-bit multiplication: checked low-word write and high-word return. -/
theorem bigMul64_of_write (memory result : Memory) (reference : Reference)
    (left right : CIL.W64) (rest : List Value)
    (stored : write memory reference (numberBytes (left * right).toNat 8) 1 = .ok result) :
    memoryInstruction .bigMul64
      (.reference (.address reference) :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory =
      .ok (result, .scalar (.i64 (CIL.WideMultiply.high64 left right)) :: rest) := by
  simp only [memoryInstruction, storeValue, referenceAt, checkedAt, stored,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Write permission is sufficient; the out location need not be initialized.
    No allocation or cell outside its eight bytes changes. -/
theorem bigMul64_succeeds (memory : Memory) (reference : Reference)
    (left right : CIL.W64) (rest : List Value)
    (writable : access memory reference 8 1 true = .ok ()) :
    ∃ result,
      memoryInstruction .bigMul64
        (.reference (.address reference) :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory =
        .ok (result, .scalar (.i64 (CIL.WideMultiply.high64 left right)) :: rest) ∧
      loadValue result (.address reference) 8 = .ok (.i64 (left * right)) ∧
      result.allocations = memory.allocations ∧
      ∀ id offset, id ≠ reference.allocation ∨ offset < reference.offset ∨ reference.offset + 8 ≤ offset →
        result.cells id offset = memory.cells id offset := by
  have width : (numberBytes (left * right).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨result, stored⟩ := write_succeeds (bytes := numberBytes (left * right).toNat 8)
    (by simpa only [width] using writable)
  refine ⟨result, bigMul64_of_write memory result reference left right rest stored, ?_,
    write_allocations _ _ _ _ _ stored, ?_⟩
  · apply load_word64_of_read
    simpa only [width] using write_readback _ _ _ _ _ stored
  · intro id offset outside
    exact write_outside _ _ _ _ _ _ _ stored (by simpa only [width] using outside)

#print axioms bigMul64_of_write
#print axioms bigMul64_succeeds
end CIL.Safety
