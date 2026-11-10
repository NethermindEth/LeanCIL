import CIL.Safety.WordMemory
import CIL.Safety.MemorySteps

/-!
# Wide multiply

`Math.BigMul(ulong, ulong, out ulong)` and `Math.BigMul(long, long, out long)` as the
`bigMul64` memory instruction: each returns the unsigned or signed high word of the exact
128-bit product and writes the low word through the out reference, changing no other cell and
no allocation. `CIL.WideMultiply.signedHigh64_decomposition` recomposes the signed product.
-/

namespace CIL.Safety

/-- A checked low-word write is sufficient to step unsigned wide multiplication. The result
    retains the exact high-word expression used by arithmetic proofs. -/
theorem step_bigMul64_of_write {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory result : Memory} {reference : Reference} {left right : CIL.W64}
    (stored : write memory reference (numberBytes (left * right).toNat 8) 1 = .ok result) :
    step body (.memory (.bigMul64 false)) pc args frame
      (.reference (.address reference) :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest)
      memory = .ok (.next (pc + 1)
        (.scalar (.i64 (CIL.WideMultiply.high64 left right)) :: rest) frame result) := by
  rw [step_memory_bigMul64_eq]
  simp only [storeValue, CIL.Value.hasUnspecified, Bool.false_eq_true, ite_false, referenceAt,
    checkedAt, stored, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_bigMul64_of_write

/-- A checked low-word write steps signed wide multiplication with its exact signed high word. -/
theorem step_bigMul64_signed_of_write {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory result : Memory} {reference : Reference} {left right : CIL.W64}
    (stored : write memory reference (numberBytes (left * right).toNat 8) 1 = .ok result) :
    step body (.memory (.bigMul64 true)) pc args frame
      (.reference (.address reference) :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest)
      memory = .ok (.next (pc + 1)
        (.scalar (.i64 (CIL.WideMultiply.signedHigh64 left right)) :: rest) frame result) := by
  rw [step_memory_bigMul64_signed_eq]
  simp only [storeValue, CIL.Value.hasUnspecified, Bool.false_eq_true, ite_false, referenceAt,
    checkedAt, stored, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_bigMul64_signed_of_write

/-- Exact unsigned 128-bit multiplication: checked low-word write and high-word return. -/
theorem bigMul64_of_write (memory result : Memory) (reference : Reference)
    (left right : CIL.W64) (rest : List Value)
    (stored : write memory reference (numberBytes (left * right).toNat 8) 1 = .ok result) :
    memoryInstruction (.bigMul64 false)
      (.reference (.address reference) :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest)
        memory =
      .ok (result, .scalar (.i64 (CIL.WideMultiply.high64 left right)) :: rest) := by
  simp only [memoryInstruction, wideArithmeticInstruction, storeValue, referenceAt, checkedAt,
    stored,    CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take_succ_cons, List.take_zero,
    List.any_cons, List.any_nil, Value.hasUnspecified, CIL.Value.hasUnspecified,
    Bool.false_or, Bool.false_eq_true, ite_false,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Write permission is sufficient; the out location need not be initialized.
    No allocation or cell outside its eight bytes changes. -/
theorem bigMul64_succeeds (memory : Memory) (reference : Reference)
    (left right : CIL.W64) (rest : List Value)
    (writable : access memory reference 8 1 true = .ok ()) :
    ∃ result,
      memoryInstruction (.bigMul64 false)
        (.reference (.address reference) :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest)
          memory =
        .ok (result, .scalar (.i64 (CIL.WideMultiply.high64 left right)) :: rest) ∧
      loadValue result (.address reference) 8 = .ok (.i64 (left * right)) ∧
      result.allocations = memory.allocations ∧
      ∀ id offset,
        id ≠ reference.allocation ∨ offset < reference.offset ∨ reference.offset + 8 ≤ offset →
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

/-- Signed 128-bit multiplication: the same checked low-word write, and the signed high word. -/
theorem bigMul64_signed_of_write (memory result : Memory) (reference : Reference)
    (left right : CIL.W64) (rest : List Value)
    (stored : write memory reference (numberBytes (left * right).toNat 8) 1 = .ok result) :
    memoryInstruction (.bigMul64 true)
      (.reference (.address reference) :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest)
        memory =
      .ok (result, .scalar (.i64 (CIL.WideMultiply.signedHigh64 left right)) :: rest) := by
  simp only [memoryInstruction, wideArithmeticInstruction, storeValue, referenceAt, checkedAt,
    stored,    CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take_succ_cons, List.take_zero,
    List.any_cons, List.any_nil, Value.hasUnspecified, CIL.Value.hasUnspecified,
    Bool.false_or, Bool.false_eq_true, ite_false,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Signed `BigMul` needs only write permission: it reads back the low word and preserves
    allocations and every cell outside the output's eight bytes. -/
theorem bigMul64_signed_succeeds (memory : Memory) (reference : Reference)
    (left right : CIL.W64) (rest : List Value)
    (writable : access memory reference 8 1 true = .ok ()) :
    ∃ result,
      memoryInstruction (.bigMul64 true)
        (.reference (.address reference) :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest)
          memory =
        .ok (result, .scalar (.i64 (CIL.WideMultiply.signedHigh64 left right)) :: rest) ∧
      loadValue result (.address reference) 8 = .ok (.i64 (left * right)) ∧
      result.allocations = memory.allocations ∧
      ∀ id offset,
        id ≠ reference.allocation ∨ offset < reference.offset ∨ reference.offset + 8 ≤ offset →
        result.cells id offset = memory.cells id offset := by
  have width : (numberBytes (left * right).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨result, stored⟩ := write_succeeds (bytes := numberBytes (left * right).toNat 8)
    (by simpa only [width] using writable)
  refine ⟨result, bigMul64_signed_of_write memory result reference left right rest stored, ?_,
    write_allocations _ _ _ _ _ stored, ?_⟩
  · apply load_word64_of_read
    simpa only [width] using write_readback _ _ _ _ _ stored
  · intro id offset outside
    exact write_outside _ _ _ _ _ _ _ stored (by simpa only [width] using outside)

#print axioms bigMul64_signed_of_write
#print axioms bigMul64_signed_succeeds
end CIL.Safety
