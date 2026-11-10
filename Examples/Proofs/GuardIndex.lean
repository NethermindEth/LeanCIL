import Extracted
import CIL.Safety.SymbolicExecution

/-!
# Comparison guard

`Examples.Guards.Index(index, length)` calls
`ArgumentOutOfRangeException.ThrowIfGreaterThanOrEqual(index, length)` on `uint` and returns
`index`. Proved: the guard compares the unsigned values, so an index at or above the length
raises `ArgumentOutOfRangeException` and a smaller one is returned with memory unchanged, even
when its bit pattern is negative as a signed integer.
-/

open CIL.Safety
namespace ExampleProof

/-- `Index` returns an index below `length` and raises `ArgumentOutOfRangeException` otherwise. -/
theorem correctness (memory : Memory) (literal : Reference) (index length : CIL.W32)
    (bound : memory.literals.lookup "index" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i32 index), .scalar (.i32 length)]
        memory =
      if length.toNat ≤ index.toNat then
        .error ⟨0, 3, .thrown "System.ArgumentOutOfRangeException"⟩
      else .ok (memory, [.scalar (.i32 index)]) := by
  by_cases outside : length.toNat ≤ index.toNat
  · simp only [outside, ite_true]
    cil_checked_steps [literalObject_of_lookup bound, formed, comparisonGuardOutcome,
      CIL.guardOperand, CIL.ComparisonGuard.throws, BitVec.setWidth_eq, outside]
  · simp only [outside, ite_false]
    cil_checked_steps [literalObject_of_lookup bound, formed,
      comparisonGuardOutcome, CIL.guardOperand, CIL.ComparisonGuard.throws, BitVec.setWidth_eq,
      outside]

#print axioms correctness

/-- An index with its top bit set is still below a larger unsigned length, so it is returned. -/
theorem high_index_returned (memory : Memory) (literal : Reference)
    (bound : memory.literals.lookup "index" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0
        [.scalar (.i32 0x80000000#32), .scalar (.i32 0xFFFFFFFF#32)] memory =
      .ok (memory, [.scalar (.i32 0x80000000#32)]) := by
  simpa using correctness memory literal 0x80000000#32 0xFFFFFFFF#32 bound formed

#print axioms high_index_returned

/-- An index equal to the length raises. -/
theorem equal_raises (memory : Memory) (literal : Reference) (index : CIL.W32)
    (bound : memory.literals.lookup "index" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i32 index), .scalar (.i32 index)] memory =
      .error ⟨0, 3, .thrown "System.ArgumentOutOfRangeException"⟩ := by
  simpa using correctness memory literal index index bound formed

#print axioms equal_raises
end ExampleProof