import Extracted
import CIL.Safety.SymbolicExecution

/-!
# Argument guards

`Examples.Guards.Count(count)` calls `ArgumentOutOfRangeException.ThrowIfNegative(count)` and
returns `count`. The compiler passes the parameter name as the literal `"count"`, an opaque
string the guard never reads, so the caller binds it. Proved: a negative count raises
`ArgumentOutOfRangeException` at the guard and any other count is returned with memory unchanged.
-/

open CIL.Safety
namespace ExampleProof

/-- `Count` returns a nonnegative count and raises `ArgumentOutOfRangeException` otherwise. -/
theorem correctness (memory : Memory) (literal : Reference) (count : CIL.W32)
    (bound : memory.literals.lookup "count" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i32 count)] memory =
      if count.toInt < 0 then .error ⟨0, 2, .thrown "System.ArgumentOutOfRangeException"⟩
      else .ok (memory, [.scalar (.i32 count)]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  by_cases negative : count.toInt < 0
  · simp only [negative, ite_true]
    cil_checked_steps [literalObject_of_lookup bound, formed, zeroGuardOutcome,
      CIL.guardOperand, CIL.ZeroGuard.throws, BitVec.setWidth_eq, negative]
  · simp only [negative, ite_false]
    cil_checked_steps [literalObject_of_lookup bound, formed, zeroGuardOutcome,
      CIL.guardOperand, CIL.ZeroGuard.throws, BitVec.setWidth_eq, negative]

#print axioms correctness

/-- Zero passes `ThrowIfNegative`; `ThrowIfNegativeOrZero` would raise for it. -/
theorem zero_returned (memory : Memory) (literal : Reference)
    (bound : memory.literals.lookup "count" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i32 0)] memory =
      .ok (memory, [.scalar (.i32 0)]) := by
  simpa using correctness memory literal 0 bound formed

#print axioms zero_returned
end ExampleProof