import Extracted
import CIL.Safety.SymbolicExecution

/-!
# String literals

`Examples.Strings.SameText()` compares two loads of the literal `"x"` by reference. A literal
loads the object the caller bound to its text, and one text has one object, so the two loads
are the same instance. Proved: the method returns true with memory unchanged, and with no
object bound to `"x"` it stops as unsupported at the first load, never treating a literal as null.
-/

open CIL CIL.Safety
namespace ExampleProof

/-- Two loads of one literal are one object, so `SameText` returns true. -/
theorem correctness (memory : CIL.Safety.Memory) (literal : Reference)
    (bound : memory.literals.lookup "x" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [literalObject_of_lookup bound, formed]

#print axioms correctness

/-- A literal the caller has not bound is unsupported, not null. -/
theorem unbound_unsupported (memory : CIL.Safety.Memory)
    (unbound : memory.literals.lookup "x" = none) :
    ∃ fuel, invoke Extracted.program fuel 0 [] memory =
      .error ⟨0, 0, .unsupported "String literal is not bound by the caller"⟩ := by
  have missing : literalObject memory "x" =
      .error (.unsupported "String literal is not bound by the caller") := by
    simp only [literalObject, unbound]
  cil_checked_steps [missing]

#print axioms unbound_unsupported
end ExampleProof
