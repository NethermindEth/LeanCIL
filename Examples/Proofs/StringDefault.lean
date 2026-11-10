import Extracted
import CIL.Safety.SymbolicExecution

/-!
# String default

`Examples.Strings.OrNone(label)` is `label ?? "none"`. Proved: a non-null label is returned
unchanged, a null label is replaced by the object the caller bound to `"none"`, and with no
object bound to `"none"` a null label stops as unsupported instead of returning null.
-/

open CIL.Safety
namespace ExampleProof

/-- A label that forms is returned as it is, without loading the literal. -/
theorem keeps_label (memory : Memory) (label : Reference)
    (formed : formObject memory (.address label) = .ok (.object (.address label))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address label)] memory =
      .ok (memory, [.object (.address label)]) := by
  cil_checked_steps [formed]

#print axioms keeps_label

/-- A null label is replaced by the bound `"none"` object. -/
theorem null_is_none (memory : Memory) (literal : Reference)
    (bound : memory.literals.lookup "none" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .ok (memory, [.object (.address literal)]) := by
  cil_checked_steps [literalObject_of_lookup bound, formed]

#print axioms null_is_none

/-- `OrNone` returns its label when it is not null and the bound `"none"` object otherwise. -/
theorem correctness (memory : Memory) (label : ManagedReference) (literal : Reference)
    (labelFormed : ∀ reference, label = .address reference →
      formObject memory label = .ok (.object label))
    (bound : memory.literals.lookup "none" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object label] memory =
      .ok (memory, [.object (if label = .null then .address literal else label)]) := by
  cases label with
  | null => simpa using null_is_none memory literal bound formed
  | address reference =>
    simpa using keeps_label memory reference (labelFormed reference rfl)

#print axioms correctness

/-- With `"none"` unbound, a null label is unsupported rather than a null result. -/
theorem unbound_unsupported (memory : Memory) (unbound : memory.literals.lookup "none" = none) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .error ⟨0, 4, .unsupported "String literal is not bound by the caller"⟩ := by
  have missing : literalObject memory "none" =
      .error (.unsupported "String literal is not bound by the caller") := by
    simp only [literalObject, unbound]
  cil_checked_steps [missing]

#print axioms unbound_unsupported
end ExampleProof
