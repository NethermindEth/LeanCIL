import Extracted
import CIL.Safety.SymbolicExecution

/-!
# Null guard

`Examples.Guards.Required(label)` calls `ArgumentNullException.ThrowIfNull(label)` and returns
`label`. Proved: a null label raises `ArgumentNullException` at the guard and any other label is
returned unchanged with memory unchanged.
-/

open CIL.Safety
namespace ExampleProof

/-- A null label raises `ArgumentNullException`. -/
theorem null_raises (memory : Memory) (literal : Reference)
    (bound : memory.literals.lookup "label" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .error ⟨0, 2, .thrown "System.ArgumentNullException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [literalObject_of_lookup bound, formed]

#print axioms null_raises

/-- A label that forms is returned as it is. -/
theorem keeps_label (memory : Memory) (label literal : Reference)
    (labelFormed : formObject memory (.address label) = .ok (.object (.address label)))
    (bound : memory.literals.lookup "label" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address label)] memory =
      .ok (memory, [.object (.address label)]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [labelFormed, literalObject_of_lookup bound, formed, leaveFrame]

#print axioms keeps_label

/-- `Required` returns a non-null label and raises `ArgumentNullException` for null. -/
theorem correctness (memory : Memory) (label : ManagedReference) (literal : Reference)
    (labelFormed : ∀ reference, label = .address reference →
      formObject memory label = .ok (.object label))
    (bound : memory.literals.lookup "label" = some literal)
    (formed : formObject memory (.address literal) = .ok (.object (.address literal))) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object label] memory =
      if label = .null then .error ⟨0, 2, .thrown "System.ArgumentNullException"⟩
      else .ok (memory, [.object label]) := by
  cases label with
  | null => simpa using null_raises memory literal bound formed
  | address reference =>
    simpa using keeps_label memory reference literal (labelFormed reference rfl) bound formed

#print axioms correctness
end ExampleProof