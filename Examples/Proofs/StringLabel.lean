import Extracted
import CIL.Safety.ObjectFields

/-!
# String label

`Examples.Labelled` holds a `string` `Label`. `Relabel(item, label)` stores the string argument
in the field and returns the string it held. Proved: its contract, for null and present strings
alike, with the one slot it writes as its whole footprint, and the `NullReferenceException` of a
null `item` at the first load.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

/-- `Relabel(item, label)` returns the label `item` held and leaves it holding `label`. -/
theorem correctness (memory : Memory) (item : Reference) (label : ManagedReference)
    (owned : Labelled.Label.Owned memory item)
    (labelFormed : formObject memory label = .ok (.object label))
    (heldFormed : formObject memory (Labelled.Label.of memory item) =
      .ok (.object (Labelled.Label.of memory item))) :
    ∃ fuel final, invoke Extracted.program fuel 0 [.object (.address item), .object label] memory =
        .ok (final, [.object (Labelled.Label.of memory item)]) ∧
      Confined [Labelled.Label.entry item] memory final ∧
        Labelled.Label.Holds final item label := by
  obtain ⟨stored, framed, held⟩ := owned.store_formed labelFormed
  have returned : formObject (setSlot memory (Labelled.Label.address item) label)
      (Labelled.Label.of memory item) = .ok (.object (Labelled.Label.of memory item)) := heldFormed
  refine ⟨CIL.executionBound Extracted.program 0, _, ?_, framed, held⟩
  cil_checked_steps [owned.live.formed, owned.located, owned.load.trans heldFormed, labelFormed,
    stored, returned, leaveFrame]

#print axioms correctness

/-- A null `item` throws `NullReferenceException` at the label load, pc 1. -/
theorem relabel_null_throws (memory : Memory) (label : ManagedReference)
    (labelFormed : formObject memory label = .ok (.object label)) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null, .object label] memory =
      .error ⟨0, 1, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [labelFormed]

#print axioms relabel_null_throws

end ExampleProof
