import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

open CIL
namespace ExampleProof

/-- The runtime type of `Examples.Account` instances. -/
def accountType : Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Account"

/-- Storing `amount` into a live account's `Balance` and reading it back returns `amount`, and
    the method's only effect is that one 8-byte store. -/
theorem correctness (memory after : CIL.Safety.Memory) (account : CIL.Safety.ManagedReference)
    (field : CIL.Safety.Reference) (amount : BitVec 64)
    (formed : CIL.Safety.formObject memory account = .ok (.object account))
    (located : CIL.Safety.objectFieldAddress memory account accountType 0 = .ok field)
    (written : CIL.Safety.write memory field (CIL.Safety.numberBytes amount.toNat 8) 1 =
      .ok after) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object account, .scalar (.i64 amount)]
      memory = .ok (after, [.scalar (.i64 amount)]) := by
  have unchanged := CIL.Safety.write_allocations _ _ _ _ _ written
  have formedAfter := (CIL.Safety.formObject_of_allocations unchanged account).trans formed
  have locatedAfter :=
    (CIL.Safety.objectFieldAddress_of_allocations unchanged account accountType 0).trans located
  have readback := CIL.Safety.objectField_readback_i64 written
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [formed, located, written, formedAfter, locatedAfter, readback,
    accountType]

#print axioms correctness
end ExampleProof
