import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

open CIL
namespace ExampleProof

/-- The runtime type of `Examples.Account` instances. -/
def accountType : Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Account"

/-- Reading `Balance` of a live account returns the value its 8 bytes hold and changes nothing. -/
theorem correctness (memory : CIL.Safety.Memory) (account : CIL.Safety.ManagedReference)
    (field : CIL.Safety.Reference) (balance : BitVec 64)
    (formed : CIL.Safety.formObject memory account = .ok (.object account))
    (located : CIL.Safety.objectFieldAddress memory account accountType 0 = .ok field)
    (loaded : CIL.Safety.loadValue memory (.address field) 8 = .ok (.i64 balance)) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object account] memory =
      .ok (memory, [.scalar (.i64 balance)]) := by
  cil_checked_steps [formed, located, loaded, accountType]

#print axioms correctness

/-- Reading a field of the null reference throws `NullReferenceException` at the `ldfld`, as the
    runtime does. -/
theorem null_throws (memory : CIL.Safety.Memory) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object .null] memory =
      .error ⟨0, 1, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps [CIL.Safety.objectFieldAddress]

#print axioms null_throws
end ExampleProof
