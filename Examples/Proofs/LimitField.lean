import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

open CIL
namespace ExampleProof

/-- The runtime type of `Examples.Account` instances. -/
def accountType : Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Account"

/-- Storing `limit` into a live account writes exactly the 4 bytes of `Limit`, and the bytes of
    `Balance`, the field before it, read back unchanged. -/
theorem correctness (memory after : CIL.Safety.Memory) (account : CIL.Safety.ManagedReference)
    (balanceField limitField : CIL.Safety.Reference) (limit : BitVec 32)
    (balance : List (BitVec 8))
    (formed : CIL.Safety.formObject memory account = .ok (.object account))
    (balanceLocated :
      CIL.Safety.objectFieldAddress memory account accountType 0 = .ok balanceField)
    (limitLocated : CIL.Safety.objectFieldAddress memory account accountType 8 = .ok limitField)
    (balanceRead : CIL.Safety.read memory balanceField 8 1 = .ok balance)
    (written : CIL.Safety.write memory limitField (CIL.Safety.numberBytes limit.toNat 4) 1 =
      .ok after) :
    (∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object account, .scalar (.i32 limit)]
      memory = .ok (after, [])) ∧
    CIL.Safety.read after balanceField 8 1 = .ok balance := by
  constructor
  · cil_checked_steps [formed, limitLocated, written, accountType]
  · exact CIL.Safety.objectField_write_preserves_earlier balanceLocated limitLocated
      (by decide) (by decide) written balanceRead

#print axioms correctness
end ExampleProof
