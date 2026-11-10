import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

open CIL
namespace ExampleProof

/-- The runtime type of `Examples.Account` instances. -/
def accountType : Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Account"

/-- The instance getter `Headroom` reads both fields through its receiver and returns their
    wrapping 64-bit sum, the 32-bit limit zero-extended, without changing memory. -/
theorem correctness (memory : CIL.Safety.Memory) (account : CIL.Safety.ManagedReference)
    (balanceField limitField : CIL.Safety.Reference) (balance : BitVec 64) (limit : BitVec 32)
    (formed : CIL.Safety.formObject memory account = .ok (.object account))
    (balanceLocated :
      CIL.Safety.objectFieldAddress memory account accountType 0 = .ok balanceField)
    (limitLocated : CIL.Safety.objectFieldAddress memory account accountType 8 = .ok limitField)
    (balanceLoaded : CIL.Safety.loadValue memory (.address balanceField) 8 = .ok (.i64 balance))
    (limitLoaded : CIL.Safety.loadValue memory (.address limitField) 4 = .ok (.i32 limit)) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object account] memory =
      .ok (memory, [.scalar (.i64 (balance + limit.zeroExtend 64))]) := by
  cil_checked_steps [formed, balanceLocated, limitLocated, balanceLoaded, limitLoaded,
    accountType]

#print axioms correctness

/-- Calling the getter on a null receiver throws `NullReferenceException` at its first `ldfld`. -/
theorem null_throws (memory : CIL.Safety.Memory) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object .null] memory =
      .error ⟨0, 1, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps [CIL.Safety.objectFieldAddress]

#print axioms null_throws
end ExampleProof
