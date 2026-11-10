import Extracted
import TypedImportInterface

namespace TypedIdentityProof
open CIL.Safety

theorem correctness : TypedImportInterface.identity.Holds Extracted.program 0 := by
  intro value memory formed
  dsimp only [TypedImportInterface.identity, MethodContract.Returns]
  refine MethodContract.Holds.intro (c := TypedImportInterface.identity) (input := value)
    memory value ?_ (Confined.refl _ memory) rfl
  cil_checked_steps

#print axioms correctness
end TypedIdentityProof
