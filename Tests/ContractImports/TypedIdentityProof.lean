import Extracted
import TypedImportInterface

namespace TypedIdentityProof
open CIL.Safety

theorem correctness : TypedImportInterface.identity.Holds Extracted.program 0 := by
  intro value memory formed
  dsimp only [TypedImportInterface.identity, MethodContract.Returns]
  refine ⟨4, memory, [.scalar (.i64 value)], ?_, Confined.refl _ memory, value, rfl, rfl⟩
  cil_checked_steps

#print axioms correctness
end TypedIdentityProof
