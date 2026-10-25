import CIL.Safety.StepTransport
import CIL.Safety.FrameEntryRenaming

/-!
# Methods with relocated retained locals

The relation fixes every instruction and call target while relocating local operands.
Retained declarations keep their initializers; inserted declarations have valid initializers.
-/

namespace CIL.Safety

/-- A method differs only by insertion of unused local declarations and operand relocation. -/
structure MethodRenaming (source target : CIL.Method) where
  indices : LocalIndexMap
  metadata : StepMetadata source target
  declarations : LocalDeclarations indices source.localKinds source.locals
    target.localKinds target.locals
  sourceReady : OrdinaryFrame source
  targetReady : OrdinaryFrame target
  code : target.code = source.code.map indices.operation

/-- Fetching an actual instruction selects its relocated target instruction at the same pc. -/
theorem MethodRenaming.instruction {source target : CIL.Method}
    (related : MethodRenaming source target) {pc : Nat} {operation : CIL.Op}
    (found : source.code[pc]? = some operation) :
    target.code[pc]? = some (related.indices.operation operation) := by
  rw [related.code, List.getElem?_map, found]
  rfl
#print axioms MethodRenaming.instruction

/-- Every source method has a corresponding target at the same callable index. -/
def ProgramRenaming (source target : CIL.Program) : Prop :=
  ∀ (method : Nat) (sourceBody : CIL.Method), source[method]? = some sourceBody →
    ∃ targetBody, target[method]? = some targetBody ∧
      Nonempty (MethodRenaming sourceBody targetBody)

end CIL.Safety
