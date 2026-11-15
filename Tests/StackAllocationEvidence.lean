import CIL.Extraction.Scalars
import CIL.Extraction.Translation

/-! # Independent certificate rejection of forged stack allocation metadata -/

namespace Tests.StackAllocationEvidence
open CIL CIL.Extraction

private def raw : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false
  callingConvention := 0, attributes := 0, implementation := 0
  returnType := .void, parameters := [], locals := [], initLocals := false
  maxStack := 1, genericParameters := [], code := [⟨0, 65039, .none⟩] }

/-- The emitted body: `localloc` under the signature the raw method declares. -/
private def emitted : Method :=
  { code := [.localloc], locals := [], returnsValue := false, declared := .ofRaw raw }

/-- The emitted body's shape, localsinit flag included, is the raw method's. -/
theorem shape_matches_metadata : MethodShapeValid raw emitted := by decide
#print axioms shape_matches_metadata

/-- Raw uninitialized storage cannot be emitted as initialized storage. -/
theorem forged_initialization_rejected :
    ¬ MethodShapeValid raw
      { emitted with declared := { emitted.declared with initLocals := true } } := by decide
#print axioms forged_initialization_rejected

/-- The raw opcode admits the emitted `localloc`. -/
theorem allocation_matches_opcode :
    featureOpMatches #[] raw ⟨0, 65039, .none⟩ .localloc = true := by decide +kernel
#print axioms allocation_matches_opcode

/-- Another opcode cannot inject a dynamic allocation into the emitted program. -/
theorem injected_allocation_rejected :
    featureOpMatches #[] raw ⟨0, 0, .none⟩ .localloc = false := by decide +kernel
#print axioms injected_allocation_rejected

/-- localloc requires the size to be the only stack item. -/
theorem nonempty_stack_rejected :
    scalarTransfer raw ⟨0, 65039, .none⟩ [.native, .word32] = none := by decide +kernel
#print axioms nonempty_stack_rejected

/-- A 64-bit integer is not a metadata-proven native byte count. -/
theorem non_native_size_rejected :
    scalarTransfer raw ⟨0, 65039, .none⟩ [.word64] = none := by decide +kernel
#print axioms non_native_size_rejected

end Tests.StackAllocationEvidence
