import CIL.Extraction.Scalars

/-! # Independent certificate rejection of forged stack allocation metadata -/

namespace Tests.StackAllocationEvidence
open CIL CIL.Extraction

private def raw : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false
  callingConvention := 0, attributes := 0, implementation := 0
  returnType := .void, parameters := [], locals := [], initLocals := false
  maxStack := 1, genericParameters := [], code := [⟨0, 65039, .none⟩] }

/-- Raw uninitialized storage cannot be emitted as initialized storage. -/
theorem forged_initialization_rejected :
    featureOpMatches raw ⟨0, 65039, .none⟩ (.stackAlloc true) = false := by decide +kernel
#print axioms forged_initialization_rejected

/-- An initialized raw method admits its matching flag. -/
theorem initialization_matches_metadata :
    featureOpMatches { raw with initLocals := true } ⟨0, 65039, .none⟩ (.stackAlloc true) =
      true := by decide +kernel
#print axioms initialization_matches_metadata

/-- Another opcode cannot inject a dynamic allocation into the emitted program. -/
theorem injected_allocation_rejected :
    featureOpMatches raw ⟨0, 0, .none⟩ (.stackAlloc false) = false := by decide +kernel
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
