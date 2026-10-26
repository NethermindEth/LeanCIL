import CIL.Extraction.Folds
/-! Kernel benchmark for a long message-only body with no admitted throw fold. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CIL CIL.Extraction
/-- Message loads alone never establish an exception fold. -/
theorem messagePrefix : foldRoles [] (List.replicate 4096 (⟨0, 20, .none⟩ : RawInstruction)) =
    List.replicate 4096 none := by decide +kernel
#print axioms messagePrefix
