import CIL.Extraction.Parameters

/-!
Standalone kernel-work comparison for argument type and home-slot lookup. Each argument is
stored once, so the reference checks visit every position in both linked metadata lists.
-/
namespace Tests.ArgumentSlotScaling
open CIL CIL.Extraction
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-- Unsigned word arguments, each stored once in original order. -/
def raw (count : Nat) : RawArguments :=
  ⟨List.replicate count (.field .unsigned64), [], (List.range count).map ArgumentOp.store⟩

/-- Each argument store targets its appended home slot. -/
def emitted (count : Nat) : List Op := (List.range count).map fun index => .setLocal index

/-- Reference list lookup at 128 argument instructions. -/
theorem baseline128 : all3 (validateArgumentOpIn (raw 128) (List.range 128)) (raw 128).code
    (List.replicate 128 true) (emitted 128) = true := by decide +kernel
#print axioms baseline128

/-- Indexed lookup, including index construction, at 128 argument instructions. -/
theorem indexed128 : argumentInstructionsValid (raw 128) (List.range 128)
    (List.replicate 128 true) (emitted 128) = true := by decide +kernel
#print axioms indexed128

/-- Reference list lookup at 512 argument instructions. -/
theorem baseline512 : all3 (validateArgumentOpIn (raw 512) (List.range 512)) (raw 512).code
    (List.replicate 512 true) (emitted 512) = true := by decide +kernel
#print axioms baseline512

/-- Indexed lookup, including index construction, at 512 argument instructions. -/
theorem indexed512 : argumentInstructionsValid (raw 512) (List.range 512)
    (List.replicate 512 true) (emitted 512) = true := by decide +kernel
#print axioms indexed512

end Tests.ArgumentSlotScaling
