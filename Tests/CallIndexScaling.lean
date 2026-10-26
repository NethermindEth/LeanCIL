import CIL.Extraction.Constrained
import Lean

/-! Kernel replay comparison of instruction and call-table lookup costs. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0
open CIL CIL.Extraction
namespace CallIndexScaling
/-- A well-formed raw shell with the supplied instruction stream. -/
def raw (code : List RawInstruction) : RawMethod := {
  token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
  genericParameters := [], code := code }
/-- No constrained opcodes; every instruction still requires reachability and opcode lookup. -/
def nops (count : Nat) := raw (List.replicate count ⟨0, 0, .none⟩)
/-- A minimal emitted method. -/
def emitted (code : List Op) : Method := { locals := [], returnsValue := false, code := code }
/-- A managed call to the identical scalar-free signature at a chosen table index. -/
def call : RawInstruction := ⟨0, 40, .call {
  target := .managed 1, typeArguments := [], parameterCount := 0, hasThis := false,
  returnsValue := false, returnType := .void, parameterTypes := [] }⟩
/-- Each instruction calls a distinct table position. -/
def calls (count : Nat) := raw (List.replicate count call)
/-- Equal signatures at distinct positions isolate positional lookup costs. -/
def methods (count : Nat) : List SpecializedMethod := List.replicate count ⟨[], raw []⟩
/-- Every table position is exercised once. -/
def callCode (count : Nat) := emitted ((List.range count).map fun index => .call index 0)
/-- Indexed constrained validation. -/
theorem constrainedNew128 : ConstrainedCallsValid [] [] (nops 128)
    (List.replicate 128 true) (emitted (List.replicate 128 .nop)) := by
  decide +kernel
#print axioms constrainedNew128
/-- Original constrained validation. -/
theorem constrainedOld128 : (List.range 128).all
    (constrainedSiteValid [] [] (nops 128)
    (List.replicate 128 true) (List.replicate 128 .nop)) = true := by
  decide +kernel
#print axioms constrainedOld128
/-- Indexed managed calls. -/
theorem managedNew128 : ManagedCallsValid (methods 128) [] (calls 128)
    (List.replicate 128 true) (callCode 128) := by
  decide +kernel
#print axioms managedNew128
/-- Original managed calls. -/
theorem managedOld128 : all3 (validateManagedCall (methods 128) []) (calls 128).code
    (List.replicate 128 true) (callCode 128).code = true := by
  decide +kernel
#print axioms managedOld128

/-- Indexed constrained validation. -/
theorem constrainedNew512 : ConstrainedCallsValid [] [] (nops 512)
    (List.replicate 512 true) (emitted (List.replicate 512 .nop)) := by
  decide +kernel
#print axioms constrainedNew512
/-- Original constrained validation. -/
theorem constrainedOld512 : (List.range 512).all
    (constrainedSiteValid [] [] (nops 512)
    (List.replicate 512 true) (List.replicate 512 .nop)) = true := by
  decide +kernel
#print axioms constrainedOld512
/-- Indexed managed calls. -/
theorem managedNew512 : ManagedCallsValid (methods 512) [] (calls 512)
    (List.replicate 512 true) (callCode 512) := by
  decide +kernel
#print axioms managedNew512
/-- Original managed calls. -/
theorem managedOld512 : all3 (validateManagedCall (methods 512) []) (calls 512).code
    (List.replicate 512 true) (callCode 512).code = true := by
  decide +kernel
#print axioms managedOld512

end CallIndexScaling
open Lean in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    unless name.toString.startsWith "CallIndexScaling." do continue
    let .thmInfo declaration := info | continue
    let start ← IO.getNumHeartbeats
    let proof := Expr.letE `checked declaration.type declaration.value (.bvar 0) false
    match Kernel.check (← getEnv) {} proof with
    | .error _ => throwError "Kernel rejected {name}"
    | .ok _ => logInfo m!"{name}: {(← IO.getNumHeartbeats) - start} raw heartbeats"


