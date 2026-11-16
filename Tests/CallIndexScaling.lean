import CIL.Extraction.Constrained
import Lean

/-! Kernel replay comparison of instruction and call-table lookup costs. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0
open CIL CIL.Extraction
namespace CallIndexScaling
/-- A well-formed raw shell with the supplied instruction stream. -/
def raw (code : List RawInstruction) : RawMethod := {
  token := 1, owner := "Tests::Scaling", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
  genericParameters := [], code := code }
/-- No constrained opcodes; every instruction still requires reachability and opcode lookup. -/
def nops (count : Nat) := raw (List.replicate count ⟨0, 0, .none⟩)
/-- A minimal emitted method. -/
def emitted (code : List Instruction) : Method :=
  { locals := [], returnsValue := false, code := code }
/-- A managed call site of the scalar-free signature every table position holds. -/
def site : CallSite := {
  method := {
    owner := .atom "Tests" "Scaling", name := name!"", hasThis := false, genericArity := 0,
    returnType := .void, parameters := [] },
  target := .managed 1, typeArguments := [], parameterCount := 0, returnsValue := false }
/-- A managed call of `site`; the emitted link chooses the table index. -/
def call : RawInstruction := ⟨0, 40, .call site⟩
/-- Each instruction calls a distinct table position. -/
def calls (count : Nat) := raw (List.replicate count call)
/-- Equal signatures at distinct positions isolate positional lookup costs. -/
def methods (count : Nat) : List SpecializedMethod := List.replicate count ⟨[], raw []⟩
/-- Every table position is exercised once, through the link at the pc of the same index. -/
def callCode (count : Nat) : Method :=
  { emitted (List.replicate count (.call site.method)) with
    links := (List.range count).map fun index => (index, .direct index) }
/-- The original scan: positional table lookups and a scan of the link table at every pc. -/
def managedOriginal (count : Nat) : Bool :=
  all3 (fun instruction (live, link) operation =>
      validateLinkedCallWith (fun _ => false) count ((methods count)[·]?)
        (([] : List ImportSlot)[·]?) instruction live link operation)
    (calls count).code ((List.replicate count true).zip
      ((List.range count).map (callCode count).linkAt)) (callCode count).code
/-- Indexed constrained validation. -/
theorem constrainedNew128 : ConstrainedCallsValid [] [] (nops 128)
    (List.replicate 128 true) (emitted (List.replicate 128 .nop)) := by
  decide +kernel
#print axioms constrainedNew128
/-- Original constrained validation. -/
theorem constrainedOld128 : (List.range 128).all
    (constrainedSiteValid [] [] (nops 128)
    (List.replicate 128 true) (emitted (List.replicate 128 .nop))) = true := by
  decide +kernel
#print axioms constrainedOld128
/-- Indexed managed calls. -/
theorem managedNew128 : ManagedCallsValid (methods 128) [] (fun _ => false) (calls 128)
    (List.replicate 128 true) (callCode 128) := by
  decide +kernel
#print axioms managedNew128
/-- Original managed calls. -/
theorem managedOld128 : managedOriginal 128 = true := by
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
    (List.replicate 512 true) (emitted (List.replicate 512 .nop))) = true := by
  decide +kernel
#print axioms constrainedOld512
/-- Indexed managed calls. -/
theorem managedNew512 : ManagedCallsValid (methods 512) [] (fun _ => false) (calls 512)
    (List.replicate 512 true) (callCode 512) := by
  decide +kernel
#print axioms managedNew512
/-- Original managed calls. -/
theorem managedOld512 : managedOriginal 512 = true := by
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


