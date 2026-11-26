import CIL.Runtime.Net11WinX64.RangeConstructor
import Tests.PercentRuntime.Source
import CIL.Safety.ObjectSteps

/-! Decoding and linkage of Percent and the CoreLib methods executed by its range check. -/
namespace Tests.PercentRuntime
open CIL CIL.Extraction CIL.Safety CIL.Runtime.Net11WinX64 CIL.Runtime.Net11WinX64.Core
set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

/-- Original method definitions whose byte and metadata witnesses are checked above. -/
def imageMethods : List RawMethod := Source.raw :: coreBytes.map Prod.snd

/-- All physical call targets, including the resource getter on the null-message path. -/
def table : List SpecializedMethod :=
  ⟨[], Source.raw, ⟨Source.id0⟩⟩ ::
    (coreBytes.map Prod.snd ++ [rangeResource.raw]).map (⟨[], ·, ⟨coreLibraryAssembly⟩⟩)

/-- CoreLib methods returned by the ordinary checked decoder. -/
def coreMethods := coreBytes.mapM fun (body, raw) => CIL.Method.ofBody? .scalar {}
  (links table raw) (List.replicate raw.code.length true) body raw []

/-- The ordinary decoder checks the caller's frame and method flags using its original bytes. -/
def checkedCaller := CIL.Method.ofBody? .scalar {} (links table Source.raw)
  (List.replicate Source.raw.code.length true) {Source.source with
    names := Source.names} Source.raw []

/-- Keep the caller's decoded frame, links and return declaration. Execute each original
    instruction separately, with only the two literal operands parameterized. -/
def caller (name message : String) : Method :=
  let code := Source.raw.code.map (RawInstruction.mapLiteral
    (fun offset _ => if offset == 5 then name else message))
  let frame := checkedCaller.getD {code := [], locals := [], returnsValue := true}
  { frame with code := Instruction.ofRawCode none code (fun _ previous raw => Instruction.ofRaw previous raw) }

/-- Execution fixture with both literal operands supplied by the caller of the theorem. -/
def program (name message : String) : Program := caller name message :: coreMethods.getD []

/-- The string operands in the body bytes, read with the method's checked metadata. -/
def physicalLiterals : Option (String × String) := do
  let decoded ← Source.decoded.toOption
  let nameOp ← decoded.code[3]?
  let messageOp ← decoded.code[4]?
  let .text name := nameOp.operand | none
  let .text message := messageOp.operand | none
  guard (nameOp.opcode == 0x72 && messageOp.opcode == 0x72)
  return (name, message)

/-- Execute the original instructions with the checked frame and resolved constructor link. -/
def compiledProgram : Program :=
  let entry := checkedCaller.getD { code := [], locals := [], returnsValue := true }
  let code := Instruction.ofRawCode none Source.raw.code
    (fun _ previous raw => Instruction.ofRaw previous raw)
  { entry with code } :: coreMethods.getD []

/-- The exact PE body and each selected CoreLib method decode to the executable program. -/
theorem decoderProgram :
    ∃ entry constructors, checkedCaller = some entry ∧ coreMethods = some constructors ∧
      compiledProgram = entry :: constructors := by
  refine ⟨checkedCaller.getD { code := [], locals := [], returnsValue := true },
    coreMethods.getD [], ?_, ?_, ?_⟩ <;> cil_kernel_rfl
#print axioms decoderProgram

end Tests.PercentRuntime
