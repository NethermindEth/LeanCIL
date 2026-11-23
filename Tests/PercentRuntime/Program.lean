import Tests.PercentRuntime.Core
import Tests.PercentRuntime.Source
import CIL.Safety.ObjectSteps

/-! Decoding and linkage of Percent and the CoreLib methods executed by its range check. -/
namespace Tests.PercentRuntime
open CIL CIL.Extraction CIL.Safety Core
set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

/-- Physical bodies reached by the constructor with a non-null message argument. -/
def coreBytes : List (BodyEvidence × RawMethod) := [
    ({ RangeCtor.body with names := RangeCtor.names }, RangeCtor.definition),
    ({ ArgumentCtor.body with names := ArgumentCtor.names }, ArgumentCtor.definition),
    ({ SystemExceptionCtor.body with names := SystemExceptionCtor.names }, SystemExceptionCtor.definition),
    ({ ExceptionMessageCtor.body with names := ExceptionMessageCtor.names }, ExceptionMessageCtor.definition),
    ({ ExceptionCtor.body with names := ExceptionCtor.names }, ExceptionCtor.definition),
    ({ ObjectCtor.body with names := ObjectCtor.names }, ObjectCtor.definition),
    ({ SetHResult.body with names := SetHResult.names }, SetHResult.definition)]


/-- Original method definitions whose byte and metadata witnesses are checked above. -/
def imageMethods : List RawMethod := Source.raw :: coreBytes.map Prod.snd

/-- All physical call targets, including the resource getter on the null-message path. -/
def table : List SpecializedMethod :=
  ⟨[], Source.raw, ⟨Source.assembly0Metadata.identity⟩⟩ ::
    (coreBytes.map Prod.snd ++ [RangeResource.raw]).map (⟨[], ·, ⟨coreLibraryScope⟩⟩)

/-- Admit a managed call or allocation only if the raw site selects its unique physical target. -/
def linked (table : List SpecializedMethod) (raw : RawInstruction) : Option Link := do
  let .call site := raw.operand | none
  let .managed token := site.target | none
  let [(callee,ordinal)] := table.zipIdx.filter (fun item => calleeMatchesSite site token item.1) | none
  if raw.opcode == 0x73 then
    let link := Link.object ordinal callee.closed.objectBases (objectFieldOffset callee.closed.objectFieldCount)
    guard (validateConstructionWith (fun i => table[i]?) raw true (some link) site.method)
    return link
  guard (raw.opcode == 0x28)
  let link := Link.direct ordinal
  guard (validateManagedCallWith table.length (fun i => table[i]?) (fun _ => none)
    raw true (some link) (.call site.method {}))
  return link
/-- Checked links indexed by the original instruction positions. -/
def links (table : List SpecializedMethod) (raw : RawMethod) :=
  raw.code.zipIdx.filterMap fun (op,pc) => (linked table op).map (pc,·)

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
