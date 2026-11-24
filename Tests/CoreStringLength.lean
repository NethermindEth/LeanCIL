import CIL.Extraction.DecodedMethod
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields
import CIL.Safety.ObjectSteps
import CIL.Runtime.Net11WinX64.CoreLib

/-!
# Execution of the CoreLib string length getter

The .NET 11.0.0 Windows x64 CoreLib image has SHA-256
`7b82f62a60e1673863813dd78af931a775be0630570a377cffa9e8cb9cb7abab`.
The fixture contains the eight bytes of MethodDef 0x06000a25 and the metadata slice the
extractor carries for it. The method belongs to System.String.
Its only field operand names the four-byte _stringLength slot. The contract requires
readable access to that slot and preserves the caller's memory.
-/

namespace Tests.CoreStringLength

open CIL CIL.Extraction CIL.Safety

/-- Carried rows and heap entries for the getter, its owner, the field, and their signatures. -/
private def metadata : MethodMetadata := { own := {
  assembly := CIL.Runtime.Net11WinX64.CoreLib.assembly
  rows := [
      (0x020000a2, fixedBytes 18 0x0120100001000000030000000000FE021C07),
      (0x020000a3, fixedBytes 18 0x09011000FFFFFFFF030000003003FE022507),
      (0x020000c6, fixedBytes 18 0x01211000020000000300000088028A03A209),
      (0x020000c7, fixedBytes 18 0x85011000FFFFFFFF0000000088028D03DB0A),
      (0x0400038a, fixedBytes 10 0x3600FFFFFFFFFFFFFFFF),
      (0x0400038b, fixedBytes 10 0xA1000400000001000000),
      (0x0400038c, fixedBytes 10 0x8100FFFFFFFFFFFFFFFF),
      (0x06000a25, fixedBytes 20 0x0000000000008608050000000200000079130000),
      (0x2a000009, fixedBytes 12 0x0000180016010000FFFFFFFF),
      (0x2a00000a, fixedBytes 12 0x000004006A010000FFFFFFFF),
      (0x2a00000c, fixedBytes 12 0x0000040080010000FFFFFFFF),
      (0x2a00000d, fixedBytes 12 0x00002200AC010000FFFFFFFF)]
  strings := [
      (1, fixedBytes 7 0x4F626A65637400),
      (2, fixedBytes 7 0x537472696E6700),
      (3, fixedBytes 7 0x53797374656D00),
      (4, fixedBytes 14 0x5F737472696E674C656E67746800),
      (5, fixedBytes 11 0x6765745F4C656E67746800)]
  blobs := [
      (1, fixedBytes 3 0x020608),
      (2, fixedBytes 4 0x03200008)]
  corlib := 0
  links := [⟨1, 0x0400038b, 0, 0x020000c6⟩, ⟨1, 0x06000a25, 0, 0x020000c6⟩] } }

private def owner := TypeExpr.object coreLibraryScope "System.String"
private def int32 := TypeExpr.atom coreLibraryScope "System.Int32"

/-- The getter reads the first of the two instance fields in the string definition. -/
private def lengthField : FieldRef :=
  { owner, index := 0, type := int32, name := name!"_stringLength" }

private def operand := RawOperand.field owner 0 int32 name!"_stringLength" false

/-- Original implicit-receiver signature, stack bound, and opcode offsets. -/
private def original : RawMethod := {
  token := 0x06000a25, owner := coreLibraryScope ++ "::System.String"
  receiverClass := some owner, objectFieldCount := 2, hasThis := true, explicitThis := false
  callingConvention := 0, attributes := 0x886, implementation := 0, returnType := int32
  parameters := [], locals := [], initLocals := false, maxStack := 8, genericParameters := []
  code := [⟨0, 2, .none⟩, ⟨1, 123, operand⟩, ⟨6, 42, .none⟩] }

/-- The method's tiny header, IL bytes, single operand token, and metadata. -/
private def body : BodyEvidence := {
  bytes := [0x1e, 2, 0x7b, 0x8b, 3, 0, 4, 0x2a], tokens := { operands := [(0x0400038b, operand)] }
  metadata, tables := metadata.tables.toOption.getD [], identities := [bytesOf coreLibraryScope]
  names := {
    owner := bytesOf original.owner
    signature := bytesOf "System.Int32 System.String::get_Length()" }
  pinned := PinnedIndex.ofIdentities [bytesOf coreLibraryScope] }

/-- The canonical method including the receiver, return type and localsinit bit. -/
@[cil_code] private def getter : Method := {
  locals := [], returnsValue := true, code := [.ldarg 0, .ldfld lengthField, .ret]
  declared := { receiver := some .object, returnType := int32, initLocals := false } }

@[cil_code] private def program : Program := [getter]

/-- The public body decoder reconstructs the getter from the original code and metadata. -/
theorem decoded : Method.ofBody? .scalar {} [] [true, true, true] body original [] = some getter ∧
    bodyMatches body original [] = true := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩

#print axioms decoded

/-- A byref receiver, a missing owner field, and a crossed IL field token each fail. -/
theorem rejects_inconsistent_evidence :
    (Method.ofBody? .scalar {} [] [true, true, true] body
      {original with receiverClass := none} []).isNone = true ∧
    (Method.ofBody? .scalar {} [] [true, true, true] body
      {original with objectFieldCount := 1} []).isNone = true ∧
    (Method.ofBody? .scalar {} [] [true, true, true]
      {body with bytes := [0x1e, 2, 0x7b, 0x8c, 3, 0, 4, 0x2a]} original []).isNone = true := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩

#print axioms rejects_inconsistent_evidence

private def lengthSlot : WordField 4 := ⟨owner, 0⟩

/-- Every caller with a readable length slot receives its exact 32-bit value and original memory. -/
theorem invoke_length (memory : Safety.Memory) (object : Reference)
    (readable : lengthSlot.Readable memory object) :
    invoke program 6 0 [.object (.address object)] memory =
      .ok (memory, [.scalar (.i32 (lengthSlot.of memory object))]) := by
  obtain ⟨live, located, loaded⟩ := readable.facts
  change objectFieldAddress memory (.address object) owner 0 = _ at located
  change loadValue memory (.address (lengthSlot.address object)) 4 = .ok (.i32 _) at loaded
  have shape : getter.fieldShape lengthField = .classSlot 0 (.word 4 false) := by cil_kernel_rfl
  let frame : Safety.Frame := ⟨memory.nextIdentity, [], [], 0⟩
  apply invoke_of_run (body := getter) (frame := frame) (entered := memory) rfl
  · simp [List.mapM_cons, List.mapM_nil, checkedValue_object memory _ live,
      bind, Except.bind, pure, Except.pure]
  · rfl
  · cil_checked_steps [shape, live, located, loaded]
    rfl

#print axioms invoke_length

end Tests.CoreStringLength
