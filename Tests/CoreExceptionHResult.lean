import CIL.Extraction.DecodedMethod
import CIL.Safety.SymbolicExecution
import CIL.Safety.Imports
import CIL.Safety.FuelLemmas
import CIL.Safety.CheckedMemoryFacts
import CIL.Safety.ObjectSteps
import CIL.Safety.StepComposition
import Tests.CoreLibImage

/-! The .NET 11 Windows x64 System.Exception.HResult setter. -/

namespace Tests.CoreExceptionHResult
open CIL CIL.Extraction CIL.Safety

private def metadata : MethodMetadata := { own := {
  assembly := Tests.CoreLibImage.assembly
  rows := [
      (0x02000090, fixedBytes 18 0x0120100001000000030000008802A802E505),
      (0x02000091, fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06),
      (0x020000a2, fixedBytes 18 0x0120100002000000030000000000FE021C07),
      (0x020000a3, fixedBytes 18 0x09011000FFFFFFFF030000003003FE022507),
      (0x040002a8, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002a9, fixedBytes 10 0x0300FFFFFFFFFFFFFFFF),
      (0x040002aa, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002ab, fixedBytes 10 0x2100FFFFFFFFFFFFFFFF),
      (0x040002ac, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002ad, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002ae, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002af, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002b0, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002b1, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002b2, fixedBytes 10 0x0100FFFFFFFFFFFFFFFF),
      (0x040002b3, fixedBytes 10 0x2100FFFFFFFFFFFFFFFF),
      (0x040002b4, fixedBytes 10 0x2100FFFFFFFF01000000),
      (0x040002b5, fixedBytes 10 0x01000400000001000000),
      (0x040002b6, fixedBytes 10 0x5180FFFFFFFF01000000),
      (0x040002b7, fixedBytes 10 0x5280FFFFFFFFFFFFFFFF),
      (0x06000611, fixedBytes 20 0x000000000000860805000000020000001F0D0000),
      (0x2a000009, fixedBytes 12 0x0000180016010000FFFFFFFF),
      (0x2a00000a, fixedBytes 12 0x000004006A010000FFFFFFFF)]
  strings := [
      (1, fixedBytes 10 0x457863657074696F6E00),
      (2, fixedBytes 7 0x4F626A65637400),
      (3, fixedBytes 7 0x53797374656D00),
      (4, fixedBytes 9 0x5F48526573756C7400),
      (5, fixedBytes 12 0x7365745F48526573756C7400)]
  blobs := [
      (1, fixedBytes 3 0x020608),
      (2, fixedBytes 5 0x0420010108)]
  corlib := 0
  links := [⟨1, 0x040002b5, 0, 0x02000090⟩, ⟨1, 0x06000611, 0, 0x02000090⟩] } }

private def owner := TypeExpr.object coreLibraryScope "System.Exception"
private def int32 := TypeExpr.atom coreLibraryScope "System.Int32"
private def resultField : FieldRef :=
  { owner, index := 13, type := int32, name := name!"_HResult" }
private def operand := RawOperand.field owner 13 int32 name!"_HResult" false

private def original : RawMethod := {
  token := 0x06000611, owner := coreLibraryScope ++ "::System.Exception"
  receiverClass := some owner, objectFieldCount := 14, hasThis := true, explicitThis := false
  callingConvention := 0, attributes := 0x886, implementation := 0, returnType := .void
  parameters := [int32], locals := [], initLocals := false, maxStack := 8, genericParameters := []
  code := [⟨0, 2, .none⟩, ⟨1, 3, .none⟩, ⟨2, 0x7d, operand⟩, ⟨7, 0x2a, .none⟩] }

private def body : BodyEvidence := {
  bytes := [0x22, 2, 3, 0x7d, 0xb5, 2, 0, 4, 0x2a]
  tokens := { operands := [(0x040002b5, operand)] }
  metadata, tables := metadata.tables.toOption.getD [], identities := [bytesOf coreLibraryScope]
  names := {
    owner := bytesOf original.owner
    signature := bytesOf "System.Void System.Exception::set_HResult(System.Int32)" }
  pinned := PinnedIndex.ofIdentities [bytesOf coreLibraryScope] }

@[cil_code] private def setter : Method := {
  locals := [], returnsValue := false, code := [.ldarg 0, .ldarg 1, .stfld resultField, .ret]
  declared := {
    receiver := some .object, parameters := [int32], returnType := .void, initLocals := false } }

@[cil_code] private def program : Program := [setter]

/-- The original method and field tokens bind the four instructions to the typed setter. -/
theorem decoded :
    Method.ofBody? .scalar {} [] [true,true,true,true] body original [] = some setter ∧
    bodyMatches body original [] = true := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms decoded

/-- Replacing stfld with ldfld, or changing only the field token, breaks that binding. -/
theorem rejects_changed_field :
    bodyMatches {body with bytes := body.bytes.set 3 0x7b} original [] = false ∧
    bodyMatches {body with bytes := body.bytes.set 4 0xb4} original [] = false := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms rejects_changed_field

private def offset := objectFieldOffset resultField.index

/-- The BCL setter returns after writing exactly the supplied four bytes to a live Exception.
    The caller provides the model's actual checked write and can compose its resulting memory. -/
theorem correctness (before after : Safety.Memory) (object field : Reference) (word : W32)
    (live : formObject before (.address object) = .ok (.object (.address object)))
    (located : objectFieldAddress before (.address object) resultField.owner offset = .ok field)
    (written : write before field (numberBytes word.toNat 4) ordinaryAccessAlignment = .ok after) :
    invoke program 6 0 [.object (.address object), .scalar (.i32 word)] before =
      .ok (after, []) := by
  have shape : setter.fieldShape resultField = .classSlot offset (.word 4 false) := by
    cil_kernel_rfl
  let frame : Safety.Frame := ⟨before.nextIdentity, [], [], 0⟩
  have store : step setter (.stfld resultField) 2
      [.object (.address object), .scalar (.i32 word)] frame
      [.scalar (.i32 word), .object (.address object)] before = .ok (.next 3 [] frame after) := by
    rw [step_stfld_word_i32_4_eq _ _ _ _ _ _ _ _ shape]
    simp [located, written, checkedAt, Except.mapError, bind, Except.bind, pure, Except.pure]
  apply invoke_of_run (body := setter) (frame := frame) (entered := before) rfl
  · simp [List.mapM_cons, List.mapM_nil, checkedValue, numericValue, live,
      bind, Except.bind, pure, Except.pure]
  · rfl
  · cil_checked_steps [store, shape, live, located, written]
    all_goals rfl
#print axioms correctness
/-- Linking other methods and providing more fuel preserves the setter's complete result. -/
theorem linked (suffix : Program) (extra : Nat) (before after : Safety.Memory)
    (object field : Reference) (word : W32)
    (live : formObject before (.address object) = .ok (.object (.address object)))
    (located : objectFieldAddress before (.address object) resultField.owner offset = .ok field)
    (written : write before field (numberBytes word.toNat 4) ordinaryAccessAlignment = .ok after) :
    invoke (program ++ suffix) (6 + extra) 0
      [.object (.address object), .scalar (.i32 word)] before = .ok (after, []) := by
  apply invoke_mono _ 6 extra _ _ _ _ (by trivial)
  apply invoke_extend ⟨suffix, rfl⟩ _ _ _ _ (.ok (after, [])) (fun _ h => nomatch h)
  exact correctness _ _ _ _ _ live located written
#print axioms linked

end Tests.CoreExceptionHResult
