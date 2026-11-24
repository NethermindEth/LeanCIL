import Tests.Support.EnumIdentity
import CIL.Extraction.Scalars

/-! Enum buffers keep exact metadata identity through storage, calls and control-flow joins. -/

namespace Tests.EnumBufferEvidence
open CIL CIL.Extraction

/-- Two same-width enums deliberately differ only in their metadata name. -/
private def element (name : String) : TypeExpr :=
  .enum (Tests.enumIdentity name) (.atom runtimeScope "System.SByte")

/-- A writable enum span over the supplied element type. -/
private def span (name : String) : TypeExpr :=
  .apply (.constructor runtimeScope "System.Span`1") (element name)

/-- A small method whose storage and return type share one enum identity. -/
private def method : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := span "First", parameters := [span "First"], locals := [span "First"],
  initLocals := true, maxStack := 2, genericParameters := [], code := [] }

/-- All eight legal enum bases retain their exact identity and existing integer width. -/
theorem enum_storage_checked :
    [("System.SByte", EnumStorage.signed8), ("System.Byte", .unsigned8),
     ("System.Int16", .signed16), ("System.UInt16", .unsigned16),
     ("System.Int32", .signed32), ("System.UInt32", .unsigned32),
     ("System.Int64", .signed64), ("System.UInt64", .unsigned64)].all
      (fun (name, storage) =>
        arrayElementType (.enum (Tests.enumIdentity "Choice") (.atom runtimeScope name)) ==
          some (.enumeration (Tests.enumIdentity "Choice") storage)) = true := by decide +kernel
#print axioms enum_storage_checked

/-- An Int32 enum widens to a word, while an enum over an Int32 byref has no scalar kind. -/
theorem enumScalarNeedsInteger :
    let int32 := TypeExpr.atom runtimeScope "System.Int32"
    (scalarType (.enum (Tests.enumIdentity "E") (.byref int32)), scalarType (.enum (Tests.enumIdentity "E") int32)) =
      (.other, .word32) := by decide +kernel
#print axioms enumScalarNeedsInteger

/-- Exact enum identity survives local stores and returns instead of becoming only a width. -/
theorem span_identity_checked :
    scalarTransfer method ⟨0, 10, .none⟩ [scalarType (span "First")] = some [] ∧
    scalarTransfer method ⟨0, 10, .none⟩ [scalarType (span "Second")] = none ∧
    scalarTransfer method ⟨0, 42, .none⟩ [scalarType (span "First")] = some [] ∧
    scalarTransfer method ⟨0, 42, .none⟩ [scalarType (span "Second")] = none := by
  decide +kernel
#print axioms span_identity_checked

/-- A method call cannot silently reinterpret one enum span as another. -/
theorem span_call_identity_checked :
    let call : RawInstruction := ⟨0, 40, .call {
      declared := { convention := 0, parameters := [span "First"] },
      method := {
        owner := .atom "Fixture" "Helpers", name := name!"Use", hasThis := false,
        genericArity := 0, returnType := .void, parameters := [span "First"] },
      name := "Use", target := .managed 2, typeArguments := [], parameterCount := 1,
      returnsValue := false }⟩
    scalarTransfer method call [scalarType (span "First")] = some [] ∧
    scalarTransfer method call [scalarType (span "Second")] = none := by decide +kernel
#print axioms span_call_identity_checked

/-- Typed element access rejects another enum token even when its byte width agrees. -/
theorem array_identity_checked :
    let stack := [ScalarKind.word32, scalarType (.array (element "First"))]
    (scalarTransfer method ⟨0, 163, .type (element "First")⟩ stack).isSome = true ∧
    scalarTransfer method ⟨0, 163, .type (element "Second")⟩ stack = none ∧
    scalarTransfer method ⟨0, 143, .type (element "Second")⟩ stack = none := by decide +kernel
#print axioms array_identity_checked

/-- Pointer-based in-place construction keeps the enum receiver's exact metadata identity. -/
theorem enum_local_constructor :
    let constructor : CallSite := {
      declared := {
        convention := 0x20, parameters := [.pointer .void, .atom runtimeScope "System.Int32"] },
      method := {
        owner := span "First", name := name!".ctor", hasThis := true, genericArity := 0,
        returnType := .void, parameters := [.pointer .void, .atom runtimeScope "System.Int32"] },
      name := ".ctor",
      target := .external (runtimeScope ++
        "::System.Void System.Span`1<First>::.ctor(System.Void*,System.Int32)"),
      typeArguments := [], parameterCount := 2, returnsValue := false }
    runtimeModel {} .call constructor.method = some (.spanInPlace (.reference 1 true)) ∧
    scalarTransfer method ⟨0, 40, .call constructor⟩
      [.word32, .reference, scalarType (.byref (span "First"))] = some [] ∧
    scalarTransfer method ⟨0, 40, .call constructor⟩
      [.word32, .reference, scalarType (.byref (span "Second"))] = none := by decide +kernel
#print axioms enum_local_constructor

end Tests.EnumBufferEvidence
