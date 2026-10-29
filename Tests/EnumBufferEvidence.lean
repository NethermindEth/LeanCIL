import CIL.Extraction.Scalars

/-! Enum buffers keep exact metadata identity through storage, calls and control-flow joins. -/

namespace Tests.EnumBufferEvidence
open CIL CIL.Extraction

/-- Two same-width enums deliberately differ only in their metadata name. -/
private def element (name : String) : TypeExpr :=
  .enum ("Fixture::" ++ name) (.atom runtimeScope "System.SByte")

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
    [("System.SByte", 1, true), ("System.Byte", 1, false),
     ("System.Int16", 2, true), ("System.UInt16", 2, false),
     ("System.Int32", 4, false), ("System.UInt32", 4, false),
     ("System.Int64", 8, false), ("System.UInt64", 8, false)].all
      (fun (name, width, signed) =>
        arrayElementType (.enum "Fixture::Choice" (.atom runtimeScope name)) ==
          some (.enumeration "Fixture::Choice" width signed)) = true := by decide +kernel
#print axioms enum_storage_checked

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
      declaringType := .atom "Fixture" "Helpers", name := "Use", target := .managed 2,
      typeArguments := [], parameterCount := 1, hasThis := false, returnsValue := false,
      returnType := .void, parameterTypes := [span "First"] }⟩
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

end Tests.EnumBufferEvidence
