import Tests.MetadataBuilder

/-!
# Metadata return restrictions

Method definitions reject modified returns even when the claimed type is an admissible opaque atom.
-/

namespace Tests.ReturnMetadataBinding

open CIL CIL.Extraction Tests.MetadataBuilder

/-- A static method with an encoded return signature and a runtime modifier reference. -/
private def returnWorld (result : List Nat) (modifierName : String) : Step Nat := do
  let runtime ← string "System.Runtime"
  let system ← string "System"
  let objectName ← string "Object"
  let compilerServices ← string "System.Runtime.CompilerServices"
  let modifier ← string modifierName
  let program ← string "Program"
  let methodName ← string "Run"
  let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtime, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let _ ← row Table.typeRef [6, objectName, system]
  let _ ← row Table.typeRef [6, modifier, compilerServices]
  let owner ← row Table.typeDef [1, program, 0, 5, 1, 1]
  let signature ← blob ([0, 0] ++ result)
  let method ← row Table.methodDef [0, 0, 0x96, methodName, signature, 1]
  link linkDeclaring method 0 owner
  pure method

/-- Bind a method's declared return to its actual signature bytes. -/
private def acceptsReturn (result : List Nat) (claimed : TypeExpr)
    (modifierName : String := "OtherModifier") : Bool :=
  (do
    let fixture := build (returnWorld result modifierName) (bytesOf "T")
      "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
    let method : RawMethod :=
      { token := fixture.2, owner := "T::Program", hasThis := false,
        explicitThis := false, callingConvention := 0, attributes := 0x96,
        implementation := 0, returnType := claimed, parameters := [], locals := [],
        initLocals := false, maxStack := 8, genericParameters := [], code := [] }
    let env := MetadataEnv.ofSlices [← fixture.1.index]
    methodIdentityValid env method [] []).isOk

/-- An opaque atom cannot conceal an unsupported required return modifier. -/
theorem rejects_opaque_modified_return :
    acceptsReturn [0x1F, 9, 8]
      (.atom runtimeScope "System.Int32 modreq(System.Runtime.CompilerServices.OtherModifier)") =
      false := by decide +kernel

#print axioms rejects_opaque_modified_return

/-- Ordinary integer and the exact required init-void return remain admitted. -/
theorem accepts_declared_returns :
    acceptsReturn [8] (.atom runtimeScope "System.Int32") = true ∧
    acceptsReturn [0x1F, 9, 1] .void "IsExternalInit" = true := by decide +kernel

#print axioms accepts_declared_returns

/-- Optional, nested and non-void init modifiers remain unsupported return signatures. -/
theorem rejects_other_modified_returns :
    acceptsReturn [0x20, 9, 8]
      (.atom runtimeScope "System.Int32 modopt(System.Runtime.CompilerServices.OtherModifier)") =
      false ∧
    acceptsReturn [0x10, 0x1F, 9, 8]
      (.byref (.atom runtimeScope
        "System.Int32 modreq(System.Runtime.CompilerServices.OtherModifier)")) = false ∧
    acceptsReturn [0x1F, 9, 8]
      (.atom runtimeScope "System.Int32 modreq(System.Runtime.CompilerServices.IsExternalInit)")
      "IsExternalInit" = false ∧
    acceptsReturn [0x20, 9, 1]
      (.atom runtimeScope "System.Void modopt(System.Runtime.CompilerServices.IsExternalInit)")
      "IsExternalInit" = false := by decide +kernel

#print axioms rejects_other_modified_returns

/-- Metadata for a value__ field whose signature supplies the enum's underlying primitive. -/
private def enumWorld (code : Nat) : MetadataSlice :=
  (build (do
    let name ← string "Number"
    let owner ← row Table.typeDef [1, name, 0, 0, 1, 1]
    let fieldName ← string "value__"
    let signature ← blob [0x06, code]
    let field ← row Table.field [0x606, fieldName, signature]
    link linkDeclaring field 0 owner)
    (bytesOf "T") "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null").1

/-- Enum storage is read through the actual metadata index and field signature decoder. -/
private def acceptsEnum (code : Nat) : Bool :=
  (do enumUnderlying (← (enumWorld code).index) 0x02000001).isOk

/-- Enum metadata admits the eight integer widths and rejects other scalar primitives. -/
theorem enum_underlying_codes :
    ([4, 5, 6, 7, 8, 9, 10, 11].all acceptsEnum) = true ∧
    ([2, 3, 12, 13, 0x18, 0x19].any acceptsEnum) = false := by decide +kernel

#print axioms enum_underlying_codes

/-- External enum claims use exactly the same eight integer runtime atoms. -/
theorem external_enum_atoms :
    let frame : Frame :=
      { corlib := some runtimeScopeBytes, anchor := runtimeScopeBytes,
        arity := 0, ownerArity := 0 }
    let named : NamedType :=
      { scope := bytesOf "E", name := bytesOf "Number", parts := [], kind := .external none,
        pinned := false }
    let admits := fun name => frame.admits (.named named)
      (.enum "E::Number" (.atom runtimeScope name))
    (["System.SByte", "System.Byte", "System.Int16", "System.UInt16", "System.Int32",
      "System.UInt32", "System.Int64", "System.UInt64"].all admits) = true ∧
    (["System.Boolean", "System.Char", "System.Single", "System.Double", "System.IntPtr",
      "System.UIntPtr"].any admits) = false := by decide +kernel

#print axioms external_enum_atoms

end Tests.ReturnMetadataBinding
