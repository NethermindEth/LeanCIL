import Tests.MetadataBuilder

/-!
# Metadata signature restrictions

Method definitions reject modified returns and modified parameters even when the claimed type is an
admissible opaque atom; an `in` reference's own modifier is the one a parameter may carry.
-/

namespace Tests.ReturnMetadataBinding

open CIL CIL.Extraction Tests.MetadataBuilder

/-- A static method with an encoded return and parameter signature and a runtime modifier
    reference in `modifierNamespace`. -/
private def signatureWorld (result : List Nat) (parameters : List (List Nat))
    (modifierNamespace modifierName : String) : Step Nat := do
  let runtime ← string "System.Runtime"
  let system ← string "System"
  let objectName ← string "Object"
  let namespaceName ← string modifierNamespace
  let modifier ← string modifierName
  let program ← string "Program"
  let methodName ← string "Run"
  let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtime, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let _ ← row Table.typeRef [6, objectName, system]
  let _ ← row Table.typeRef [6, modifier, namespaceName]
  let owner ← row Table.typeDef [1, program, 0, 5, 1, 1]
  let signature ← blob ([0, parameters.length] ++ result ++ parameters.flatten)
  let method ← row Table.methodDef [0, 0, 0x96, methodName, signature, 1]
  link linkDeclaring method 0 owner
  pure method

/-- Bind a method's declared return and parameters to its actual signature bytes. -/
private def acceptsSignature (result : List Nat) (claimed : TypeExpr)
    (parameters : List (List Nat)) (claimedParameters : List TypeExpr)
    (modifierNamespace modifierName : String) : Bool :=
  (do
    let fixture := build (signatureWorld result parameters modifierNamespace modifierName)
      (bytesOf "T")
    let method : RawMethod :=
      { token := fixture.2, owner := "T::Program", hasThis := false,
        explicitThis := false, callingConvention := 0, attributes := 0x96,
        implementation := 0, returnType := claimed, parameters := claimedParameters, locals := [],
        initLocals := false, maxStack := 8, genericParameters := [], code := [] }
    let env := MetadataEnv.ofSlices [← fixture.1.index] (platform := objectPlatform)
    methodIdentityValid env method [] []).isOk

/-- Bind a parameterless method's declared return to its actual signature bytes. -/
private def acceptsReturn (result : List Nat) (claimed : TypeExpr)
    (modifierName : String := "OtherModifier") : Bool :=
  acceptsSignature result claimed [] [] "System.Runtime.CompilerServices" modifierName

/-- Bind an int32 method's one declared parameter to its actual signature bytes. -/
private def acceptsParameter (parameter : List Nat) (claimed : TypeExpr)
    (modifierNamespace : String := "System.Runtime.CompilerServices")
    (modifierName : String := "OtherModifier") : Bool :=
  acceptsSignature [8] (.primitive .int32) [parameter] [claimed] modifierNamespace
    modifierName

/-- An opaque atom cannot conceal an unsupported required return modifier. -/
theorem rejects_opaque_modified_return :
    acceptsReturn [0x1F, 9, 8]
      (.spelledModified runtimeScope
          "System.Int32 modreq(System.Runtime.CompilerServices.OtherModifier)") =
      false := by decide +kernel

#print axioms rejects_opaque_modified_return

/-- Ordinary integer and the exact required init-void return remain admitted. -/
theorem accepts_declared_returns :
    acceptsReturn [8] (.primitive .int32) = true ∧
    acceptsReturn [0x1F, 9, 1] .void "IsExternalInit" = true := by decide +kernel

#print axioms accepts_declared_returns

/-- Optional, nested and non-void init modifiers remain unsupported return signatures. -/
theorem rejects_other_modified_returns :
    acceptsReturn [0x20, 9, 8]
      (.spelledModified runtimeScope
          "System.Int32 modopt(System.Runtime.CompilerServices.OtherModifier)") =
      false ∧
    acceptsReturn [0x10, 0x1F, 9, 8]
      (.byref (.spelledModified runtimeScope
        "System.Int32 modreq(System.Runtime.CompilerServices.OtherModifier)")) = false ∧
    acceptsReturn [0x1F, 9, 8]
      (.spelledModified runtimeScope
          "System.Int32 modreq(System.Runtime.CompilerServices.IsExternalInit)")
      "IsExternalInit" = false ∧
    acceptsReturn [0x20, 9, 1]
      (.spelledModified runtimeScope
          "System.Void modopt(System.Runtime.CompilerServices.IsExternalInit)")
      "IsExternalInit" = false := by decide +kernel

#print axioms rejects_other_modified_returns

/-- A modified parameter is refused: the argument read narrows by the declared type, which an
    opaque atom would hide. -/
theorem rejects_modified_parameters :
    acceptsParameter [0x1F, 9, 5]
      (.spelledModified runtimeScope
          "System.Byte modreq(System.Runtime.CompilerServices.OtherModifier)") =
      false ∧
    acceptsParameter [0x20, 9, 5]
      (.spelledModified runtimeScope
          "System.Byte modopt(System.Runtime.CompilerServices.OtherModifier)") =
      false ∧
    acceptsParameter [0x10, 0x1F, 9, 8]
      (.byref (.spelledModified runtimeScope
        "System.Int32 modreq(System.Runtime.CompilerServices.OtherModifier)")) = false ∧
    acceptsParameter [0x1F, 9, 0x10, 8]
      (.spelledModified runtimeScope
        "System.Int32& modreq(System.Runtime.CompilerServices.OtherModifier)") = false := by
  decide +kernel

#print axioms rejects_modified_parameters

/-- A plain parameter and an `in` reference, whose `InAttribute` modifier it loses at run time,
    remain admitted. -/
theorem accepts_declared_parameters :
    acceptsParameter [5] (.primitive .byte) = true ∧
    acceptsParameter [0x1F, 9, 0x10, 8] (.byref (.primitive .int32))
      "System.Runtime.InteropServices" "InAttribute" = true := by decide +kernel

#print axioms accepts_declared_parameters

/-- Metadata for a value__ field whose signature supplies the enum's underlying primitive. -/
private def enumWorld (code : Nat) : MetadataSlice :=
  (build (do
    let name ← string "Number"
    let owner ← row Table.typeDef [1, name, 0, 0, 1, 1]
    let fieldName ← string "value__"
    let signature ← blob [0x06, code]
    let field ← row Table.field [0x606, fieldName, signature]
    link linkDeclaring field 0 owner)
    (bytesOf "T")).1

/-- Enum storage is read through the actual metadata index and field signature decoder. -/
private def acceptsEnum (code : Nat) : Bool :=
  (do enumUnderlying (← (enumWorld code).index) 0x02000001).isOk

/-- Enum metadata admits the eight integer widths and rejects other scalar primitives. -/
theorem enum_underlying_codes :
    ([4, 5, 6, 7, 8, 9, 10, 11].all acceptsEnum) = true ∧
    ([2, 3, 12, 13, 0x18, 0x19].any acceptsEnum) = false := by decide +kernel

#print axioms enum_underlying_codes

end Tests.ReturnMetadataBinding
