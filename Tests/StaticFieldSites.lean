import CIL.Extraction.Translation
import Tests.BodyEncoding

/-!
# Static sites bound to the field their token names

`T` reads the static `Y` with `ldsfld`, `ldsflda` or a field `ldtoken`, or stores it with
`stsfld`. `Y` and `X` are either fields of `T`'s own `Fixture`, which the carried slice defines,
or member references into `Ext.Point` of an assembly no slice carries. The static site at the
access carries the descriptor of `X`, so the model would use `X`'s storage for `Y`: every such
body is refused, while the carried `Y` with its own descriptor is a valid translation for each
instruction. Of the fields of types no slice carries, only `BitConverter.IsLittleEndian` is
admitted, and only as the `ldsfld` the feature check reads as a constant.
-/

namespace Tests.StaticFieldSites

open CIL CIL.Extraction Tests.MetadataBuilder Tests.BodyEncoding

private def pin : AssemblyPin :=
  { identity := "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" }
private def extScope : String := "Ext, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def int32 : TypeExpr := .atom runtimeScope "System.Int32"

/-- The static field instructions under test. -/
private def ldsfld : Nat := 0x7E
private def ldsflda : Nat := 0x7F
private def stsfld : Nat := 0x80
private def ldtoken : Nat := 0xD0

/-- The owner of `X` and `Y`: `T`'s `Fixture` when `carried`, else `Ext.Point`. -/
private def owner (carried : Bool) : TypeExpr :=
  if carried then .atom pin.identity "Fixture" else .object extScope "Ext.Point"

/-- `X` and `Y` as the instruction names them; a carried static counts from its owner's first
    field. -/
private def xField (carried : Bool) : FieldRef :=
  { owner := owner carried, index := 0, type := int32, name := name!"X" }
private def yField (carried : Bool) : FieldRef :=
  { owner := owner carried, index := if carried then 1 else 0, type := int32, name := name!"Y" }

/-- The signature bytes of the result of the method using `opcode`: the loaded `int`, a
    reference to it, or nothing. -/
private def resultBytes (opcode : Nat) : List Nat :=
  if opcode == ldsfld then [0x08] else if opcode == ldsflda then [0x10, 0x08] else [0x01]

/-- `T` with `static M()`, the fields `X` and `Y` of `Fixture` when `carried` or references to
    those of `Ext.Point` otherwise, and a reference to `BitConverter.IsLittleEndian`; it returns
    the tokens of `Y` and of `IsLittleEndian`. -/
private def world (carried : Bool) (result : List Nat) : Step (Nat × Nat) := do
  let runtimeName ← string "System.Runtime"
  let extName ← string "Ext"
  let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtimeName, 0, 0]
  let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, extName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let objectName ← string "Object"
  let systemName ← string "System"
  let _ ← row Table.typeRef [1 * 4 + 2, objectName, systemName]
  let pointName ← string "Point"
  let pointRef ← row Table.typeRef [2 * 4 + 2, pointName, extName]
  let converterName ← string "BitConverter"
  let converterRef ← row Table.typeRef [1 * 4 + 2, converterName, systemName]
  let moduleName ← string "<Module>"
  let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
  let fixtureName ← string "Fixture"
  let fixture ← row Table.typeDef [1, fixtureName, 0, 1 * 4 + 1, 1, 1]
  let xName ← string "X"
  let yName ← string "Y"
  let intField ← blob [0x06, 0x08]
  let staticFlags := 0x0016
  let fields ← if carried then do
      let x ← row Table.field [staticFlags, xName, intField]
      let y ← row Table.field [staticFlags, yName, intField]
      pure [x, y]
    else pure []
  let methodName ← string "M"
  let methodBlob ← blob ([0x00, 0x00] ++ result)
  let definition ← row Table.methodDef [0, 0, 0, methodName, methodBlob, 1]
  link linkDeclaring definition 0 fixture
  for field in fields do link linkDeclaring field 0 fixture
  let pointParent := (pointRef - 0x01000000) * 8 + 1
  let _ ← row Table.memberRef [pointParent, xName, intField]
  let yRef ← row Table.memberRef [pointParent, yName, intField]
  let endianName ← string "IsLittleEndian"
  let booleanField ← blob [0x06, 0x02]
  let endian ← row Table.memberRef [(converterRef - 0x01000000) * 8 + 1, endianName, booleanField]
  pure (fields.getLast?.getD yRef, endian)

private def slice (carried : Bool) (result : List Nat) : MetadataSlice × Nat × Nat :=
  build (world carried result) (bytesOf "T") pin.identity

/-- The static operand of `field`. -/
private def operandOf (field : FieldRef) : RawOperand :=
  .field field.owner field.index field.type field.name true

/-- The raw body `opcode field; ret`, with `ldc.i4.1` before a store and `pop` after a token. -/
private def raw (opcode : Nat) (field : FieldRef) (returnType : TypeExpr) : RawMethod :=
  let access := operandOf field
  { token := 0x06000001, owner := pin.identity ++ "::Fixture", hasThis := false,
    explicitThis := false, callingConvention := 0, attributes := 0, implementation := 0,
    returnType, parameters := [], locals := [], initLocals := false, maxStack := 8,
    genericParameters := [],
    code :=
      if opcode == stsfld then [⟨0, 0x17, .none⟩, ⟨1, stsfld, access⟩, ⟨6, 0x2A, .none⟩]
      else if opcode == ldtoken then [⟨0, ldtoken, access⟩, ⟨5, 0x26, .none⟩, ⟨6, 0x2A, .none⟩]
      else [⟨0, opcode, access⟩, ⟨5, 0x2A, .none⟩] }

/-- The bytes and token table of `raw` with `token` at the access. -/
private def body (opcode : Nat) (field : FieldRef) (returnType : TypeExpr) (world : MetadataSlice)
    (token : Nat) : BodyEvidence :=
  let encoded := MetadataBuilder.littleEndian 4 token
  let bytes :=
    if opcode == stsfld then [7 * 4 + 2, 0x17, stsfld] ++ encoded ++ [0x2A]
    else if opcode == ldtoken then [7 * 4 + 2, ldtoken] ++ encoded ++ [0x26, 0x2A]
    else [6 * 4 + 2, opcode] ++ encoded ++ [0x2A]
  evidenceOf bytes [(token, operandOf field)] { own := world } (raw opcode field returnType)

/-- The result type of the method using `opcode` on an `int`. -/
private def returnType (opcode : Nat) : TypeExpr :=
  if opcode == ldsfld then int32 else if opcode == ldsflda then .byref int32 else .void

/-- The body accessing `Y` of `owner carried` with `opcode`. -/
private def yBody (carried : Bool) (opcode : Nat) : BodyEvidence :=
  let world := slice carried (resultBytes opcode)
  body opcode (yField carried) (returnType opcode) world.1 world.2.1

private def unknown (count : Nat) : Option FeatureState := some ⟨List.replicate count none, []⟩

/-- The evidence of the method accessing `Y`: the stack holds the loaded value or its address after
    a load, the stored value before a store and the handle after a token. -/
private def evidence (carried : Bool) (opcode : Nat) : MethodEvidence :=
  let three := opcode == stsfld || opcode == ldtoken
  let pushed : ScalarKind :=
    if opcode == ldsfld || opcode == stsfld then .word32
    else if opcode == ldsflda then .reference else .other
  let operations : List ArgumentOp := List.replicate (if three then 3 else 2) .other
  let original := raw opcode (yField carried) (returnType opcode)
  { original, body := yBody carried opcode, arguments := [], closed := original,
    parameterInput := { arguments := [], locals := [], code := operations },
    reachable := List.replicate (if three then 3 else 2) true,
    featureStates := if three then [unknown 0, unknown 1, unknown 0] else [unknown 0, unknown 1],
    scalarStates := if three then [some [], some [pushed], some []] else [some [], some [pushed]],
    layoutUses := [], assembly := pin,
    signature := (spelled? (yBody carried opcode).names.signature).getD "" }

/-- The descriptor of the static readonly `field`, which its constructor sets to `value`, keyed by
    `identity`. -/
private def descriptorOf (field : FieldRef) (identity value : Nat) : StaticDescriptor :=
  let initializer : StaticInitializer :=
    { method := 0, literal := some (.i32 (BitVec.ofNat 32 value)), arguments := [] }
  { identity, field, bytes := [BitVec.ofNat 8 value, 0, 0, 0], scalar := some false,
    initializer := some initializer }

/-- The emitted method accessing `Y` with `opcode`, whose static site carries `descriptor`. -/
private def method (carried : Bool) (opcode : Nat) (descriptor : StaticDescriptor) : Method :=
  let field := yField carried
  let code : List Instruction :=
    if opcode == ldsfld then [.ldsfld field, .ret]
    else if opcode == ldsflda then [.ldsflda field, .ret]
    else if opcode == stsfld then [.ldc_i4 1, .stsfld field, .ret]
    else [.ldtoken (.field field), .pop, .ret]
  { locals := [], returnsValue := opcode == ldsfld || opcode == ldsflda,
    declared := DeclaredSignature.ofRaw (raw opcode field (returnType opcode)), code,
    staticSites := [(if opcode == stsfld then 1 else 0, descriptor)] }

/-- The method with the site of `Y` carrying `X`'s descriptor or `Y`'s own; the two differ only in
    the field they name. -/
private def withX (carried : Bool) (opcode : Nat) : Method :=
  method carried opcode (descriptorOf (xField carried) 2 2)
private def withY (carried : Bool) (opcode : Nat) : Method :=
  method carried opcode (descriptorOf (yField carried) 2 2)

/-- Whether the extraction of one method accessing `Y` is a valid translation. -/
private abbrev valid (carried : Bool) (opcode : Nat) (emitted : Method) : Prop :=
  TranslationValid [] #[] [] [evidence carried opcode] [] [emitted]

/-! ## A carried owner -/

/-- Each access to the carried `Y` is a valid translation with `Y`'s own descriptor at its site. -/
theorem carried_access_with_own_descriptor_accepted :
    valid true ldsfld (withY true ldsfld) ∧ valid true ldsflda (withY true ldsflda) ∧
    valid true stsfld (withY true stsfld) ∧ valid true ldtoken (withY true ldtoken) := by
  decide +kernel
#print axioms carried_access_with_own_descriptor_accepted

/-- Each access to the carried `Y` whose site carries `X`'s descriptor is no valid translation. -/
theorem carried_access_with_descriptor_of_x_rejected :
    ¬ valid true ldsfld (withX true ldsfld) ∧ ¬ valid true ldsflda (withX true ldsflda) ∧
    ¬ valid true stsfld (withX true stsfld) ∧ ¬ valid true ldtoken (withX true ldtoken) := by
  decide +kernel
#print axioms carried_access_with_descriptor_of_x_rejected

/-! ## An owner no slice carries -/

/-- Whether decoding the body accessing `Y` of `Ext.Point` fails on the refusal of its token. -/
private def refusedAtY (opcode : Nat) : Bool :=
  match checkBody (yBody false opcode) (raw opcode (yField false) (returnType opcode)) [] with
  | .error (.metadata (.unboundStaticField token)) =>
    token == (slice false (resultBytes opcode)).2.1
  | _ => false

/-- Each access to `Y` of `Ext.Point` fails on its token, whichever descriptor its site
    carries, and is no valid translation. -/
theorem uncarried_access_rejected :
    ([ldsfld, ldsflda, stsfld, ldtoken].all refusedAtY) = true ∧
    ¬ valid false ldsfld (withX false ldsfld) ∧ ¬ valid false ldsflda (withX false ldsflda) ∧
    ¬ valid false stsfld (withX false stsfld) ∧ ¬ valid false ldtoken (withX false ldtoken) ∧
    ¬ valid false ldsfld (withY false ldsfld) ∧ ¬ valid false ldsflda (withY false ldsflda) ∧
    ¬ valid false stsfld (withY false stsfld) ∧ ¬ valid false ldtoken (withY false ldtoken) := by
  decide +kernel
#print axioms uncarried_access_rejected

/-! ## The platform constant field -/

/-- The result type of the method using `opcode` on `IsLittleEndian`, and its signature bytes. -/
private def endianReturn (opcode : Nat) : TypeExpr :=
  if opcode == ldsfld then littleEndianField.type
  else if opcode == ldsflda then .byref littleEndianField.type else .void
private def endianResult (opcode : Nat) : List Nat :=
  if opcode == ldsfld then [0x02] else if opcode == ldsflda then [0x10, 0x02] else [0x01]

/-- The decoding of the body accessing `IsLittleEndian` with `opcode`. -/
private def endianDecoding (opcode : Nat) : Option BodyError :=
  let world := slice false (endianResult opcode)
  match checkBody (body opcode littleEndianField (endianReturn opcode) world.1 world.2.2)
      (raw opcode littleEndianField (endianReturn opcode)) [] with
  | .ok _ => none
  | .error found => some found

/-- `IsLittleEndian` binds for `ldsfld`, and every other static field instruction fails on its
    token. -/
theorem endian_field_only_loaded :
    endianDecoding ldsfld = none ∧
    ([ldsflda, stsfld, ldtoken].all fun opcode => match endianDecoding opcode with
      | some (.mismatchedToken _ token) => token == (slice false (endianResult opcode)).2.2
      | _ => false) = true := by
  decide +kernel
#print axioms endian_field_only_loaded

/-- The evidence of `ldsfld IsLittleEndian; ret`. -/
private def endianEvidence : MethodEvidence :=
  let world := slice false (endianResult ldsfld)
  let original := raw ldsfld littleEndianField (endianReturn ldsfld)
  let decoded := body ldsfld littleEndianField (endianReturn ldsfld) world.1 world.2.2
  { original, body := decoded, arguments := [], closed := original,
    parameterInput := { arguments := [], locals := [], code := [.other, .other] },
    reachable := [true, true], featureStates := [unknown 0, unknown 1],
    scalarStates := [some [], some [.word32]], layoutUses := [], assembly := pin,
    signature := (spelled? decoded.names.signature).getD "" }

/-- A descriptor of `IsLittleEndian` whose constructor stores 0. -/
private def endianDescriptor : StaticDescriptor :=
  { identity := 3, field := littleEndianField, bytes := [0], scalar := some false,
    initializer := some { method := 0, literal := some (.i32 0), arguments := [] } }

/-- `ldsfld IsLittleEndian` emitted as a static load, its site carrying a descriptor of the
    field that holds 0, is no valid translation: the feature check admits only the constant. -/
theorem endian_field_as_static_load_rejected :
    ¬ TranslationValid [] #[] [] [endianEvidence] []
      [{ locals := [], returnsValue := true,
         declared := DeclaredSignature.ofRaw endianEvidence.original,
         code := [.ldsfld littleEndianField, .ret],
         staticSites := [(0, endianDescriptor)] }] := by
  decide +kernel
#print axioms endian_field_as_static_load_rejected

end Tests.StaticFieldSites
