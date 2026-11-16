import CIL.Extraction.Translation
import Tests.BodyEncoding

/-!
# Instance fields of an unpinned owner

`T` names the type `Ext.Point` of an assembly `Ext` that no slice carries, and its fields `X`
and `Y`, both `int`, by member references. No carried field list gives the position of either,
so metadata binding refuses each as an instance field, at any index and whether the operand names
`Ext.Point` as a struct or as a class. A method `M(ref Ext.Point)` or `M(Ext.Point)` whose body
loads, addresses or stores `Y` through its token fails every evidence check, with the emitted
access at the offset or slot of `X`, and so does an operand that flags `Y` static, since these
instructions take only instance fields. Of the platform pair `ValueTuple<int, int>`, `Item1` and
`Item2` keep indices 0 and 1 and any other member is refused.
-/

namespace Tests.ImportedFieldIndex

open CIL CIL.Extraction Tests.MetadataBuilder Tests.BodyEncoding

private def pin : AssemblyPin :=
  { identity := "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" }
private def extScope : String := "Ext, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def int32 : TypeExpr := .atom runtimeScope "System.Int32"
/-- `Ext.Point` as a struct and as a class; its member references admit either reading. -/
private def point : TypeExpr := .aggregate (extScope ++ "::Ext.Point") 0
private def pointClass : TypeExpr := .object extScope "Ext.Point"

/-- The field instructions under test: `ldfld`, `ldflda` and `stfld`. -/
private def ldfld : Nat := 0x7B
private def ldflda : Nat := 0x7C
private def stfld : Nat := 0x7D

/-- The signature bytes of the result of the method that accesses a field with `opcode`: the
    loaded `int`, a reference to it, or nothing after a store. -/
private def resultBytes (opcode : Nat) : List Nat :=
  if opcode == ldfld then [0x08] else if opcode == ldflda then [0x10, 0x08] else [0x01]

/-- `T` with `static M(p)`, `p` a `ref Ext.Point` struct or an `Ext.Point` class and the result
    `opcode` gives, and the references to `Ext.Point.X` and `Ext.Point.Y`, whose tokens it
    returns. -/
private def world (classOwner : Bool) (opcode : Nat) : Step (Nat × Nat) := do
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
  let moduleName ← string "<Module>"
  let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
  let fixtureName ← string "Fixture"
  let owner ← row Table.typeDef [1, fixtureName, 0, 1 * 4 + 1, 1, 1]
  let methodName ← string "M"
  let pointCoded := (pointRef - 0x01000000) * 4 + 1
  let parameter := if classOwner then [0x12, pointCoded] else [0x10, 0x11, pointCoded]
  let methodBlob ← blob ([0x00, 0x01] ++ resultBytes opcode ++ parameter)
  let definition ← row Table.methodDef [0, 0, 0, methodName, methodBlob, 1]
  link linkDeclaring definition 0 owner
  let intField ← blob [0x06, 0x08]
  let parent := (pointRef - 0x01000000) * 8 + 1
  let xName ← string "X"
  let yName ← string "Y"
  let xRef ← row Table.memberRef [parent, xName, intField]
  let yRef ← row Table.memberRef [parent, yName, intField]
  pure (xRef, yRef)

private def slice (classOwner : Bool) (opcode : Nat) : MetadataSlice × Nat × Nat :=
  build (world classOwner opcode) (bytesOf "T") pin.identity

/-- The error checking `operand` against `token` gives, or `none` when it is accepted. -/
private def check (token : Nat) (operand : RawOperand) : Option MetadataError :=
  match (do checkEntry (MetadataEnv.ofSlices [← (slice false ldfld).1.index]) 0 token operand) with
  | .ok _ => none
  | .error found => some found

private def xToken : Nat := (slice false ldfld).2.1
private def yToken : Nat := (slice false ldfld).2.2

/-- `X` and `Y` are refused as instance fields of the struct and of the class, at index 0 and at
    the position `Y` has in CoreCLR's layout. -/
theorem unpinned_instance_fields_refused :
    check xToken (.field point 0 int32 name!"X" false) = some (.unboundInstanceField xToken) ∧
    check yToken (.field point 0 int32 name!"Y" false) = some (.unboundInstanceField yToken) ∧
    check yToken (.field point 1 int32 name!"Y" false) = some (.unboundInstanceField yToken) ∧
    check xToken (.field pointClass 0 int32 name!"X" false) =
      some (.unboundInstanceField xToken) ∧
    check yToken (.field pointClass 0 int32 name!"Y" false) =
      some (.unboundInstanceField yToken) := by decide +kernel
#print axioms unpinned_instance_fields_refused

/-- The body `ldarg.0; ldfld Y; ret`, `ldarg.0; ldflda Y; ret` or `ldarg.0; ldc.i4.1; stfld Y;
    ret` with `Y` claimed at `index`, and static when `flagged`, over `p` of type `owner`. -/
private def raw (owner : TypeExpr) (opcode index : Nat) (flagged := false) : RawMethod :=
  let access : RawOperand := .field owner index int32 name!"Y" flagged
  { token := 0x06000001, owner := pin.identity ++ "::Fixture", hasThis := false,
    explicitThis := false, callingConvention := 0, attributes := 0, implementation := 0,
    returnType :=
      if opcode == ldfld then int32 else if opcode == ldflda then .byref int32 else .void,
    parameters := [if owner == pointClass then pointClass else .byref point],
    locals := [], initLocals := false, maxStack := 8, genericParameters := [],
    code :=
      if opcode == stfld then
        [⟨0, 0x02, .none⟩, ⟨1, 0x17, .none⟩, ⟨2, stfld, access⟩, ⟨7, 0x2A, .none⟩]
      else [⟨0, 0x02, .none⟩, ⟨1, opcode, access⟩, ⟨6, 0x2A, .none⟩] }

/-- The bytes and token table of `raw`, over the metadata of its world. -/
private def body (owner : TypeExpr) (opcode index : Nat) (flagged := false) : BodyEvidence :=
  let world := slice (owner == pointClass) opcode
  let token := MetadataBuilder.littleEndian 4 world.2.2
  let bytes :=
    if opcode == stfld then [8 * 4 + 2, 0x02, 0x17, stfld] ++ token ++ [0x2A]
    else [7 * 4 + 2, 0x02, opcode] ++ token ++ [0x2A]
  evidenceOf bytes [(world.2.2, .field owner index int32 name!"Y" flagged)] { own := world.1 }
    (raw owner opcode index flagged)

/-- Whether decoding the body fails on exactly the refusal of its `Y` token. -/
private def refusedAtY (owner : TypeExpr) (opcode index : Nat) : Bool :=
  match checkBody (body owner opcode index) (raw owner opcode index) [] with
  | .error (.metadata (.unboundInstanceField token)) =>
    token == (slice (owner == pointClass) opcode).2.2
  | _ => false

/-- Whether decoding the body with `Y` flagged static fails on its token, before binding. -/
private def flaggedRefused (owner : TypeExpr) (opcode : Nat) : Bool :=
  match checkBody (body owner opcode 0 true) (raw owner opcode 0 true) [] with
  | .error (.mismatchedToken _ token) => token == (slice (owner == pointClass) opcode).2.2
  | _ => false

private def evidence (owner : TypeExpr) (opcode index : Nat) (flagged := false) :
    MethodEvidence :=
  let classOwner := owner == pointClass
  let unknown (count : Nat) : Option FeatureState := some ⟨List.replicate count none, []⟩
  let argument : StorageType := if classOwner then .object else .reference
  let receiver : ScalarKind := if classOwner then .object else .reference
  let access : FieldAccess :=
    if opcode == ldfld then .load else if opcode == ldflda then .address else .store
  let stored := opcode == stfld
  let operations : List ArgumentOp :=
    if stored then [.load 0, .other, .other, .other] else [.load 0, .other, .other]
  { original := raw owner opcode index flagged, body := body owner opcode index flagged,
    arguments := [], closed := raw owner opcode index flagged,
    parameterInput := { arguments := [argument], locals := [], code := operations },
    reachable := List.replicate (if stored then 4 else 3) true,
    featureStates :=
      if stored then [unknown 0, unknown 1, unknown 2, unknown 0]
      else [unknown 0, unknown 1, unknown 1],
    scalarStates :=
      if stored then [some [], some [receiver], some [.word32, receiver], some []]
      else [some [], some [receiver],
        some [if opcode == ldfld then .word32 else .reference]],
    layoutUses := if classOwner then [] else [.field (if stored then 2 else 1) 0 index access],
    assembly := pin,
    signature := (spelled? (body owner opcode index flagged).names.signature).getD "" }

/-- `Ext.Point` as CoreCLR lays it out: `X` at 0, `Y` at 4. -/
private def rawLayouts : List RawLayout :=
  [{ identity := extScope ++ "::Ext.Point", explicit := false, packing := 0, declaredSize := 0,
     fields := [{ type := .signed32 }, { type := .signed32 }] }]
private def layouts : Array ComputedLayout :=
  #[⟨{ size := 8, fields := [{ offset := 0, width := 4 }, { offset := 4, width := 4 }] }, 4⟩]

/-- The emitted struct method, accessing the field at `offset`. -/
private def structMethod (opcode offset : Nat) : Method :=
  { locals := [], returnsValue := opcode != stfld,
    declared := DeclaredSignature.ofRaw (raw point opcode 0),
    code :=
      if opcode == ldfld then [.ldarg 0, .fieldAt offset 4 false, .ret]
      else if opcode == ldflda then [.ldarg 0, .fieldAddress offset, .ret]
      else [.ldarg 0, .ldc_i4 1, .setFieldAt offset 4, .ret],
    environment := { rawLayouts := rawLayouts, layouts := layouts } }

/-- The emitted class method, accessing `Y` claimed at `index`. -/
private def classMethod (opcode index : Nat) : Method :=
  let field : FieldRef := { owner := pointClass, index, type := int32, name := name!"Y" }
  { locals := [], returnsValue := opcode != stfld,
    declared := DeclaredSignature.ofRaw (raw pointClass opcode 0),
    code :=
      if opcode == ldfld then [.ldarg 0, .ldfld field, .ret]
      else if opcode == ldflda then [.ldarg 0, .ldflda field, .ret]
      else [.ldarg 0, .ldc_i4 1, .stfld field, .ret] }

/-- Each struct access to `Y` through the offset of `X` fails on its token and is no valid
    translation. -/
theorem struct_access_of_y_at_offset_of_x_rejected :
    ([ldfld, ldflda, stfld].all fun opcode => refusedAtY point opcode 0) = true ∧
    ¬ TranslationValid rawLayouts layouts [] [evidence point ldfld 0] [] [structMethod ldfld 0] ∧
    ¬ TranslationValid rawLayouts layouts [] [evidence point ldflda 0] []
      [structMethod ldflda 0] ∧
    ¬ TranslationValid rawLayouts layouts [] [evidence point stfld 0] []
      [structMethod stfld 0] := by
  decide +kernel
#print axioms struct_access_of_y_at_offset_of_x_rejected

/-- Each class access to `Y` at the slot of index 0, which `X` shares, fails on its token and is
    no valid translation. -/
theorem class_access_of_y_at_slot_of_x_rejected :
    ([ldfld, ldflda, stfld].all fun opcode => refusedAtY pointClass opcode 0) = true ∧
    ¬ TranslationValid [] #[] [] [evidence pointClass ldfld 0] [] [classMethod ldfld 0] ∧
    ¬ TranslationValid [] #[] [] [evidence pointClass ldflda 0] [] [classMethod ldflda 0] ∧
    ¬ TranslationValid [] #[] [] [evidence pointClass stfld 0] [] [classMethod stfld 0] := by
  decide +kernel
#print axioms class_access_of_y_at_slot_of_x_rejected

/-- An operand flagging `Y` static, the form binding admits at index 0, fails each instance field
    instruction on its token, since those opcodes take only instance fields, and is no valid
    translation. -/
theorem static_flagged_access_of_y_rejected :
    ([point, pointClass].all fun owner =>
      [ldfld, ldflda, stfld].all fun opcode => flaggedRefused owner opcode) = true ∧
    ¬ TranslationValid rawLayouts layouts [] [evidence point ldfld 0 true] []
      [structMethod ldfld 0] ∧
    ¬ TranslationValid rawLayouts layouts [] [evidence point ldflda 0 true] []
      [structMethod ldflda 0] ∧
    ¬ TranslationValid rawLayouts layouts [] [evidence point stfld 0 true] []
      [structMethod stfld 0] ∧
    ¬ TranslationValid [] #[] [] [evidence pointClass ldfld 0 true] [] [classMethod ldfld 0] ∧
    ¬ TranslationValid [] #[] [] [evidence pointClass ldflda 0 true] [] [classMethod ldflda 0] ∧
    ¬ TranslationValid [] #[] [] [evidence pointClass stfld 0 true] [] [classMethod stfld 0] := by
  decide +kernel
#print axioms static_flagged_access_of_y_rejected

/-! ## The platform pair -/

/-- `T` with `System.ValueTuple<int, int>` and its members `Item1 : !0`, `Item2 : !1` and
    `Rest : !0`, the last a member the pair does not declare. -/
private def pairWorld : Step (Nat × Nat × Nat) := do
  let runtimeName ← string "System.Runtime"
  let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtimeName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let tupleName ← string "ValueTuple`2"
  let systemName ← string "System"
  let tupleRef ← row Table.typeRef [1 * 4 + 2, tupleName, systemName]
  let tupleBlob ← blob [0x15, 0x11, (tupleRef - 0x01000000) * 4 + 1, 2, 0x08, 0x08]
  let tupleSpec ← row Table.typeSpec [tupleBlob]
  let parent := (tupleSpec - 0x1B000000) * 8 + 4
  let firstSignature ← blob [0x06, 0x13, 0x00]
  let secondSignature ← blob [0x06, 0x13, 0x01]
  let firstName ← string "Item1"
  let secondName ← string "Item2"
  let restName ← string "Rest"
  let firstRef ← row Table.memberRef [parent, firstName, firstSignature]
  let secondRef ← row Table.memberRef [parent, secondName, secondSignature]
  let restRef ← row Table.memberRef [parent, restName, firstSignature]
  pure (firstRef, secondRef, restRef)

private def pairSlice : MetadataSlice × Nat × Nat × Nat :=
  build pairWorld (bytesOf "T") pin.identity

private def pair : TypeExpr :=
  .aggregate (runtimeScope ++ "::System.ValueTuple`2<System.Int32,System.Int32>") 0

/-- The error checking `operand` against `token` of the pair world gives, if any. -/
private def checkPair (token : Nat) (operand : RawOperand) : Option MetadataError :=
  match (do checkEntry (MetadataEnv.ofSlices [← pairSlice.1.index]) 0 token operand) with
  | .ok _ => none
  | .error found => some found

/-- `Item1` and `Item2` are the pair's fields 0 and 1; `Rest` is refused at index 0, as an
    instance and as a static member. -/
theorem pair_items_bound_and_other_members_refused :
    checkPair pairSlice.2.1 (.field pair 0 int32 name!"Item1" false) = none ∧
    checkPair pairSlice.2.2.1 (.field pair 1 int32 name!"Item2" false) = none ∧
    checkPair pairSlice.2.2.2 (.field pair 0 int32 name!"Rest" false) =
      some (.unboundInstanceField pairSlice.2.2.2) ∧
    checkPair pairSlice.2.2.2 (.field pair 0 int32 name!"Rest" true) =
      some (.unboundInstanceField pairSlice.2.2.2) := by decide +kernel
#print axioms pair_items_bound_and_other_members_refused

end Tests.ImportedFieldIndex
