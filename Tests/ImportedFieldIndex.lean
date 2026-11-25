import CIL.Extraction.Translation
import Tests.BodyEncoding

/-!
# Instance fields of an unpinned owner

`T` names the type `Ext.Point` of an assembly `Ext` that no slice carries, and its fields `X`
and `Y`, both `int`, by member references. No carried field list gives the position of either,
so metadata binding refuses each as an instance field, at any index and whether the operand names
`Ext.Point` as a struct or as a class. A method `M(ref Ext.Point)` whose body loads, addresses or
stores `Y` through its token fails every evidence check, with the emitted access at the offset of
`X`. `M(Ext.Point)` fails earlier, on its own signature, since no carried slice defines the class
its parameter names, and is no valid translation with the access at the slot of `X`. A
parameterless `M()` that reaches `Y` of the class through `ldnull` names `Ext.Point` only in
the operand and fails on the `Y` token. An operand that flags `Y` static fails on its token for
the struct and for the parameterless class method, since no carried row gives a static of
`Ext.Point` either, and on the signature for `M(Ext.Point)`. The platform pair binds `Item1`
and `Item2` at indices 0 and 1 for primitive arguments of equal storage width. Its signature
must mark the head as a value type, and its TypeRef must name the exact runtime assembly.
-/

namespace Tests.ImportedFieldIndex

open CIL CIL.Extraction Tests.MetadataBuilder Tests.BodyEncoding

private def pin : AssemblyPin := ⟨unsignedAssembly name!"T"⟩
/-- The scope text of `pin`'s types. -/
private def pinScope : String := "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def extScope : String := "Ext, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def int32 : TypeExpr := .primitive .int32
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

/-- `T` with `static M(p)`, `p` a `ref Ext.Point` struct or an `Ext.Point` class, or with no
    parameter when `parameterless`, and the result `opcode` gives, and the references to
    `Ext.Point.X` and `Ext.Point.Y`, whose tokens it returns. -/
private def world (classOwner : Bool) (opcode : Nat) (parameterless := false) :
    Step (Nat × Nat) := do
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
  let parameter :=
    if parameterless then []
    else if classOwner then [0x12, pointCoded] else [0x10, 0x11, pointCoded]
  let count := if parameterless then 0 else 1
  let methodBlob ← blob ([0x00, count] ++ resultBytes opcode ++ parameter)
  let definition ← row Table.methodDef [0, 0, 0, methodName, methodBlob, 1]
  link linkDeclaring definition 0 owner
  let intField ← blob [0x06, 0x08]
  let parent := (pointRef - 0x01000000) * 8 + 1
  let xName ← string "X"
  let yName ← string "Y"
  let xRef ← row Table.memberRef [parent, xName, intField]
  let yRef ← row Table.memberRef [parent, yName, intField]
  pure (xRef, yRef)

private def slice (classOwner : Bool) (opcode : Nat) (parameterless := false) :
    MetadataSlice × Nat × Nat :=
  build (world classOwner opcode parameterless) (bytesOf "T")

/-- `Ext.Point` as a platform definition of this kind. -/
private def pointDefinition (kind : PlatformKind) : PlatformDefinition :=
  { scope := bytesOf extScope, parts := [bytesOf "Ext", bytesOf "Point"], kind }

/-- The field owner has value storage. -/
private def structPlatform : PlatformTable := platform_table%
  [runtimeType "Object" .objectRoot, pointDefinition .valueType]

/-- The field owner has reference storage. -/
private def classPlatform : PlatformTable := platform_table%
  [runtimeType "Object" .objectRoot, pointDefinition .classType]

/-- The platform definitions of a world: `Ext.Point` is the class or the struct its signature
    reads it as. -/
private def pointPlatform (classOwner : Bool) : PlatformTable :=
  if classOwner then classPlatform else structPlatform

/-- The error checking `operand` against `token` gives, or `none` when it is accepted, with
    `Ext.Point` defined as the kind the operand's owner names. -/
private def check (token : Nat) (operand : RawOperand) : Option MetadataError :=
  let platform := match operand with
    | .field owner .. => pointPlatform (owner == pointClass)
    | _ => structPlatform
  match (do
    let env := MetadataEnv.ofSlices [← (slice false ldfld).1.index] (platform := platform)
    checkEntry env 0 token operand) with
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

/-- The receiver opcode of the body: `ldnull` in the parameterless method, else `ldarg.0`. -/
private def receiverOpcode (parameterless : Bool) : Nat := if parameterless then 0x14 else 0x02

/-- The body `ldarg.0; ldfld Y; ret`, `ldarg.0; ldflda Y; ret` or `ldarg.0; ldc.i4.1; stfld Y;
    ret` with `Y` claimed at `index`, and static when `flagged`, over `p` of type `owner`, or
    over `ldnull` in place of `ldarg.0` when `parameterless`. -/
private def raw (owner : TypeExpr) (opcode index : Nat) (flagged parameterless := false) :
    RawMethod :=
  let access : RawOperand := .field owner index int32 name!"Y" flagged
  let receiver := receiverOpcode parameterless
  { token := 0x06000001, owner := pinScope ++ "::Fixture", hasThis := false,
    explicitThis := false, callingConvention := 0, attributes := 0, implementation := 0,
    returnType :=
      if opcode == ldfld then int32 else if opcode == ldflda then .byref int32 else .void,
    parameters :=
      if parameterless then [] else [if owner == pointClass then pointClass else .byref point],
    locals := [], initLocals := false, maxStack := 8, genericParameters := [],
    code :=
      if opcode == stfld then
        [⟨0, receiver, .none⟩, ⟨1, 0x17, .none⟩, ⟨2, stfld, access⟩, ⟨7, 0x2A, .none⟩]
      else [⟨0, receiver, .none⟩, ⟨1, opcode, access⟩, ⟨6, 0x2A, .none⟩] }

/-- `Ext.Point` as CoreCLR lays it out: `X` at 0, `Y` at 4. -/
private def rawLayouts : List RawLayout :=
  [{ identity := extScope ++ "::Ext.Point", explicit := false, packing := 0, declaredSize := 0,
     declaration := [⟨name!"Ext", name!"Point"⟩],
     fields := [{ type := .signed32 }, { type := .signed32 }] }]

/-- The bytes and token table of `raw`, over the metadata of its world. -/
private def body (owner : TypeExpr) (opcode index : Nat) (flagged parameterless := false) :
    BodyEvidence :=
  let world := slice (owner == pointClass) opcode parameterless
  let token := MetadataBuilder.littleEndian 4 world.2.2
  let receiver := receiverOpcode parameterless
  let bytes :=
    if opcode == stfld then [8 * 4 + 2, receiver, 0x17, stfld] ++ token ++ [0x2A]
    else [7 * 4 + 2, receiver, opcode] ++ token ++ [0x2A]
  let classOwner := owner == pointClass
  let method := raw owner opcode index flagged parameterless
  let result := evidenceOf bytes [(world.2.2, .field owner index int32 name!"Y" flagged)]
    { own := world.1 } method (pointPlatform classOwner)
  { result with layoutDeclarations := if classOwner then #[] else layoutDeclarations rawLayouts }

/-- Whether decoding the body fails on exactly the refusal of its `Y` token. -/
private def refusedAtY (owner : TypeExpr) (opcode index : Nat) (parameterless := false) : Bool :=
  match checkBody (body owner opcode index (parameterless := parameterless))
    (raw owner opcode index (parameterless := parameterless)) [] with
  | .error (.metadata (.unboundInstanceField token)) =>
    token == (slice (owner == pointClass) opcode).2.2
  | _ => false

/-- Whether decoding the body fails on the signature of `M`, whose parameter names a class no
    carried slice defines, before any field operand is bound. -/
private def refusedAtSignature (opcode index : Nat) (flagged := false) : Bool :=
  match checkBody (body pointClass opcode index flagged) (raw pointClass opcode index flagged) []
  with
  | .error (.metadata (.methodMismatch token)) => token == (raw pointClass opcode index).token
  | _ => false

/-- Whether decoding the body with `Y` flagged static fails on its token, which names a static
    of a type no slice carries. -/
private def flaggedRefused (owner : TypeExpr) (opcode : Nat) (parameterless := false) : Bool :=
  match checkBody (body owner opcode 0 true parameterless) (raw owner opcode 0 true parameterless)
    [] with
  | .error (.metadata (.unboundStaticField token)) =>
    token == (slice (owner == pointClass) opcode parameterless).2.2
  | _ => false

private def evidence (owner : TypeExpr) (opcode index : Nat) (flagged := false) :
    MethodEvidence :=
  let classOwner := owner == pointClass
  let unknown (count : Nat) : Option FeatureState := some ⟨List.replicate count none, []⟩
  let argument : StorageType := if classOwner then .object else .reference
  let receiver : ScalarKind := if classOwner then .object else .reference
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
    layoutUses := [],
    assembly := pin,
    signature := (spelled? (body owner opcode index flagged).names.signature).getD "" }

private def layouts : Array ComputedLayout :=
  #[⟨{ size := 8, fields := [{ offset := 0, width := 4 }, { offset := 4, width := 4 }] }, 4⟩]

/-- The emitted struct method, accessing `Y` at the claimed index. -/
private def structMethod (opcode index : Nat) : Method :=
  let field : FieldRef := { owner := point, index, type := int32, name := name!"Y" }
  { locals := [], returnsValue := opcode != stfld,
    declared := DeclaredSignature.ofRaw (raw point opcode 0),
    code :=
      if opcode == ldfld then [.ldarg 0, .ldfld field, .ret]
      else if opcode == ldflda then [.ldarg 0, .ldflda field, .ret]
      else [.ldarg 0, .ldc_i4 1, .stfld field, .ret],
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
    ¬ TranslationValid rawLayouts layouts [] structPlatform [evidence point ldfld 0] []
      [structMethod ldfld 0] ∧
    ¬ TranslationValid rawLayouts layouts [] structPlatform [evidence point ldflda 0] []
      [structMethod ldflda 0] ∧
    ¬ TranslationValid rawLayouts layouts [] structPlatform [evidence point stfld 0] []
      [structMethod stfld 0] := by
  decide +kernel
#print axioms struct_access_of_y_at_offset_of_x_rejected

/-- Each class access to `Y` at the slot of index 0, which `X` shares, fails on the signature of
    its method and is no valid translation. -/
theorem class_access_of_y_at_slot_of_x_rejected :
    ([ldfld, ldflda, stfld].all fun opcode => refusedAtSignature opcode 0) = true ∧
    ¬ TranslationValid [] #[] [] classPlatform [evidence pointClass ldfld 0] []
      [classMethod ldfld 0] ∧
    ¬ TranslationValid [] #[] [] classPlatform [evidence pointClass ldflda 0] []
      [classMethod ldflda 0] ∧
    ¬ TranslationValid [] #[] [] classPlatform [evidence pointClass stfld 0] []
      [classMethod stfld 0] := by
  decide +kernel
#print axioms class_access_of_y_at_slot_of_x_rejected

/-- The parameterless class method, whose signature does not name `Ext.Point`, reaches the field
    check and fails on its `Y` token for each instance field instruction. -/
theorem class_access_of_y_without_signature_rejected :
    ([ldfld, ldflda, stfld].all fun opcode => refusedAtY pointClass opcode 0 true) = true := by
  decide +kernel
#print axioms class_access_of_y_without_signature_rejected

/-- An operand flagging `Y` static fails each instance field instruction on its token for the
    struct and for the parameterless class method, since no carried row gives a static of
    `Ext.Point`, and on its method's signature for `M(Ext.Point)`; none is a valid translation. -/
theorem static_flagged_access_of_y_rejected :
    ([ldfld, ldflda, stfld].all fun opcode =>
      flaggedRefused point opcode && refusedAtSignature opcode 0 true &&
        flaggedRefused pointClass opcode true) = true ∧
    ¬ TranslationValid rawLayouts layouts [] structPlatform [evidence point ldfld 0 true] []
      [structMethod ldfld 0] ∧
    ¬ TranslationValid rawLayouts layouts [] structPlatform [evidence point ldflda 0 true] []
      [structMethod ldflda 0] ∧
    ¬ TranslationValid rawLayouts layouts [] structPlatform [evidence point stfld 0 true] []
      [structMethod stfld 0] ∧
    ¬ TranslationValid [] #[] [] classPlatform [evidence pointClass ldfld 0 true] []
      [classMethod ldfld 0] ∧
    ¬ TranslationValid [] #[] [] classPlatform [evidence pointClass ldflda 0 true] []
      [classMethod ldflda 0] ∧
    ¬ TranslationValid [] #[] [] classPlatform [evidence pointClass stfld 0 true] []
      [classMethod stfld 0] := by
  decide +kernel
#print axioms static_flagged_access_of_y_rejected

/-! ## The platform pair -/

/-- A fixture that returns the member tokens for Item1, Item2 and Rest in that order. -/
private abbrev PairWorld := Step (Nat × Nat × Nat)

/-- A tuple with the given assembly, type marker, arity and argument bytes. Its member
    references declare Item1 and Rest as !0 and Item2 with the signature type `second`. -/
private def pairWorldWith (arguments : List Nat) (second := [0x13, 0x01])
    (assembly := runtimeAssembly) (marker := 0x11) (headArity := 2) (arity := 2)
    (first := [0x13, 0x00]) : PairWorld := do
  let name ← Tests.MetadataBuilder.stringBytes (assembly.name.bytes?.getD [])
  let culture ← Tests.MetadataBuilder.stringBytes (assembly.culture.bytes?.getD [])
  let publicKeyToken ← blob (assembly.publicKeyToken.elim [] fun key => fixedDigits 8 8 key [])
  let version := assembly.version
  let _ ← row Table.assemblyRef
    [version.major, version.minor, version.build, version.revision, 0, publicKeyToken, name,
     culture, 0]
  modify fun builder => { builder with corlib := 1 }
  let tupleName ← string s!"ValueTuple`{headArity}"
  let systemName ← string "System"
  let tupleRef ← row Table.typeRef [1 * 4 + 2, tupleName, systemName]
  let tupleBlob ← blob ([0x15, marker, tokenRow tupleRef * 4 + 1, arity] ++ arguments)
  let tupleSpec ← row Table.typeSpec [tupleBlob]
  let parent := (tupleSpec - 0x1B000000) * 8 + 4
  let firstSignature ← blob (0x06 :: first)
  let secondSignature ← blob (0x06 :: second)
  let firstName ← string "Item1"
  let secondName ← string "Item2"
  let restName ← string "Rest"
  let firstRef ← row Table.memberRef [parent, firstName, firstSignature]
  let secondRef ← row Table.memberRef [parent, secondName, secondSignature]
  let restRef ← row Table.memberRef [parent, restName, firstSignature]
  pure (firstRef, secondRef, restRef)

/-- `ValueTuple<int, int>` with `Item2 : !1`. -/
private def pairWorld : PairWorld := pairWorldWith [0x08, 0x08]

private def pairSlice : MetadataSlice × Nat × Nat × Nat :=
  build pairWorld (bytesOf "T")

private def pair : TypeExpr :=
  .aggregate (s!"{runtimeScope}::System.ValueTuple`2<{runtimeScope}::System.Int32,{runtimeScope}::System.Int32>") 0

/-- The platform definition of the pair. -/
private def pairPlatform : PlatformTable := platform_table% [runtimeType "ValueTuple`2" .valuePair]

/-- The error checking `operand` against `token` of the pair world gives, if any. -/
private def checkPair (token : Nat) (operand : RawOperand) (slice := pairSlice.1) (platform := pairPlatform) :
    Option MetadataError :=
  match (do checkEntry (MetadataEnv.ofSlices [← slice.index] (platform := platform)) 0 token operand) with
  | .ok _ => none
  | .error found => some found

/-- `Item1` and `Item2` are the pair's fields 0 and 1; `Rest` is refused at index 0 as an
    instance member, and as a static since the pair is an instantiation. -/
theorem pair_items_bound_and_other_members_refused :
    checkPair pairSlice.2.1 (.field pair 0 int32 name!"Item1" false) = none ∧
    checkPair pairSlice.2.2.1 (.field pair 1 int32 name!"Item2" false) = none ∧
    checkPair pairSlice.2.2.2 (.field pair 0 int32 name!"Rest" false) =
      some (.unboundInstanceField pairSlice.2.2.2) ∧
    checkPair pairSlice.2.2.2 (.field pair 0 int32 name!"Rest" true) =
      some (.instantiatedStaticField pairSlice.2.2.2) := by decide +kernel
#print axioms pair_items_bound_and_other_members_refused

/-- Each primitive argument of Item1's owner must carry the signature's primitive scope. -/
theorem pair_argument_scopes_checked :
    let rejects := fun first second =>
      let owner := s!"{runtimeScope}::System.ValueTuple`2<{first}System.Int32,{second}System.Int32>"
      (checkPair pairSlice.2.1 (.field (.aggregate owner 0) 0 int32 name!"Item1" false)).isSome
    let scope := runtimeScope ++ "::"
    rejects "" scope && rejects scope "" && rejects "Other::" scope && rejects scope "Other::" :=
  by decide +kernel
#print axioms pair_argument_scopes_checked

/-- The error checking `operand` against the `Item2` reference of `pairWorldWith arguments
    second` gives, if any. -/
private def checkSecond (arguments second : List Nat) (operand : RawOperand) :
    Option MetadataError :=
  let (slice, _, token, _) := build (pairWorldWith arguments second) (bytesOf "T")
  checkPair token operand slice

/-- `ValueTuple<int, uint>` as the extractor names it. -/
private def mixedPair : TypeExpr :=
  .aggregate (s!"{runtimeScope}::System.ValueTuple`2<{runtimeScope}::System.Int32,{runtimeScope}::System.UInt32>") 0

/-- `Item2` declared `!0` is refused even where both arguments are `int`, and on
    `ValueTuple<int, uint>` a valid `Item2 : !1` holds the second argument, `uint`, not the
    first. -/
theorem pair_second_item_reads_its_own_declaration :
    checkSecond [0x08, 0x08] [0x13, 0x00] (.field pair 1 int32 name!"Item2" false) =
      some (.operandMismatch
        (build (pairWorldWith [0x08, 0x08] [0x13, 0x00]) (bytesOf "T")).2.2.1) ∧
    checkSecond [0x08, 0x09] [0x13, 0x01]
      (.field mixedPair 1 (.primitive .uint32) name!"Item2" false) = none ∧
    (checkSecond [0x08, 0x09] [0x13, 0x01] (.field mixedPair 1 int32 name!"Item2" false)).isSome =
      true := by decide +kernel
#print axioms pair_second_item_reads_its_own_declaration

/-- The field reference at the requested item position, checked against its claimed type. -/
private def itemError (world : PairWorld) (index : Nat) (owner held : TypeExpr)
    (platform := pairPlatform) :
    Option MetadataError :=
  let (slice, first, second, _) := build world (bytesOf "T")
  if index == 0 then checkPair first (.field owner index held name!"Item1" false) slice platform
  else checkPair second (.field owner index held name!"Item2" false) slice platform

/-- A member reference declaring the first int32 item as int64 fails signature binding. -/
theorem refuses_int64_first_item :
    itemError (pairWorldWith [0x08, 0x08] (first := [0x0A])) 0 pair int32 =
      some (.operandMismatch 0x0A000001) := by decide +kernel
#print axioms refuses_int64_first_item

/-- The extractor's aggregate operand for two tuple arguments in the given assembly. -/
private def tupleOwner (first second : String) (scope := runtimeScope) (layout := 0) : TypeExpr :=
  .aggregate (s!"{scope}::System.ValueTuple`2<{scope}::{first},{scope}::{second}>") layout

/-- The inner pair uses the same head as the outer pair (TypeRef row 1, coded index 5). -/
private def nestedWorld := pairWorldWith [0x15, 0x11, 5, 2, 0x08, 0x08, 0x08]

/-- The nested tuple has its own layout after the inner pair. -/
private def nestedOwner := tupleOwner "System.ValueTuple`2<System.Int32,System.Int32>"
  "System.Int32" (layout := 1)

/-- An aggregate argument prevents binding the outer pair's first item. -/
theorem refuses_nested_first_item :
    itemError nestedWorld 0 nestedOwner pair = some (.unboundInstanceField 0x0A000001) := by
  decide +kernel
#print axioms refuses_nested_first_item

/-- The scalar second item of the same outer pair has no certified index either. -/
theorem refuses_nested_second_item :
    itemError nestedWorld 1 nestedOwner int32 = some (.unboundInstanceField 0x0A000002) := by
  decide +kernel
#print axioms refuses_nested_second_item

/-- A pair with unequal primitive widths has no certified field order. -/
theorem refuses_unequal_width_pair :
    itemError (pairWorldWith [0x08, 0x0A]) 0 (tupleOwner "System.Int32" "System.Int64") int32 =
      some (.unboundInstanceField 0x0A000001) := by decide +kernel
#print axioms refuses_unequal_width_pair

/-- Two unsupported primitives have no certified storage width. -/
theorem refuses_single_pair :
    itemError (pairWorldWith [0x0C, 0x0C]) 0 (tupleOwner "System.Single" "System.Single")
      (.primitive .single) = some (.unboundInstanceField 0x0A000001) := by
  decide +kernel
#print axioms refuses_single_pair

/-- CoreCLR places the four-byte Item2 of (byte, uint) at offset 0. Its index cannot certify
    the sequential offset 4, even when the MemberRef correctly declares Item2 as !1. -/
theorem refuses_byte_uint_second_item :
    checkSecond [0x05, 0x09] [0x13, 0x01]
      (.field (tupleOwner "System.Byte" "System.UInt32") 1 (.primitive .uint32)
        name!"Item2" false) = some (.unboundInstanceField 0x0A000002) := by decide +kernel
#print axioms refuses_byte_uint_second_item

/-- Equal widths preserve both field positions across distinct primitive types. -/
theorem binds_equal_width_items :
    let bytes := pairWorldWith [0x05, 0x02]
    let owner := tupleOwner "System.Byte" "System.Boolean"
    itemError (pairWorldWith [0x08, 0x09]) 0 mixedPair int32 = none ∧
    itemError bytes 0 owner (.primitive .byte) = none ∧
    itemError bytes 1 owner (.primitive .boolean) = none := by decide +kernel
#print axioms binds_equal_width_items

/-- Repeating a CLASS marker in the operand cannot give the tuple a field index. -/
theorem refuses_class_marked_pair :
    let owner := TypeExpr.objectConstructor runtimeScope "System.ValueTuple`2"
    itemError (pairWorldWith [8, 8] (marker := 0x12)) 0 (.apply (.apply owner int32) int32)
      int32 = some (.platformKindMismatch 0x01000001) ∧
    itemError (pairWorldWith [8, 8] (marker := 0x12)) 0 (.apply (.apply owner int32) int32)
      int32 (restating pairPlatform "ValueTuple`2" (.genericClass 2)) =
      some (.unboundInstanceField 0x0A000001) := by decide +kernel
#print axioms refuses_class_marked_pair

/-- The first item with the same assembly scope in its reference and its operand. -/
private def scopedItem (assembly : AssemblyName) (scope := assembly.display) : Option MetadataError :=
  let claimed : PlatformDefinition :=
    ⟨bytesOf scope, [bytesOf "System", bytesOf "ValueTuple`2"], .valuePair⟩
  let platform : PlatformTable :=
    { includesScope := false, entries := SearchTree.ofSorted [(platformKey claimed.parts, [claimed])] }
  itemError (pairWorldWith [8, 8] (assembly := assembly)) 0
    (tupleOwner "System.Int32" "System.Int32" scope) (.atom scope "System.Int32") platform

/-- An unsigned reference cannot name the platform pair. -/
theorem refuses_unsigned_pair :
    scopedItem { runtimeAssembly with publicKeyToken := none } =
      some (.unsupportedAssemblyRef 0x23000001) := by decide +kernel
#print axioms refuses_unsigned_pair

/-- Two signed references with different eight-byte tokens identify different assemblies. -/
theorem refuses_other_signed_pair :
    scopedItem { runtimeAssembly with
      publicKeyToken := some (runtimeAssembly.publicKeyToken.getD 0 + 1) } =
      some (.unsupportedAssemblyRef 0x23000001) := by decide +kernel
#print axioms refuses_other_signed_pair

/-- A different reference assembly version cannot name the platform pair. -/
theorem refuses_other_version_pair :
    scopedItem { runtimeAssembly with version.revision := 1 }
      "System.Runtime, Version=11.0.0.1, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" =
      some (.unboundInstanceField 0x0A000001) := by cil_kernel_rfl
#print axioms refuses_other_version_pair

/-- A different core library cannot name the supported pair. -/
theorem refuses_mscorlib_pair :
    scopedItem { runtimeAssembly with
      name := name!"mscorlib", publicKeyToken := some 0xb77a5c561934e089 }
      "mscorlib, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089" =
      some (.unboundInstanceField 0x0A000001) := by cil_kernel_rfl
#print axioms refuses_mscorlib_pair

/-- A literal culture named neutral shares the empty culture's display spelling. -/
theorem refuses_literal_neutral_culture :
    let assembly := { runtimeAssembly with culture := name!"neutral" }
    itemError (pairWorldWith [8, 8] (assembly := assembly)) 0 pair int32 =
      some (.unsupportedAssemblyRef 0x23000001) := by decide +kernel
#print axioms refuses_literal_neutral_culture

/-- Three primitive arguments cannot use the two-item layout. -/
theorem refuses_three_item_tuple :
    itemError (pairWorldWith [8, 8, 8] (arity := 3)) 0
      (.aggregate (runtimeScope ++ "::System.ValueTuple`2<System.Int32,System.Int32,System.Int32>")
        0) int32 = some (.genericMismatch 0x01000001) := by decide +kernel
#print axioms refuses_three_item_tuple

/-- Two arguments cannot give the three-item head a pair layout. -/
theorem refuses_three_item_head :
    itemError (pairWorldWith [8, 8] (headArity := 3)) 0
      (.aggregate (runtimeScope ++ "::System.ValueTuple`3<System.Int32,System.Int32>") 0) int32 =
      some (.missingPlatformDefinition 0x01000001) ∧
    itemError (pairWorldWith [8, 8] (headArity := 3)) 0
      (.aggregate (runtimeScope ++ "::System.ValueTuple`3<System.Int32,System.Int32>") 0) int32
      (platform_table% [runtimeType "ValueTuple`3" (.genericValue 3)]) =
      some (.genericMismatch 0x01000001) := by decide +kernel
#print axioms refuses_three_item_head

/-- The pair's reference to `System.ValueTuple`2`, the first in its world. -/
private def tupleRef : Nat := 0x01000001

/-- `Item1` is bound only under a definition that states the pair: without the definition the
    pair's reference is refused, and under one that states a plain value type the item is. -/
theorem pair_items_need_the_pair_definition :
    checkPair pairSlice.2.1 (.field pair 0 int32 name!"Item1" false) = none ∧
    checkPair pairSlice.2.1 (.field pair 0 int32 name!"Item1" false)
        (platform := removing pairPlatform "ValueTuple`2") =
      some (.missingPlatformDefinition tupleRef) ∧
    checkPair pairSlice.2.1 (.field pair 0 int32 name!"Item1" false)
        (platform := restating pairPlatform "ValueTuple`2" (.genericValue 2)) =
      some (.platformKindMismatch pairSlice.2.1) := by decide +kernel
#print axioms pair_items_need_the_pair_definition

end Tests.ImportedFieldIndex
