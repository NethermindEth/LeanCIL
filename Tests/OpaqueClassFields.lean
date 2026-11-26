import CIL.Extraction.Translation
import Tests.BodyEncoding

/-!
# Class fields of types outside the model

`Fixture` of `T` holds fields typed `object`, `List<int>`, `IList<int>`, `Func<int>`, the value
type `ValueTuple<int, int>`, a generic parameter, a modified `object` and a `Fixture`, and
`Holder` a static `object`. Binding admits each generic class instance as an `apply` chain over a
class head and `object` as `System.Object` of the primitive assembly, and refuses a head of the
other kind, a wrong argument, a claimed `string`, a parameter, a modifier and the static. A load
of such a field pushes an opaque reference, which another such field stores, which a type test
turns into an object, and which no receiver, catalog-typed field or array operation takes.
-/

namespace Tests.OpaqueClassFields

open CIL CIL.Extraction Tests.MetadataBuilder

private def pin : AssemblyPin := ⟨unsignedAssembly name!"T"⟩
/-- The scope text of `pin`'s types. -/
private def pinScope : String := "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def int32 : TypeExpr := .primitive .int32
private def int64 : TypeExpr := .primitive .int64
private def fixture : TypeExpr := .object pinScope "Fixture"
private def holder : TypeExpr := .object pinScope "Holder"
private def systemObject : TypeExpr := .object runtimeScope "System.Object"

/-- A generic class instance of the primitive assembly, `name` closed at `arguments`. -/
private def classOf (name : String) (arguments : List TypeExpr) : TypeExpr :=
  arguments.foldl .apply (.objectConstructor runtimeScope name)

/-- The same instance stated with a value head. -/
private def valueOf (name : String) (arguments : List TypeExpr) : TypeExpr :=
  arguments.foldl .apply (.constructor runtimeScope name)

private def listName : String := "System.Collections.Generic.List`1"
private def tupleName : String := "System.ValueTuple`2"

/-- The tokens of the fields of `Fixture`, in declaration order, and of the static of `Holder`. -/
private structure Tokens where
  object : Nat
  list : Nat
  interfaceList : Nat
  function : Nat
  tuple : Nat
  parameter : Nat
  modified : Nat
  catalog : Nat
  static : Nat

/-- The coded `TypeDefOrRef` of a `TypeRef` token. -/
private def referenceCoded (token : Nat) : Nat := (token - 0x01000000) * 4 + 1

/-- `T` with the classes `Fixture` and `Holder` and the fields this file describes. -/
private def world : Step Tokens := do
  let runtimeName ← string "System.Runtime"
  let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtimeName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let systemName ← string "System"
  let collectionsName ← string "System.Collections.Generic"
  let servicesName ← string "System.Runtime.CompilerServices"
  let objectRef ← row Table.typeRef [1 * 4 + 2, ← string "Object", systemName]
  let listRef ← row Table.typeRef [1 * 4 + 2, ← string "List`1", collectionsName]
  let interfaceRef ← row Table.typeRef [1 * 4 + 2, ← string "IList`1", collectionsName]
  let functionRef ← row Table.typeRef [1 * 4 + 2, ← string "Func`1", systemName]
  let tupleRef ← row Table.typeRef [1 * 4 + 2, ← string "ValueTuple`2", systemName]
  let volatileRef ← row Table.typeRef [1 * 4 + 2, ← string "IsVolatile", servicesName]
  let _ ← row Table.typeDef [0, ← string "<Module>", 0, 0, 1, 1]
  let base := referenceCoded objectRef
  let owner ← row Table.typeDef [1, ← string "Fixture", 0, base, 1, 1]
  let instanceFlags := 0x0006
  let typed (name : String) (signature : List Nat) : Step Nat := do
    let field ← row Table.field [instanceFlags, ← string name, ← blob (0x06 :: signature)]
    link linkDeclaring field 0 owner
    pure field
  let object ← typed "O" [0x1C]
  let list ← typed "L" [0x15, 0x12, referenceCoded listRef, 1, 0x08]
  let interfaceList ← typed "I" [0x15, 0x12, referenceCoded interfaceRef, 1, 0x08]
  let function ← typed "F" [0x15, 0x12, referenceCoded functionRef, 1, 0x08]
  let tuple ← typed "V" [0x15, 0x11, referenceCoded tupleRef, 2, 0x08, 0x08]
  let parameter ← typed "P" [0x13, 0]
  let modified ← typed "M" [0x1F, referenceCoded volatileRef, 0x1C]
  let catalog ← typed "C" [0x12, (owner - 0x02000000) * 4]
  let holderType ← row Table.typeDef [1, ← string "Holder", 0, base, 9, 1]
  let static ← row Table.field [0x0016, ← string "S", ← blob [0x06, 0x1C]]
  link linkDeclaring static 0 holderType
  pure { object, list, interfaceList, function, tuple, parameter, modified, catalog, static }

private def slice : MetadataSlice × Tokens := build world (bytesOf "T")

/-- A type of `System.Runtime`'s `System.Collections.Generic` namespace of this kind. -/
private def collectionType (name : String) (kind : PlatformKind) : PlatformDefinition :=
  { assembly := runtimeAssembly, parts := [bytesOf "System.Collections.Generic", bytesOf name],
    kind }

/-- The platform definitions of the types the fields and the classes' base name. -/
private def fieldPlatform : PlatformTable := platform_table%
  [runtimeType "Object" .objectRoot, collectionType "List`1" (.genericClass 1),
   collectionType "IList`1" (.genericInterface 1), runtimeType "Func`1" (.genericClass 1),
   runtimeType "ValueTuple`2" .valuePair]

/-- The error binding `token` to `operand` gives, or `none` when it is accepted. -/
private def check (token : Nat) (operand : RawOperand) : Option MetadataError :=
  let env := (MetadataEnv.ofSlices [·] (platform := fieldPlatform)) <$> slice.1.index
  match (do checkEntry (← env) 0 token operand) with
  | .ok _ => none
  | .error found => some found

/-- The instance field operand of `Fixture` at `index` holding `type`. -/
private def field (index : Nat) (type : TypeExpr) (name : MetadataName) : RawOperand :=
  .field fixture index type name false

private def tokens : Tokens := slice.2

/-- Each generic class instance binds as an `apply` chain over a class head and `object` as
    `System.Object` of the primitive assembly, whichever instruction uses the token. -/
theorem opaque_class_fields_bound :
    check tokens.object (field 0 systemObject name!"O") = none ∧
    check tokens.list (field 1 (classOf listName [int32]) name!"L") = none ∧
    check tokens.interfaceList
      (field 2 (classOf "System.Collections.Generic.IList`1" [int32]) name!"I") = none ∧
    check tokens.function (field 3 (classOf "System.Func`1" [int32]) name!"F") = none ∧
    check tokens.tuple (field 4 (valueOf tupleName [int32, int32]) name!"V") = none ∧
    check tokens.catalog (field 7 fixture name!"C") = none := by decide +kernel
#print axioms opaque_class_fields_bound

/-- A static `object`, `object` claimed as `string`, `ValueTuple<int, int>` under a class
    head, `List<int>` under a value head or as `List<long>`, a generic parameter and a modified
    `object` are each refused on their token. -/
theorem misstated_class_fields_refused :
    check tokens.static (.field holder 0 systemObject name!"S" true) =
      some (.operandMismatch tokens.static) ∧
    check tokens.static (.field holder 0 (.atom runtimeScope "System.Object" .classType) name!"S"
        true) =
      none ∧
    check tokens.object (field 0 (.object runtimeScope "System.String") name!"O") =
      some (.operandMismatch tokens.object) ∧
    check tokens.tuple (field 4 (classOf tupleName [int32, int32]) name!"V") =
      some (.operandMismatch tokens.tuple) ∧
    check tokens.list (field 1 (valueOf listName [int32]) name!"L") =
      some (.operandMismatch tokens.list) ∧
    check tokens.list (field 1 (classOf listName [int64]) name!"L") =
      some (.operandMismatch tokens.list) ∧
    check tokens.parameter (field 5 (.parameter 0) name!"P") =
      some (.operandMismatch tokens.parameter) ∧
    check tokens.parameter (field 5 (.object runtimeScope "T") name!"P") =
      some (.operandMismatch tokens.parameter) ∧
    check tokens.modified (field 6 systemObject name!"M") =
      some (.operandMismatch tokens.modified) := by decide +kernel
#print axioms misstated_class_fields_refused

/-! ## Stack kinds -/

private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction :=
  ⟨0, opcode, operand⟩

/-- An instance method of `Fixture` taking a `Fixture`, with `code`. -/
private def method (code : List RawInstruction) : RawMethod :=
  { token := 0x06000001, owner := pinScope ++ "::Fixture", hasThis := true,
    receiverClass := some fixture, explicitThis := false, callingConvention := 0, attributes := 0,
    implementation := 0, returnType := .void, parameters := [fixture], locals := [],
    initLocals := false, maxStack := 2, genericParameters := [], code }

private def unknown (count : Nat) : Option FeatureState := some ⟨List.replicate count none, []⟩

/-- The field of `Fixture` at `index` holding `type`, as an instruction names it. -/
private def fieldRef (index : Nat) (type : TypeExpr) (name : MetadataName) : FieldRef :=
  { owner := fixture, index := index, type := type, name := name }

/-- `this.F = other.F` for the field `F` at `index` holding `type`, with an opaque reference
    between the load and the store. -/
private def copies (index : Nat) (type : TypeExpr) (name : MetadataName) : Bool :=
  let operand := field index type name
  let raw := method [i 2, i 3, i 123 operand, i 125 operand, i 42]
  let reference := fieldRef index type name
  decide (ScalarFlowValid raw [unknown 0, unknown 1, unknown 2, unknown 2, unknown 0]
    [some [], some [.object], some [.object, .object], some [.opaque, .object], some []]
    [.ldarg 0, .ldarg 1, .ldfld reference, .stfld reference, .ret])

/-- A record copy of each such field loads an opaque reference and stores it. -/
theorem opaque_fields_copied :
    copies 0 systemObject name!"O" = true ∧
    copies 1 (classOf listName [int32]) name!"L" = true ∧
    copies 2 (classOf "System.Collections.Generic.IList`1" [int32]) name!"I" = true ∧
    copies 3 (classOf "System.Func`1" [int32]) name!"F" = true := by decide +kernel
#print axioms opaque_fields_copied

/-- Whether `stfld` of the field at `index` holding `type` takes `value` on an object. -/
private def stores (index : Nat) (type : TypeExpr) (name : MetadataName) (value : ScalarKind) :
    Bool :=
  scalarEmissionMatches none (some (i 3)) (i 125 (field index type name)) [value, .object]
    (.stfld (fieldRef index type name))

/-- The method `Fixture::Run()`, called with a receiver. -/
private def runMethod : MethodRef :=
  { owner := fixture, name := name!"Run", hasThis := true, genericArity := 0,
    returnType := .void, parameters := [] }

/-- The call of `runMethod`, linked to the second method of `T`. -/
private def run : CallSite :=
  { method := runMethod, declared := { convention := 0x20 },
    target := .managed 0x06000002, typeArguments := [],
    parameterCount := 0, returnsValue := false }

/-- An opaque reference is no `Fixture` to store, call or read through, and no array to measure;
    `castclass Fixture` turns it into an object that is. `object` also stores an object, a
    string or a class array, but not a value array or what `box` leaves. -/
theorem opaque_references_not_read_through :
    stores 7 fixture name!"C" .opaque = false ∧
    scalarTransfer (method []) (i 116 (.type fixture)) [.opaque] = some [.object] ∧
    scalarTransfer (method []) (i 117 (.type fixture)) [.opaque] = some [.object] ∧
    stores 7 fixture name!"C" .object = true ∧
    scalarTransfer (method []) (i 111 (.call run)) [.opaque] = none ∧
    scalarTransfer (method []) (i 111 (.call run)) [.object] = some [] ∧
    scalarTransfer (method []) (i 123 (field 7 fixture name!"C")) [.opaque] = some [.object] ∧
    scalarEmissionMatches none (some (i 3)) (i 123 (field 7 fixture name!"C")) [.opaque]
      (.ldfld (fieldRef 7 fixture name!"C")) = false ∧
    scalarTransfer (method []) (i 142) [.opaque] = none ∧
    scalarTransfer (method []) (i 142) [.object] = some [.native] ∧
    stores 0 systemObject name!"O" .object = true ∧
    stores 0 systemObject name!"O" .nullObject = true ∧
    stores 0 systemObject name!"O" (.array .signed32) = false ∧
    scalarTransfer (method []) (i 140 (.type int32)) [.word32] = some [.other] ∧
    stores 0 systemObject name!"O" .other = false ∧
    stores 1 (classOf listName [int32]) name!"L" .object = false := by decide +kernel
#print axioms opaque_references_not_read_through

end Tests.OpaqueClassFields
