import Tests.Support.EnumIdentity
import Tests.MetadataWorld

/-!
# Platform definitions the metadata checks rely on

Each check that relies on a type no carried slice defines reads the type's platform definition,
so a list with the entry removed or stating another kind is refused. A type reference outside the
carried slices takes its kind from its definition and refuses a signature that reads it as the
other kind; an external enum admits only the integer element type its definition states; a class
chain ends at the definition of `System.Object`; and a type is a value type or an enum through
its base only when the base is the definition of `System.ValueType` or `System.Enum` in the
core library's scope, so a `System.Enum` of the fixture's own assembly or of another assembly
makes no enum. The pair's items and the byte-order constant are tested with their own worlds,
in `Tests.ImportedFieldIndex` and `Tests.StaticFieldSites`.
-/

namespace Tests.PlatformDefinitions

open CIL CIL.Extraction Tests.MetadataBuilder Tests.MetadataWorld

/-- A local root can supply runtime storage only under the recognized neutral publisher. -/
theorem carried_core_scope_checks_publisher :
    isCorlibScope (bytesOf "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a") = true ∧
    isCorlibScope (bytesOf "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=null") = false ∧
    isCorlibScope (bytesOf "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=7cec85d7bea7798e") = false ∧
    isCorlibScope (bytesOf "System.Runtime, Version=11.0.0.0, Culture=fr, PublicKeyToken=b03f5f7f11d50a3a") = false := by
  decide +kernel
#print axioms carried_core_scope_checks_publisher

/-- Three carried class definitions. The root ends the chain and its direct child owns a field. -/
private def carriedClasses (scope rootName : String) (rootFlags : Nat) :
    Except MetadataError MetadataEnv := do
  let rows : Step Unit := do
    let space ← string "System"
    let root ← string rootName
    let parent ← string "Exception"
    let child ← string "SystemException"
    let fieldName ← string "_HResult"
    let fieldType ← blob [0x06, 0x08]
    let _ ← row Table.typeDef [rootFlags, root, space, 0, 1, 1]
    let _ ← row Table.typeDef [1, parent, space, 4, 1, 1]
    let _ ← row Table.typeDef [1, child, space, 8, 2, 1]
    let _ ← row Table.field [1, fieldName, fieldType]
  let slice := (build rows (bytesOf "System.Private.CoreLib") scope 11).1
  let index ← slice.indexWith (← slice.tables) (bytesOf scope)
  return MetadataEnv.ofSlices [index]

/-- Only the checked root ends the lineage. Its child's field counts towards the grandchild. -/
theorem carried_object_lineage :
    (do let env ← carriedClasses coreLibraryScope "Object" 1
        let lineage ← env.classChain resolveFuel 0 0x02000003
        let fields ← env.chainFieldCount lineage
        let frame ← env.frame 0 0
        return (lineage, fields, frame.corlib)) =
      .ok ([(0, 0x02000002)], 1, some (bytesOf coreLibraryScope)) := by rfl
#print axioms carried_object_lineage

/-- The defining CoreLib identity supplies Int32 storage even without a facade reference. -/
theorem carried_primitive_storage :
    typeStorageAt (fun _ => none) (.atom coreLibraryScope "System.Int32") = some (.field .signed32) ∧
    typeStorageAt (fun _ => none) (.atom ownIdentity "System.Int32") = none :=
  ⟨rfl, rfl⟩
#print axioms carried_primitive_storage

/-- A facade, another name or an interface cannot stand in for the defining root class. -/
theorem carried_object_rejects_other_definitions :
    let check := fun scope name flags => do
      let env ← carriedClasses scope name flags
      env.classChain resolveFuel 0 0x02000003
    check runtimeScope "Object" 1 = .error (.unsupportedBase 0x02000001) ∧
    check coreLibraryScope "Other" 1 = .error (.unsupportedBase 0x02000001) ∧
    check coreLibraryScope "Object" 0x21 = .error (.unsupportedBase 0x02000001) :=
  ⟨rfl, rfl, rfl⟩
#print axioms carried_object_rejects_other_definitions

/-! ## A type reference outside the carried slices -/

/-- `System.Console` of the world resolved under `platform`, read with `hint`. -/
private def console (platform : PlatformTable) (hint : Option Bool) :
    Except MetadataError NamedType := do
  let env := MetadataEnv.ofSlices [← own.1.index, ← lib.index] (platform := platform)
  typeRefNamed env 0 resolveFuel tokens.consoleRef hint

/-- Whether `result` is a type of this kind. -/
private def resolvedAs (result : Except MetadataError NamedType) (kind : Extraction.TypeKind) :
    Bool :=
  match result with
  | .ok named => named.kind == kind
  | .error _ => false

/-- Whether `result` failed with `error`. -/
private def failedWith {α : Type} (result : Except MetadataError α) (error : MetadataError) :
    Bool :=
  match result with
  | .error found => found == error
  | .ok _ => false

/-- `Console` is the class its definition states, read with no hint or as a class; without the
    definition it is refused, and a definition that states a value type refuses the class hint and
    makes the unhinted reference a value type. -/
theorem references_take_their_kind_from_the_definition :
    resolvedAs (console worldPlatform none) (.external (some false)) = true ∧
    resolvedAs (console worldPlatform (some false)) (.external (some false)) = true ∧
    failedWith (console worldPlatform (some true)) (.platformKindMismatch tokens.consoleRef) =
      true ∧
    failedWith (console (removing worldPlatform "Console") none)
      (.missingPlatformDefinition tokens.consoleRef) = true ∧
    failedWith (console (restating worldPlatform "Console" .valueType) (some false))
      (.platformKindMismatch tokens.consoleRef) = true ∧
    resolvedAs (console (restating worldPlatform "Console" .valueType) none)
      (.external (some true)) = true := by decide +kernel
#print axioms references_take_their_kind_from_the_definition

/-- Removing the declaring definition leaves the ordinary method reference and type unresolved. -/
theorem missing_owner_requires_link :
    (do
      let env := MetadataEnv.ofSlices [<- own.1.index, <- lib.index]
        (platform := removing worldPlatform "Console")
      let missing := MetadataError.missingPlatformDefinition tokens.consoleRef
      let type := SigType.named false tokens.consoleRef
      let head := ArgumentHead.platform runtimeScopeBytes [systemNamespace, bytesOf "Console"]
      return failedWith (env.methodSite tokens.writeLine) missing &&
        failedWith (env.resolve 0 type) missing &&
        failedWith (env.resolveToken 0 tokens.consoleRef) missing &&
        failedWith (head.resolve env tokens.writeLine 0)
            (.missingPlatformDefinition tokens.writeLine)).toOption = some true := by
  decide +kernel

#print axioms missing_owner_requires_link

/-- A pinned base cannot be classified through a platform entry, for any scope or table. -/
theorem pinned_base_requires_its_definition (env : MetadataEnv) (index : MetadataIndex)
    (token base : Nat) (scope : List Nat) (parts : List (List Nat)) (core : Bool)
    (pinned : env.pinned.matches scope = true) :
    env.externalBaseKind index token base scope parts core = .error (.missingSlice base) := by
  simp [MetadataEnv.externalBaseKind, pinned]
#print axioms pinned_base_requires_its_definition

/-- The metadata of a class with a closed generic base and an ordinary static method owner. -/
private def derivedOwner : Step Nat := do
  let runtime <- string "System.Runtime"
  let system <- string "System"
  let object <- string "Object"
  let key <- blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ <- row Table.assemblyRef [11, 0, 0, 0, 0, key, runtime, 0, 0]
  let _ <- row Table.typeRef [6, object, system]
  let baseName <- string "Base`1"
  let base <- row Table.typeDef [1, baseName, 0, 5, 1, 1]
  let parameter <- string "T"
  let _ <- row Table.genericParam [0, 0, 2, parameter]
  let signature <- blob [0x15, 0x12, 4, 1, 8]
  let _ <- row Table.typeSpec [signature]
  let derived <- string "Derived"
  let owner <- row Table.typeDef [1, derived, 0, 6, 1, 1]
  link linkGenericParams base 0 0x2A000001
  return owner

/-- A static owner can derive from the closed class Base<int>. -/
theorem closed_class_base_classifies :
    (do
      let (image, owner) := build derivedOwner (bytesOf "T") ownIdentity
      let env := MetadataEnv.ofSlices [<- image.index]
      return (<- typeDefNamed env 0 resolveFuel owner).kind).toOption = some .classType := by
  decide +kernel
#print axioms closed_class_base_classifies

/-- Each class derives from Pair of two copies of the previous class, with distinct TypeSpecs. -/
private def repeatedBases (depth : Nat) : Step Nat := do
  let runtime <- string "System.Runtime"
  let key <- blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ <- row Table.assemblyRef [11, 0, 0, 0, 0, key, runtime, 0, 0]
  let object <- row Table.typeRef [6, <- string "Object", <- string "System"]
  let base := tokenRow object * 4 + 1
  let _ <- row Table.typeDef [0, <- string "<Module>", 0, 0, 1, 1]
  let pair <- row Table.typeDef [1, <- string "Pair`2", 0, base, 1, 1]
  let first <- row Table.genericParam [0, 0, tokenRow pair * 2, <- string "A"]
  let _ <- row Table.genericParam [1, 0, tokenRow pair * 2, <- string "B"]
  link linkGenericParams pair 0 first
  let mut owner <- row Table.typeDef [1, <- string "D0", 0, base, 1, 1]
  for level in [:depth] do
    let argument := tokenRow owner * 4
    let signature <- blob [0x15, 0x12, tokenRow pair * 4, 2, 0x12, argument, 0x12, argument]
    let base <- row Table.typeSpec [signature]
    owner <- row Table.typeDef [1, <- string s!"D{level + 1}", 0, tokenRow base * 4 + 2, 1, 1]
  return owner

/-- The same number of owner resolutions at each depth, after metadata indexing. -/
private def measureOwners (depth : Nat) : IO (Prod Nat Nat) := do
  let (image, owner) := build (repeatedBases depth) (bytesOf "T") ownIdentity
  let .ok index := image.index | throw (IO.userError "invalid repeated base fixture")
  let env := MetadataEnv.ofSlices [index]
  let repetitions := 512
  let start <- IO.monoNanosNow
  let before <- IO.getNumHeartbeats
  for sample in [:repetitions] do
    unless resolvedAs (typeDefNamed env 0 (resolveFuel + sample % 2) owner) .classType do
      throw (IO.userError "constructed base owner did not resolve as a class")
  let work := (<- IO.getNumHeartbeats) - before
  return (((<- IO.monoNanosNow) - start) / repetitions, work / repetitions)

#eval do
  let mut atEight := 0
  for depth in [8, 10, 12, 14] do
    let (nanos, work) <- measureOwners depth
    IO.println s!"constructed base depth {depth}: {nanos} ns, {work} heartbeats per resolution"
    if depth == 8 then atEight := work
    if work == 0 || work * 8 > atEight * depth then
      throw (IO.userError "owner resolution grew faster than the depth of the metadata")

/-- A TypeSpec base gives a class owner without inspecting its signature or a platform entry. -/
theorem constructed_base_kind (env : MetadataEnv) (index : MetadataIndex) (pos owner : Nat)
    (row : TypeDefRow) (parts : List (List Nat)) (classFlag : row.flags &&& 0x20 = 0)
    (constructed : metadataTableOf row.extends_ = Table.typeSpec) :
    typeDefKind env index pos owner row parts = .ok .classType := by
  simp [typeDefKind, classFlag, constructed, Table.typeSpec, bind, Except.bind, pure, Except.pure]
#print axioms constructed_base_kind

/-- A constructed base supplies no instance layout for a receiver or an inherited field. -/
theorem constructed_base_has_no_layout (env : MetadataEnv) (index : MetadataIndex)
    (position owner fuel : Nat) (row : TypeDefRow)
    (found : env.slice position owner = .ok index) (entry : index.typeDef owner = .ok row)
    (constructed : metadataTableOf row.extends_ = Table.typeSpec) :
    env.classChain (fuel + 1) position owner = .error (.unsupportedBase owner) := by
  simp [MetadataEnv.classChain, found, entry, constructed, bind, Except.bind, Table.typeSpec]

#print axioms constructed_base_has_no_layout

/-- A platform head accepts exactly the parameter count carried by its resolved definition. -/
theorem platform_arity_matches (env : MetadataEnv) (named : NamedType) (position token count : Nat)
    (external : named.pinned = false) :
    (env.requireArity position token named count).isOk = (named.platformArity == count) := by
  cases equal : named.platformArity == count <;>
    simp [MetadataEnv.requireArity, external, equal] <;> rfl

#print axioms platform_arity_matches

/-- A closed argument from a definition requires the complete assembly identity among the pins. -/
theorem definition_requires_pin (env : MetadataEnv) (scope : List Nat) (method token count : Nat)
    (absent : env.exactPins.contains scope = false) :
    ArgumentHead.resolve env method count (.definition scope token) =
      .error (.missingSlice token) := by
  simp [ArgumentHead.resolve, absent]
  rfl

#print axioms definition_requires_pin

/-- Named types with fixed runtime storage cannot use an aggregate layout. -/
theorem fixed_storage_excludes_layout (frame : Frame) (named : NamedType) (layout : Nat)
    (identity : String) (fixed : named.fixedStorage = true) :
    frame.admits (.named named) (.aggregate identity layout) = false := by
  simp [Frame.admits, typeAdmits, fixed]

#print axioms fixed_storage_excludes_layout

/-- An opaque declaring name supplies no type expression for a local, field or type argument. -/
theorem imported_owner_has_no_storage (frame : Frame) (named : NamedType) (expr : TypeExpr)
    (opaqueKind : named.kind = .importedOwner) :
    frame.admits (.named named) expr = false := by
  cases expr <;>
    simp [Frame.admits, typeAdmits, opaqueKind, objectNamed, valueLike, NamedType.isEnum]

#print axioms imported_owner_has_no_storage

/-- The interface flag determines the kind even if the image states a base. -/
theorem interface_from_flags (env : MetadataEnv) (index : MetadataIndex) (pos owner : Nat)
    (row : TypeDefRow) (parts : List (List Nat)) (flag : row.flags &&& 0x20 != 0) :
    typeDefKind env index pos owner row parts = .ok .interfaceType := by
  simp [typeDefKind, flag]
  rfl

#print axioms interface_from_flags

/-- The identity of a constructed layout includes the defining scope of its named argument. -/
theorem aggregate_argument_keeps_scope (head argument : NamedType) (corlib : Option (List Nat)) :
    aggregateSpelling corlib 4 (.genericInst head (.cons (.named argument) .nil)) =
      some (head.scope ++ [58, 58] ++ head.name ++ [60] ++
        (argument.scope ++ [58, 58] ++ argument.name) ++ [62]) := rfl

#print axioms aggregate_argument_keeps_scope

/-! ## An external enum -/

/-- The scope bytes from the enum assembly row. -/
private def enumScope := bytesOf "E, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- The platform enum `Number` of `E` over `int`. -/
private def numberPlatform : PlatformTable := platform_table%
  [{ scope := enumScope, parts := [[], bytesOf "Number"], kind := .enumType 8 }]

/-- Whether the type `spelled` of `E` with the name parts of `Number`, resolved outside the
    carried slices, is admitted under `platform` as an enum over the runtime's type `name`. -/
private def admitsNumber (platform : PlatformTable) (name : String) (spelled := "Number") : Bool :=
  let frame : Frame :=
    { corlib := some runtimeScopeBytes, anchor := runtimeScopeBytes, arity := 0, ownerArity := 0 }
  let env := MetadataEnv.ofSlices [] (platform := platform)
  match env.externalNamed 0 enumScope (bytesOf spelled) [[], bytesOf "Number"] none with
  | .ok named => frame.admits (.named named) (.enum (Tests.enumIdentity spelled (Tests.enumAssembly name!"E")) (.atom runtimeScope name))
  | .error _ => false

/-- A platform enum cannot use aggregate storage at any layout index. -/
theorem enums_refuse_aggregate_storage (frame : Frame) (named : NamedType) (code index : Nat)
    (identity : String) (kind : named.kind = .enumType code) :
    frame.admits (.named named) (.aggregate identity index) = false := by
  simp [Frame.admits, typeAdmits, kind, valueLike]
#print axioms enums_refuse_aggregate_storage

/-- A missing entry for a closed platform argument preserves the diagnostic and method token. -/
theorem missing_closed_argument_definition (method : Nat) :
    (InstanceArgument.named (.platform (bytesOf "E") [[], bytesOf "Number"])).resolve
      (MetadataEnv.ofSlices []) method resolveFuel =
        .error (.missingPlatformDefinition method) := by
  rfl
#print axioms missing_closed_argument_definition

/-- The eight integer element types, by code from `0x04`, and the other scalar ones. -/
private def integerNames : List (Nat × String) :=
  [(0x04, "System.SByte"), (0x05, "System.Byte"), (0x06, "System.Int16"),
   (0x07, "System.UInt16"), (0x08, "System.Int32"), (0x09, "System.UInt32"),
   (0x0A, "System.Int64"), (0x0B, "System.UInt64")]
/-- Scalar names whose element codes cannot supply enum storage. -/
private def otherNames : List (Nat × String) :=
  [(0x02, "System.Boolean"), (0x03, "System.Char"), (0x0C, "System.Single"),
   (0x0D, "System.Double"), (0x18, "System.IntPtr"), (0x19, "System.UIntPtr")]

/-- An external enum admits the element type its definition states and no other: none without
    the definition, none when it states a value type, none when it states an enum over a type no
    enum may have, and none for a type whose parts name another type's definition. -/
theorem external_enums_take_their_underlying_type_from_the_definition :
    admitsNumber numberPlatform "System.Int32" = true ∧
    admitsNumber numberPlatform "System.Byte" = false ∧
    admitsNumber numberPlatform "System.Int32" (spelled := "Other") = false ∧
    admitsNumber (removing numberPlatform "Number") "System.Int32" = false ∧
    admitsNumber (restating numberPlatform "Number" .valueType) "System.Int32" = false ∧
    (integerNames.all fun (code, name) =>
      admitsNumber (restating numberPlatform "Number" (.enumType code)) name) = true ∧
    (otherNames.any fun (code, name) =>
      admitsNumber (restating numberPlatform "Number" (.enumType code)) name) = false := by
  decide +kernel
#print axioms external_enums_take_their_underlying_type_from_the_definition

/-! ## The end of a class chain -/

/-- Whether checking `operand` against `token` of the world gives `error` under `platform`, or
    passes when `error` is `none`. -/
private def checks (platform : PlatformTable) (token : Nat) (operand : RawOperand)
    (error : Option MetadataError) : Bool :=
  match (do
    let env := MetadataEnv.ofSlices [← own.1.index, ← lib.index] (platform := platform)
    checkEntry env 0 token operand) with
  | .ok _ => error.isNone
  | .error found => error == some found

/-- `count`, an instance field of the class `Program`, whose chain ends at `System.Object`. -/
private def countOperand : RawOperand :=
  .field (.object ownIdentity "Program") 0 int32 name!"count" false

/-- An instance field of a class is bound only when the chain ends at the definition of
    `System.Object`: without it the class's base is refused, and as a plain class the chain is. -/
theorem class_chains_end_at_the_object_definition :
    checks worldPlatform tokens.countField countOperand none = true ∧
    checks (removing worldPlatform "Object") tokens.countField countOperand
      (some (.missingPlatformDefinition tokens.objectRef)) = true ∧
    checks (restating worldPlatform "Object" .classType) tokens.countField countOperand
      (some (.platformKindMismatch tokens.objectRef)) = true := by decide +kernel
#print axioms class_chains_end_at_the_object_definition

/-! ## The kind a base gives -/

/-- `Lib`'s reference to `System.ValueType`, the base of `Lib.Pair`. -/
private def valueTypeRef : Nat := 0x01000002

/-- `Lib.Pair` is a value type only through the definition of `System.ValueType`: without it the
    base is refused, and a definition that states a plain class or the root of enums is refused
    for that name. -/
theorem value_types_come_from_the_value_type_definition :
    checks worldPlatform tokens.pairRef (.type (.atom libScope "Lib.Pair")) none = true ∧
    checks worldPlatform tokens.pairRef (.type (.object libScope "Lib.Pair"))
      (some (.operandMismatch tokens.pairRef)) = true ∧
    checks (removing worldPlatform "ValueType") tokens.pairRef (.type (.atom libScope "Lib.Pair"))
      (some (.missingPlatformDefinition valueTypeRef)) = true ∧
    checks (restating worldPlatform "ValueType" .classType) tokens.pairRef
      (.type (.atom libScope "Lib.Pair")) (some (.platformKindMismatch valueTypeRef)) = true ∧
    checks (restating worldPlatform "ValueType" .enumRoot) tokens.pairRef
      (.type (.atom libScope "Lib.Pair")) (some (.platformKindMismatch valueTypeRef)) = true := by
  decide +kernel
#print axioms value_types_come_from_the_value_type_definition

/-- Where the base `System.Enum` of `Program` is defined: in `T` itself, or in the assembly
    `Ext` outside the carried slices. -/
private inductive EnumHome where
  | own
  | ext

/-- `T` whose `Program`, with an `int` instance field `value__` and an instance method `Run`,
    extends a `System.Enum` of `home`. Returns the token of `Run`. -/
private def enumWorld (home : EnumHome) (rootName := "Enum") : Step Nat := do
  let runtime ← string "System.Runtime"
  let extName ← string "Ext"
  let system ← string "System"
  let objectName ← string "Object"
  let enumName <- string rootName
  let program ← string "Program"
  let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtime, 0, 0]
  let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, extName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let objectRef ← row Table.typeRef [1 * 4 + 2, objectName, system]
  let extEnum ← row Table.typeRef [2 * 4 + 2, enumName, system]
  let moduleName ← string "<Module>"
  let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
  let ownEnum ← row Table.typeDef [1, enumName, system, (objectRef - 0x01000000) * 4 + 1, 1, 1]
  let base := match home with
    | .own => (ownEnum - 0x02000000) * 4
    | .ext => (extEnum - 0x01000000) * 4 + 1
  let owner ← row Table.typeDef [1, program, 0, base, 1, 1]
  let valueName ← string "value__"
  let fieldSignature ← blob [0x06, 0x08]
  let field ← row Table.field [0x606, valueName, fieldSignature]
  link linkDeclaring field 0 owner
  let methodName ← string "Run"
  let signature ← blob [0x20, 0, 1]
  let method ← row Table.methodDef [0, 0, 0x86, methodName, signature, 1]
  link linkDeclaring method 0 owner
  pure method

/-- `Ext`'s `System.Enum` as the platform definition of this kind, beside `System.Object`. -/
private def extEnumPlatform (kind : PlatformKind) : PlatformTable :=
  restating (platform_table% [runtimeType "Object" .objectRoot,
    { scope := bytesOf "Ext, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null",
      parts := [bytesOf "System", bytesOf "Enum"], kind := .classType }]) "Enum" kind

/-- Checking `Run` with its receiver claimed an object of a class with the one field `value__`
    or a managed reference. -/
private def receiver (home : EnumHome) (platform : PlatformTable) (objectReceiver : Bool) :
    Except MetadataError MethodNames := do
  let fixture := build (enumWorld home) (bytesOf "T") ownIdentity
  let method : RawMethod :=
    { token := fixture.2, owner := ownIdentity ++ "::Program", hasThis := true,
      explicitThis := false, callingConvention := 0, attributes := 0x86, implementation := 0,
      returnType := .void, parameters := [], locals := [], initLocals := false, maxStack := 8,
      genericParameters := [], code := [],
      receiverClass := if objectReceiver then some (.object ownIdentity "Program") else none,
      objectFieldCount := if objectReceiver then 1 else 0 }
  let env := MetadataEnv.ofSlices [← fixture.1.index] (platform := platform)
  methodIdentityValid env method [] []

/-- The tokens of `Run` and `Program` in both worlds. -/
private def runToken : Nat := 0x06000001
private def programToken : Nat := 0x02000003

/-- A type that extends a `System.Enum` of its own assembly, or of an assembly other than the
    core library, is a class, never an enum whose receiver is a managed reference: the first is an
    object, and the second's chain ends at no core `System.Object`. -/
theorem only_the_core_library_enum_makes_an_enum :
    (receiver .own objectPlatform true).isOk = true ∧
    failedWith (receiver .own objectPlatform false) (.methodMismatch runToken) = true ∧
    failedWith (receiver .ext (extEnumPlatform .classType) true)
      (.unsupportedBase programToken) = true ∧
    failedWith (receiver .ext (extEnumPlatform .classType) false) (.methodMismatch runToken) =
      true ∧
    failedWith (receiver .ext (extEnumPlatform .enumRoot) false)
      (.methodMismatch runToken) = true := by decide +kernel
#print axioms only_the_core_library_enum_makes_an_enum

/-- The core root definitions, a struct and an enum in the same assembly. -/
private def coreDefinitions : Step Unit := do
  let system <- string "System"
  let _ <- row Table.typeDef [0, <- string "<Module>", 0, 0, 1, 1]
  let object <- row Table.typeDef [1, <- string "Object", system, 0, 1, 1]
  let value <- row Table.typeDef [1, <- string "ValueType", system, tokenRow object * 4, 1, 1]
  let root <- row Table.typeDef [1, <- string "Enum", system, tokenRow value * 4, 1, 1]
  let _ <- row Table.typeDef [1, <- string "Struct", 0, tokenRow value * 4, 1, 1]
  let flag <- row Table.typeDef [1, <- string "Flag", 0, tokenRow root * 4, 1, 1]
  let field <- row Table.field [0x606, <- string "value__", <- blob [0x06, 0x08]]
  link linkDeclaring field 0 flag

/-- Resolve the same declarations with and without the ECMA publisher key in the Assembly row. -/
private def carriedKinds (keyed : Bool) : Except MetadataError (List Extraction.TypeKind) := do
  let token := if keyed then "b77a5c561934e089" else "null"
  let identity := "mscorlib, Version=1.0.0.0, Culture=neutral, PublicKeyToken=" ++ token
  let (image, _) := build coreDefinitions (bytesOf "mscorlib") identity
  let assembly := image.assembly
  let ecmaKey := List.replicate 8 0 ++ [4] ++ List.replicate 7 0
  let assembly := if keyed then
    { assembly with
      assemblyRow := (assembly.assemblyRow.set 12 1).set 16 1
      keyToken := bytesOf token
      blobs := [(0, [0]), (1, 16 :: ecmaKey)] }
    else assembly
  let env := MetadataEnv.ofSlices [← ({ image with assembly } : MetadataSlice).index]
  let kind := fun token => (typeDefNamed env 0 resolveFuel token).map NamedType.kind
  return [← kind 0x02000001, ← kind 0x02000002, ← kind 0x02000004,
    ← kind 0x02000005, ← kind 0x02000006]

/-- Only the published core identity supplies the value and enum roots in its own image. -/
theorem carried_core_roots :
    (carriedKinds true).toOption =
        some [.classType, .classType, .classType, .valueType, .enumType 8] ∧
    (carriedKinds false).toOption =
        some [.classType, .classType, .classType, .classType, .classType] := by decide +kernel
#print axioms carried_core_roots

/-- An external System.ValueType in another scope supplies an ordinary class base. -/
theorem foreign_value_type_is_a_class_base :
    (do
      let (image, _) := build (enumWorld .ext "ValueType") (bytesOf "T") ownIdentity
      let env := MetadataEnv.ofSlices [<- image.index]
      return (<- typeDefNamed env 0 resolveFuel programToken).kind).toOption =
        some .classType := by
  decide +kernel
#print axioms foreign_value_type_is_a_class_base

end Tests.PlatformDefinitions
