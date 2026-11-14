import CIL.Extraction.Signatures
import CIL.Extraction.Generics

/-!
# Resolving metadata names and types

A signature type names its classes and value types by token of the slice the blob comes from.
This file gives a token a scoped name and a kind, following `TypeRef` scopes and nested types,
and finds the `TypeDef` of a type the carried slices define. `ResolvedType` is independent of
the slice a type was read in, so a call site's generic arguments can be substituted into a
callee's signature from another slice. `typeAdmits` states when an extractor's `TypeExpr`
names a resolved type; it is a relation because the extractor picks the `TypeExpr`
constructor (`atom`, `object`, `aggregate`, `enum`) by what it admits, while the scope, the name
and the kind facts come from the bytes.

Definitions in platform assemblies are not carried: a type defined outside the carried slices
is `external`, with a kind known only from the signature that names it.
-/

namespace CIL.Extraction

/-- What a resolved type is. A type outside the carried slices has the value-or-class byte of
    the signature that named it, if any. -/
inductive TypeKind where
  | valueType
  | enumType (underlying : Nat)
  | classType
  | interfaceType
  | external (valueType : Option Bool)
  deriving DecidableEq, Repr

/-- A type by the identity of the assembly that defines it and its Cecil full name
    (`Namespace.Name`, nested types as `Outer/Inner`), as bytes. `pinned` is set for a type
    found in a carried slice. -/
structure NamedType where
  scope : List Nat
  name : List Nat
  /-- The namespace column and the simple name of each enclosing type and of the type itself,
      kept apart: `name` joins them with dots and slashes and leaves out a nested type's
      namespace, so types it spells alike stay different. -/
  parts : List (List Nat)
  kind : TypeKind
  pinned : Bool
  deriving DecidableEq, Repr

mutual

/-- A signature type with every token resolved. -/
inductive ResolvedType where
  | primitive (code : Nat)
  | named (type : NamedType)
  | var (index : Nat)
  | mvar (index : Nat)
  | byref (element : ResolvedType)
  | pointer (element : ResolvedType)
  | szarray (element : ResolvedType)
  | genericInst (head : NamedType) (arguments : ResolvedList)
  | functionPointer (convention : Nat) (result : ResolvedType) (parameters : ResolvedList)
  | modified (required : Bool) (modifier : NamedType) (element : ResolvedType)
  deriving DecidableEq, Repr

/-- A list of resolved types, as a chain so that the types derive decidable equality. -/
inductive ResolvedList where
  | nil
  | cons (head : ResolvedType) (tail : ResolvedList)
  deriving DecidableEq, Repr

end

/-- The types of a chain, in order. -/
def ResolvedList.toList : ResolvedList → List ResolvedType
  | .nil => []
  | .cons head tail => head :: tail.toList

/-- The chain of a list of types. -/
def ResolvedList.ofList : List ResolvedType → ResolvedList
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

/-- The pinned assemblies' slices of one method, its own first, and the name stem of every
    assembly the extraction pins: a reference to an assembly of a pinned name whose slice is not
    carried is refused, whatever its version, not treated as a platform reference. -/
structure MetadataEnv where
  slices : List MetadataIndex
  /-- `assemblyStem` of each pinned identity. -/
  pinned : List (List Nat) := []

/-- The slice at a position, or `unresolvedType` for a token that points outside the list. -/
def MetadataEnv.slice (env : MetadataEnv) (position token : Nat) :
    Except MetadataError MetadataIndex :=
  match env.slices[position]? with
  | some index => .ok index
  | none => .error (.unresolvedType token)

/-- The slice, link-resolved: the link of a kind from a token, if the slice states one. -/
def MetadataIndex.link (index : MetadataIndex) (kind source : Nat) : Option (Nat × Nat) :=
  index.links.find? (kind * 0x100000000 + source)

/-- How deeply names, enclosing types and signature types may nest. -/
def resolveFuel : Nat := 32

/-- The simple name of an assembly identity followed by `versionMarker`: every identity of an
    assembly of that name, at any version, culture or key, starts with it. -/
def assemblyStem : List Nat → List Nat
  | [] => []
  | byte :: rest =>
    if versionMarker.isPrefixOf (byte :: rest) then versionMarker else byte :: assemblyStem rest

/-- `Namespace.Name`, or the bare name for the global namespace. -/
def qualifiedName (namespace_ name : List Nat) : List Nat :=
  if namespace_.isEmpty then name else namespace_ ++ 46 :: name

/-- The name of a type nested in an enclosing one. -/
def nestedName (enclosing name : List Nat) : List Nat := enclosing ++ 47 :: name

/-- The assemblies that define the primitive types. -/
def corlibNames : List (List Nat) :=
  -- `System.Runtime`, `netstandard`, `mscorlib` and `System.Private.CoreLib` as bytes, so the
  -- kernel never evaluates their string literals.
  [[83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101],
   [110, 101, 116, 115, 116, 97, 110, 100, 97, 114, 100],
   [109, 115, 99, 111, 114, 108, 105, 98],
   [83, 121, 115, 116, 101, 109, 46, 80, 114, 105, 118, 97, 116, 101, 46, 67, 111, 114, 101, 76,
    105, 98]]

/-- Whether an assembly identity names an assembly of one of the core-library names, at any
    version. -/
def isCorlibScope (scope : List Nat) : Bool :=
  corlibNames.any fun name => (name ++ versionMarker).isPrefixOf scope

/-- Whether the `TypeRef` at `token` is scoped by a reference to an assembly of a core-library
    name: the base of a type counts as `System.Enum`, `System.ValueType` or `System.Object` only
    then. -/
def MetadataIndex.coreLibraryReference (index : MetadataIndex) (token : Nat) :
    Except MetadataError Bool := do
  let row ← index.typeRef token
  if metadataTableOf row.scope != Table.assemblyRef then return false
  .ok (corlibNames.contains (← index.string (← index.assemblyRef row.scope).name))

/-- The identity of the assembly the slice's primitive types come from, or `none` when the
    slice names none. -/
def MetadataIndex.corlibIdentity (index : MetadataIndex) :
    Except MetadataError (Option (List Nat)) :=
  if index.corlib == 0 then .ok none
  else do
    let token := tokenOf Table.assemblyRef index.corlib
    let row ← index.assemblyRef token
    if !corlibNames.contains (← index.string row.name) then throw (.unsupportedAssemblyRef token)
    .ok (some (← index.assemblyRefIdentity token))

/-- The scope, full name and name parts a `TypeRef` spells: its assembly, or the outermost
    enclosing type's. -/
def typeRefQualified (env : MetadataEnv) (position : Nat) :
    Nat → Nat → Except MetadataError (List Nat × List Nat × List (List Nat))
  | 0, token => .error (.unresolvedType token)
  | fuel + 1, token => do
    let index ← env.slice position token
    let row ← index.typeRef token
    let namespace_ ← index.string row.namespace_
    let simple ← index.string row.name
    let name := qualifiedName namespace_ simple
    match metadataTableOf row.scope with
    | 0x23 => .ok (← index.assemblyRefIdentity row.scope, name, [namespace_, simple])
    | 0x00 => .ok (index.identity, name, [namespace_, simple])
    | 0x01 =>
      let (scope, enclosing, parts) ← typeRefQualified env position fuel row.scope
      .ok (scope, nestedName enclosing simple, parts ++ [namespace_, simple])
    | _ => .error (.unsupportedScope token)

/-- The first instance field among `count` consecutive `Field` rows from `row`: a scan that
    stops at the first instance field, which an enum declares before its constants. -/
def firstInstanceField (index : MetadataIndex) : Nat → Nat → Except MetadataError (Option Nat)
  | 0, _ => .ok none
  | count + 1, row => do
    let token := tokenOf Table.field row
    let field ← index.field token
    if field.flags / 0x10 % 2 == 1 then firstInstanceField index count (row + 1)
    else .ok (some token)
/-- The first `Field` row after a type's own: the next `TypeDef`'s, or one past the table. -/
def MetadataIndex.fieldEnd (index : MetadataIndex) (token : Nat) (row : TypeDefRow) :
    Except MetadataError Nat :=
  if tokenRow token == index.header.rows Table.typeDef then
    .ok (index.header.rows Table.field + 1)
  else do
    let next ← index.typeDef (token + 1)
    if next.fieldList < row.fieldList then throw (.unresolvedType token)
    .ok next.fieldList

/-- The fields of a type, in table order. -/
def MetadataIndex.fieldRange (index : MetadataIndex) (token : Nat) :
    Except MetadataError (Nat × Nat) := do
  let row ← index.typeDef token
  .ok (row.fieldList, ← index.fieldEnd token row)

/-- The integer element type of the single instance field of an enum. -/
def enumUnderlying (index : MetadataIndex) (token : Nat) : Except MetadataError Nat := do
  let (start, stop) ← index.fieldRange token
  if index.instanceTotal.find? token != some 1 then throw (.unresolvedType token)
  match ← firstInstanceField index (stop - start) start with
  | some field =>
    let row ← index.field field
    match ← decodeFieldSig (← index.blob row.signature) with
    | .primitive code =>
      if 0x04 ≤ code && code ≤ 0x0B then .ok code else .error (.unresolvedType token)
    | _ => .error (.unresolvedType token)
  | none => .error (.unresolvedType token)
/-- The namespace `System` as bytes. -/
def systemNamespace : List Nat := [83, 121, 115, 116, 101, 109]

/-- `Enum`, the simple name of `System.Enum`, as bytes. -/
def enumName : List Nat := [69, 110, 117, 109]

/-- `ValueType`, the simple name of `System.ValueType`, as bytes. -/
def valueTypeName : List Nat := [86, 97, 108, 117, 101, 84, 121, 112, 101]

/-- `Object`, the simple name of `System.Object`, as bytes. -/
def objectName : List Nat := [79, 98, 106, 101, 99, 116]

/-- The core-library base names spell the texts they stand for; a wrong byte would turn every
    struct into a class. -/
theorem base_names_spell :
    spelled? systemNamespace = some "System" ∧ spelled? enumName = some "Enum" ∧
      spelled? valueTypeName = some "ValueType" ∧ spelled? objectName = some "Object" :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms base_names_spell

/-- An interface has the interface flag; a type that extends `System.Enum` is an enum with the
    underlying type of its instance field, one that extends `System.ValueType` is a value
    type, and any other type is a class. The base counts only when its own reference names a
    core-library assembly, so the slice's `corlib` number plays no part. -/
def typeDefKind (env : MetadataEnv) (position token : Nat) (row : TypeDefRow) :
    Except MetadataError TypeKind := do
  if row.flags / 0x20 % 2 == 1 then return .interfaceType
  if metadataTableOf row.extends_ != Table.typeRef then return .classType
  let index ← env.slice position token
  let (_, _, parts) ← typeRefQualified env position resolveFuel row.extends_
  if !(← index.coreLibraryReference row.extends_) then return .classType
  if parts == [systemNamespace, enumName] then return .enumType (← enumUnderlying index token)
  if parts == [systemNamespace, valueTypeName] then return .valueType
  .ok .classType

/-- The named type of a `TypeDef` in the slice at `position`: its scope is that slice's
    assembly, its name follows the `NestedClass` row for a nested type and its kind follows
    its flags and base. -/
def typeDefNamed (env : MetadataEnv) (position : Nat) : Nat → Nat → Except MetadataError NamedType
  | 0, token => .error (.unresolvedType token)
  | fuel + 1, token => do
    let index ← env.slice position token
    let row ← index.typeDef token
    let simple ← index.string row.name
    let namespace_ ← index.string row.namespace_
    let (name, parts) ←
      if row.flags % 8 < 2 then pure (qualifiedName namespace_ simple, [namespace_, simple])
      else do
        let some (linked, nesting) := index.link linkNesting token
          | throw (.unresolvedType token)
        if linked != position then throw (.unresolvedType token)
        let nested ← index.nestedClass nesting
        if nested.nested != token then throw (.unresolvedType token)
        let enclosing ← typeDefNamed env position fuel nested.enclosing
        pure (nestedName enclosing.name simple, enclosing.parts ++ [namespace_, simple])
    let kind ← typeDefKind env position token row
    .ok { scope := index.identity, name := name, parts := parts, kind := kind, pinned := true }

/-- The named type of a `TypeRef`. A scope that names a carried slice is resolved through the
    slice's definition link to the `TypeDef` that defines it, whose name must be the one the
    reference spells; a scope of a pinned name is refused; any other type is `external` with the
    given value-or-class hint. -/
def typeRefNamed (env : MetadataEnv) (position : Nat) :
    Nat → Nat → Option Bool → Except MetadataError NamedType
  | 0, token, _ => .error (.unresolvedType token)
  | fuel + 1, token, hint => do
    let (scope, name, parts) ← typeRefQualified env position resolveFuel token
    match env.slices.findIdx? (fun candidate => candidate.identity == scope) with
    | none =>
      if env.pinned.any (·.isPrefixOf scope) then throw (.missingSlice token)
      .ok { scope := scope, name := name, parts := parts, kind := .external hint, pinned := false }
    | some target =>
      let index ← env.slice position token
      let some (linked, definition) := index.link linkDefinition token
        | throw (.unresolvedType token)
      if linked != target then throw (.unresolvedType token)
      let named ← typeDefNamed env linked fuel definition
      if named.scope != scope || named.parts != parts then throw (.operandMismatch token)
      .ok named

/-- The named type of a custom modifier. A modifier is read by its scope and name alone, so it
    needs no link to a definition, whether or not its scope is a carried slice or the type
    resolves. -/
def modifierNamed (env : MetadataEnv) (position token : Nat) : Except MetadataError NamedType := do
  match metadataTableOf token with
  | 0x01 =>
    let (scope, name, parts) ← typeRefQualified env position resolveFuel token
    .ok { scope := scope, name := name, parts := parts, kind := .external none, pinned := false }
  | 0x02 =>
    let index ← env.slice position token
    let row ← index.typeDef token
    let namespace_ ← index.string row.namespace_
    let simple ← index.string row.name
    .ok { scope := index.identity, name := qualifiedName namespace_ simple,
          parts := [namespace_, simple], kind := .external none, pinned := false }
  | _ => .error (.unsupportedTable token)

/-- Whether a signature's class-or-value-type byte agrees with a type found in a carried
    slice. -/
def hintAgrees : TypeKind → Option Bool → Bool
  | .valueType, some valueType | .enumType _, some valueType => valueType
  | .classType, some valueType | .interfaceType, some valueType => !valueType
  | _, _ => true

/-- The named type of a `TypeDef` or `TypeRef` token read with a value-or-class byte. -/
def namedOf (env : MetadataEnv) (position token : Nat) (hint : Option Bool) :
    Except MetadataError NamedType := do
  let named ← match metadataTableOf token with
    | 0x02 => typeDefNamed env position resolveFuel token
    | 0x01 => typeRefNamed env position resolveFuel token hint
    | _ => .error (.unsupportedTable token)
  if hintAgrees named.kind hint then .ok named else .error (.operandMismatch token)

mutual

/-- Resolve every token of a signature type read in the slice at `position`. -/
def resolveType (env : MetadataEnv) (position : Nat) :
    Nat → SigType → Except MetadataError ResolvedType
  | 0, _ => .error (.unresolvedType 0)
  | _ + 1, .primitive code => .ok (.primitive code)
  | _ + 1, .named valueType token => do
    .ok (.named (← namedOf env position token (some valueType)))
  | _ + 1, .var index => .ok (.var index)
  | _ + 1, .mvar index => .ok (.mvar index)
  | fuel + 1, .byref element => do .ok (.byref (← resolveType env position fuel element))
  | fuel + 1, .pointer element => do .ok (.pointer (← resolveType env position fuel element))
  | fuel + 1, .szarray element => do .ok (.szarray (← resolveType env position fuel element))
  | fuel + 1, .genericInst valueType token arguments => do
    let head ← namedOf env position token (some valueType)
    .ok (.genericInst head (← resolveList env position fuel arguments))
  | fuel + 1, .functionPointer convention result parameters => do
    let resolved ← resolveType env position fuel result
    .ok (.functionPointer convention resolved (← resolveList env position fuel parameters))
  | fuel + 1, .modified required modifier element => do
    let named ← modifierNamed env position modifier
    .ok (.modified required named (← resolveType env position fuel element))

/-- Resolve a chain of signature types. -/
def resolveList (env : MetadataEnv) (position : Nat) :
    Nat → SigList → Except MetadataError ResolvedList
  | 0, _ => .error (.unresolvedType 0)
  | _ + 1, .nil => .ok .nil
  | fuel + 1, .cons head tail => do
    .ok (.cons (← resolveType env position fuel head) (← resolveList env position fuel tail))

end

/-- Resolve a signature type read in the slice at `position`. -/
def MetadataEnv.resolve (env : MetadataEnv) (position : Nat) (type : SigType) :
    Except MetadataError ResolvedType :=
  resolveType env position (resolveFuel + 2) type

/-- The type a `TypeDef`, `TypeRef` or `TypeSpec` token names. -/
def MetadataEnv.resolveToken (env : MetadataEnv) (position token : Nat) :
    Except MetadataError ResolvedType :=
  match metadataTableOf token with
  | 0x02 | 0x01 => do .ok (.named (← namedOf env position token none))
  | 0x1B => do
    let index ← env.slice position token
    let blob ← index.blob (← index.signatureOf Table.typeSpec token)
    env.resolve position (← decodeTypeSpec blob)
  | _ => .error (.unsupportedTable token)

/-! ## Spelling -/

/-- `System.`, the namespace of every primitive type with its separator, as bytes. -/
def systemPrefix : List Nat := systemNamespace ++ [46]

/-- `System.String` as bytes. -/
def systemStringName : List Nat := systemPrefix ++ [83, 116, 114, 105, 110, 103]

/-- `System.Object` as bytes. -/
def systemObjectName : List Nat := systemPrefix ++ objectName

/-- `ValueTuple\``, the stem of every value tuple's simple name, as bytes. -/
def valueTupleSimpleStem : List Nat := [86, 97, 108, 117, 101, 84, 117, 112, 108, 101, 96]

/-- `System.ValueTuple\``, the stem of every value tuple's name, as bytes. -/
def valueTupleStem : List Nat := systemPrefix ++ valueTupleSimpleStem

/-- `ValueTuple\`2`, the simple name of the pair, as bytes. -/
def valueTuplePairName : List Nat := valueTupleSimpleStem ++ [50]

/-- `Item1`, the pair's first field, as bytes. -/
def firstItemName : List Nat := [73, 116, 101, 109, 49]

/-- `Item2`, the pair's second field, as bytes. -/
def secondItemName : List Nat := [73, 116, 101, 109, 50]

/-- The value tuple names spell the texts they stand for. -/
theorem value_tuple_names_spell :
    spelled? valueTupleStem = some "System.ValueTuple`" ∧
      spelled? valueTuplePairName = some "ValueTuple`2" ∧
      spelled? firstItemName = some "Item1" ∧ spelled? secondItemName = some "Item2" :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms value_tuple_names_spell

/-- The `System` type name of an element type byte, as bytes, so that no decision evaluates a
    string; `primitiveName_spells` gives the text of each. -/
def primitiveName : Nat → Option (List Nat)
  | 0x01 => some (systemPrefix ++ [86, 111, 105, 100])
  | 0x02 => some (systemPrefix ++ [66, 111, 111, 108, 101, 97, 110])
  | 0x03 => some (systemPrefix ++ [67, 104, 97, 114])
  | 0x04 => some (systemPrefix ++ [83, 66, 121, 116, 101])
  | 0x05 => some (systemPrefix ++ [66, 121, 116, 101])
  | 0x06 => some (systemPrefix ++ [73, 110, 116, 49, 54])
  | 0x07 => some (systemPrefix ++ [85, 73, 110, 116, 49, 54])
  | 0x08 => some (systemPrefix ++ [73, 110, 116, 51, 50])
  | 0x09 => some (systemPrefix ++ [85, 73, 110, 116, 51, 50])
  | 0x0A => some (systemPrefix ++ [73, 110, 116, 54, 52])
  | 0x0B => some (systemPrefix ++ [85, 73, 110, 116, 54, 52])
  | 0x0C => some (systemPrefix ++ [83, 105, 110, 103, 108, 101])
  | 0x0D => some (systemPrefix ++ [68, 111, 117, 98, 108, 101])
  | 0x0E => some systemStringName
  | 0x18 => some (systemPrefix ++ [73, 110, 116, 80, 116, 114])
  | 0x19 => some (systemPrefix ++ [85, 73, 110, 116, 80, 116, 114])
  | 0x1C => some systemObjectName
  | _ => none

/-- Each element type byte with a name spells the `System` type it stands for. -/
theorem primitiveName_spells :
    [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x18,
        0x19, 0x1C].map (fun code => (primitiveName code).bind spelled?) =
      ["System.Void", "System.Boolean", "System.Char", "System.SByte", "System.Byte",
        "System.Int16", "System.UInt16", "System.Int32", "System.UInt32", "System.Int64",
        "System.UInt64", "System.Single", "System.Double", "System.String", "System.IntPtr",
        "System.UIntPtr", "System.Object"].map some := by
  cil_kernel_rfl
#print axioms primitiveName_spells

mutual

/-- Cecil's `FullName` of a type: nested types as `Outer/Inner`, instances as `Head<A,B>`,
    references as `T&`, pointers as `T*`, vectors as `T[]`, parameters as `!n` and `!!n` and
    modifiers as `T modreq(M)`. With `pointers`, a function pointer is `method R *(P,Q)`; its
    calling convention is not spelled, so an identity compared across methods leaves it out. -/
def cecilName (pointers : Bool) : Nat → ResolvedType → Option (List Nat)
  | 0, _ => none
  | _ + 1, .primitive code => primitiveName code
  | _ + 1, .named named => some named.name
  -- `!` and `!!`
  | _ + 1, .var index => some (33 :: decimalDigits 10 index)
  | _ + 1, .mvar index => some (33 :: 33 :: decimalDigits 10 index)
  | fuel + 1, .byref element => (· ++ [38]) <$> cecilName pointers fuel element
  | fuel + 1, .pointer element => (· ++ [42]) <$> cecilName pointers fuel element
  | fuel + 1, .szarray element => (· ++ [91, 93]) <$> cecilName pointers fuel element
  | fuel + 1, .genericInst head arguments => do
    let inner ← cecilNames pointers fuel arguments
    some (head.name ++ [60] ++ inner ++ [62])
  | fuel + 1, .modified required modifier element => do
    let spelled ← cecilName pointers fuel element
    -- ` modreq(` and ` modopt(`
    let marker := if required then [32, 109, 111, 100, 114, 101, 113, 40]
      else [32, 109, 111, 100, 111, 112, 116, 40]
    some (spelled ++ marker ++ modifier.name ++ [41])
  | fuel + 1, .functionPointer _ result parameters =>
    if pointers then do
      let returned ← cecilName pointers fuel result
      let spelled ← cecilNames pointers fuel parameters
      -- `method ` and ` *(`
      some ([109, 101, 116, 104, 111, 100, 32] ++ returned ++ [32, 42, 40] ++ spelled ++ [41])
    else none

/-- The names of a chain of types, separated by commas. -/
def cecilNames (pointers : Bool) : Nat → ResolvedList → Option (List Nat)
  | 0, _ => none
  | _ + 1, .nil => some []
  | fuel + 1, .cons head .nil => cecilName pointers fuel head
  | fuel + 1, .cons head tail => do
    let first ← cecilName pointers fuel head
    let rest ← cecilNames pointers fuel tail
    some (first ++ [44] ++ rest)

end

mutual

/-- The identity of an aggregate type of a carried assembly: `scope::Name`, and for an instance
    `scope::Head<argument identities>`, with a primitive's scope the primitive assembly's. -/
def aggregateSpelling (corlib : List Nat) : Nat → ResolvedType → Option (List Nat)
  | 0, _ => none
  | _ + 1, .primitive code => do
    let name ← primitiveName code
    some (corlib ++ [58, 58] ++ name)
  | _ + 1, .named named => some (named.scope ++ [58, 58] ++ named.name)
  | fuel + 1, .genericInst head arguments => do
    if head.pinned then
      let inner ← aggregateSpellings corlib fuel arguments
      some (head.scope ++ [58, 58] ++ head.name ++ [60] ++ inner ++ [62])
    else
      -- A value tuple is an aggregate and keeps Cecil's spelling; any other instance outside
      -- the carried slices, such as a vector, spells its arguments with their scopes.
      let inner ← if valueTupleStem.isPrefixOf head.name
        then cecilNames false fuel arguments else aggregateSpellings corlib fuel arguments
      some (head.scope ++ [58, 58] ++ head.name ++ [60] ++ inner ++ [62])
  | _ + 1, _ => none

/-- The identities of a chain of types, separated by commas. -/
def aggregateSpellings (corlib : List Nat) : Nat → ResolvedList → Option (List Nat)
  | 0, _ => none
  | _ + 1, .nil => some []
  | fuel + 1, .cons head .nil => aggregateSpelling corlib fuel head
  | fuel + 1, .cons head tail => do
    let first ← aggregateSpelling corlib fuel head
    let rest ← aggregateSpellings corlib fuel tail
    some (first ++ [44] ++ rest)

end

/-! ## Substitution and the modifiers a call site drops -/

mutual

/-- Substitute call-site generic arguments for the parameters of a signature, as Cecil does:
    a parameter with no arguments stays, an argument list too short for a parameter fails, and
    modifiers and function pointers are left as written. -/
def substituteResolved (methodArguments ownerArguments : Option (List ResolvedType)) :
    Nat → ResolvedType → Option ResolvedType
  | 0, _ => none
  | _ + 1, .var index =>
    match ownerArguments with
    | none => some (.var index)
    | some arguments => arguments[index]?
  | _ + 1, .mvar index =>
    match methodArguments with
    | none => some (.mvar index)
    | some arguments => arguments[index]?
  | fuel + 1, .byref element =>
    .byref <$> substituteResolved methodArguments ownerArguments fuel element
  | fuel + 1, .pointer element =>
    .pointer <$> substituteResolved methodArguments ownerArguments fuel element
  | fuel + 1, .szarray element =>
    .szarray <$> substituteResolved methodArguments ownerArguments fuel element
  | fuel + 1, .genericInst head arguments =>
    .genericInst head <$> substituteResolvedList methodArguments ownerArguments fuel arguments
  | _ + 1, type => some type

/-- Substitute through a chain of types. -/
def substituteResolvedList (methodArguments ownerArguments : Option (List ResolvedType)) :
    Nat → ResolvedList → Option ResolvedList
  | 0, _ => none
  | _ + 1, .nil => some .nil
  | fuel + 1, .cons head tail => do
    some (.cons (← substituteResolved methodArguments ownerArguments fuel head)
      (← substituteResolvedList methodArguments ownerArguments fuel tail))

end

mutual

/-- Whether a type has a custom modifier anywhere inside it. -/
def hasModifier : Nat → ResolvedType → Bool
  | 0, _ => true
  | _ + 1, .modified .. => true
  | fuel + 1, .byref element => hasModifier fuel element
  | fuel + 1, .pointer element => hasModifier fuel element
  | fuel + 1, .szarray element => hasModifier fuel element
  | fuel + 1, .genericInst _ arguments => listHasModifier fuel arguments
  | fuel + 1, .functionPointer _ result parameters =>
    hasModifier fuel result || listHasModifier fuel parameters
  | _ + 1, _ => false

/-- Whether a chain of types has a custom modifier anywhere inside it. -/
def listHasModifier : Nat → ResolvedList → Bool
  | 0, _ => true
  | _ + 1, .nil => false
  | fuel + 1, .cons head tail => hasModifier fuel head || listHasModifier fuel tail
end

/-- The namespace `System.Runtime.InteropServices` as bytes. -/
def interopServicesNamespace : List Nat :=
  systemPrefix ++ [82, 117, 110, 116, 105, 109, 101, 46, 73, 110, 116, 101, 114, 111, 112, 83,
    101, 114, 118, 105, 99, 101, 115]

/-- `InAttribute`, the simple name of the modifier of `in` parameters, as bytes. -/
def inAttributeName : List Nat := [73, 110, 65, 116, 116, 114, 105, 98, 117, 116, 101]

/-- The namespace `System.Runtime.CompilerServices` as bytes. -/
def compilerServicesNamespace : List Nat :=
  systemPrefix ++ [82, 117, 110, 116, 105, 109, 101, 46, 67, 111, 109, 112, 105, 108, 101, 114,
    83, 101, 114, 118, 105, 99, 101, 115]

/-- `IsExternalInit`, the simple name of the modifier of `init` accessors, as bytes. -/
def externalInitName : List Nat :=
  [73, 115, 69, 120, 116, 101, 114, 110, 97, 108, 73, 110, 105, 116]

/-- `runtimeScope` as bytes. -/
def runtimeScopeBytes : List Nat :=
  [83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 44, 32,
    86, 101, 114, 115, 105, 111, 110, 61, 49, 49, 46, 48, 46, 48, 46, 48,
    44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97,
    108, 44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101,
    110, 61, 98, 48, 51, 102, 53, 102, 55, 102, 49, 49, 100, 53, 48, 97,
    51, 97]

/-- The modifier names and the runtime scope spell the texts they stand for. -/
theorem modifier_names_spell :
    spelled? interopServicesNamespace = some "System.Runtime.InteropServices" ∧
      spelled? inAttributeName = some "InAttribute" ∧
      spelled? compilerServicesNamespace = some "System.Runtime.CompilerServices" ∧
      spelled? externalInitName = some "IsExternalInit" ∧
      spelled? runtimeScopeBytes = some runtimeScope :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms modifier_names_spell

/-- `System.Runtime`'s `System.Runtime.InteropServices.InAttribute`, by namespace and simple
    name, the modifier Roslyn writes on `in` parameters. -/
def isInModifier (modifier : NamedType) : Bool :=
  modifier.parts == [interopServicesNamespace, inAttributeName] &&
    modifier.scope == runtimeScopeBytes

/-- `System.Runtime.CompilerServices.IsExternalInit` from any assembly, by namespace and simple
    name, the marker Roslyn writes on `init` accessors. -/
def isInitModifier (modifier : NamedType) : Bool :=
  modifier.parts == [compilerServicesNamespace, externalInitName]

/-- The reference an `in` parameter's `modreq(InAttribute)` wraps: modified directly, once. -/
def inReference : ResolvedType → Option ResolvedType
  | .modified true modifier (.byref element) =>
    if isInModifier modifier && !hasModifier resolveFuel element then some element else none
  | _ => none

/-- The type of a parameter at run time: an `in` reference loses its modifier. -/
def declaredParameter (type : ResolvedType) : ResolvedType :=
  match inReference type with
  | some element => .byref element
  | none => type

/-- The type a method returns at run time: an `init` accessor's `void` loses its modifier. -/
def declaredReturn : ResolvedType → ResolvedType
  | .modified true modifier (.primitive 1) =>
    if isInitModifier modifier then .primitive 1 else .modified true modifier (.primitive 1)
  | type => type

/-- A call site's parameter type: substituted inside an `in` reference, which then loses its
    modifier, and substituted whole otherwise. -/
def siteParameter (methodArguments ownerArguments : Option (List ResolvedType))
    (type : ResolvedType) : Option ResolvedType :=
  match inReference type with
  | some element =>
    .byref <$> substituteResolved methodArguments ownerArguments resolveFuel element
  | none => substituteResolved methodArguments ownerArguments resolveFuel type

/-- A call site's return type: substituted, then an `init` accessor's `void` loses its
    modifier. -/
def siteReturn (methodArguments ownerArguments : Option (List ResolvedType))
    (type : ResolvedType) : Option ResolvedType :=
  declaredReturn <$> substituteResolved methodArguments ownerArguments resolveFuel type

/-- A declared type of a method instantiated at the given arguments, as Cecil writes the
    instance: an `in` reference is substituted inside and keeps its modifier, any other type is
    substituted whole, and a parameter with no argument fails. -/
def instanceType (methodArguments ownerArguments : List ResolvedType) (type : ResolvedType) :
    Option ResolvedType :=
  match type with
  | .modified true modifier (.byref element) =>
    if isInModifier modifier && !hasModifier resolveFuel element then
      (fun inner => .modified true modifier (.byref inner)) <$>
        substituteResolved (some methodArguments) (some ownerArguments) resolveFuel element
    else substituteResolved (some methodArguments) (some ownerArguments) resolveFuel type
  | _ => substituteResolved (some methodArguments) (some ownerArguments) resolveFuel type

/-! ## The relation between resolved types and the extractor's types -/

/-- How the extractor's types read the generic parameters and the primitive types of one
    signature: the identity of the primitive assembly, the scope Cecil gives a modified type
    whose element is a generic parameter, the number of method generic parameters that precede
    the owner's, and the number of the owner's. -/
structure Frame where
  corlib : Option (List Nat)
  anchor : List Nat
  arity : Nat
  ownerArity : Nat

/-- A class, interface or external type that may be a class. -/
def classLike : TypeKind → Bool
  | .classType | .interfaceType | .external (some false) | .external none => true
  | _ => false

/-- A value type, or an external type that may be one. -/
def valueLike : TypeKind → Bool
  | .valueType | .external (some true) | .external none => true
  | _ => false

/-- Whether a type is an enum found in a carried slice. -/
def NamedType.isEnum (named : NamedType) : Bool :=
  match named.kind with
  | .enumType _ => true
  | _ => false

/-- Whether a name is that of a primitive type to which `typeStorage` gives value storage as an
    atom of the runtime scope: the boolean, character, integer and native integer types. -/
def valueAtomName (name : List Nat) : Bool :=
  [0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x18, 0x19].any fun code =>
    primitiveName code == some name

/-- The integer element types an enum may have, spelled as atoms of the primitive assembly. -/
def integerAtom (frame : Frame) : TypeExpr → Bool
  | .atom scope name =>
    frame.corlib == some (bytesOf scope) &&
      ((List.range 8).any fun offset => primitiveName (0x04 + offset) == some (bytesOf name))
  | _ => false

mutual

/-- Whether the extractor's `TypeExpr` names the resolved type. The scope, the name and the kind
    facts come from the metadata; the constructor is the extractor's choice among those the kind
    allows. `fuel` bounds the nesting. -/
def typeAdmits (frame : Frame) : Nat → ResolvedType → TypeExpr → Bool
  | 0, _, _ => false
  | fuel + 1, type, expr =>
    match type, expr with
    | .primitive code, .void => code == 0x01
    | .primitive code, .atom scope name =>
      code != 0x01 && frame.corlib == some (bytesOf scope) &&
        primitiveName code == some (bytesOf name)
    | .primitive 0x0E, .object scope name =>
      frame.corlib == some (bytesOf scope) && bytesOf name == systemStringName
    -- A type that cannot be a value type is never the runtime's primitive with value storage.
    | .named named, .atom scope name =>
      named.scope == bytesOf scope && named.name == bytesOf name && !named.isEnum &&
        (valueLike named.kind || !(named.scope == runtimeScopeBytes && valueAtomName named.name))
    | .named named, .object scope name =>
      named.scope == bytesOf scope && named.name == bytesOf name && classLike named.kind
    | .named named, .aggregate identity _ =>
      bytesOf identity == named.scope ++ [58, 58] ++ named.name && valueLike named.kind
    | .named named, .enum identity underlying =>
      bytesOf identity == named.scope ++ [58, 58] ++ named.name &&
        match named.kind with
        | .enumType code => typeAdmits frame fuel (.primitive code) underlying
        | .external (some true) | .external none => integerAtom frame underlying
        | _ => false
    | .var index, .parameter number => index < frame.ownerArity && number == frame.arity + index
    -- Past the arity, a method parameter's index would be an owner parameter's.
    | .mvar index, .parameter number => index < frame.arity && number == index
    | .byref element, .byref inner => typeAdmits frame fuel element inner
    | .pointer element, .pointer inner => typeAdmits frame fuel element inner
    | .szarray element, .array inner => typeAdmits frame fuel element inner
    | .genericInst head arguments, .aggregate identity _ =>
      valueLike head.kind &&
        (if head.pinned then
          match frame.corlib with
          | some corlib => aggregateSpelling corlib fuel (.genericInst head arguments)
          | none => none
        else (fun spelled => head.scope ++ [58, 58] ++ spelled) <$>
          cecilName false fuel (.genericInst head arguments)) == some (bytesOf identity)
    | .genericInst head arguments, expr => appliedAdmits frame fuel head arguments expr
    | .functionPointer convention result parameters,
        .functionPointer expectedResult expectedParameters expectedConvention hasThis
          explicitThis =>
      expectedConvention == convention % 0x20 && hasThis == (convention / hasThisFlag % 2 == 1) &&
        explicitThis == (convention / explicitThisFlag % 2 == 1) &&
        typeAdmits frame fuel result expectedResult &&
        chainAdmits frame fuel parameters expectedParameters
    | .modified required modifier element, .atom scope name =>
      bytesOf scope == frame.anchor &&
        cecilName false fuel (.modified required modifier element) == some (bytesOf name)
    | _, _ => false

/-- A generic instance whose head and arguments the `apply` chain of `expr` repeats. -/
def appliedAdmits (frame : Frame) : Nat → NamedType → ResolvedList → TypeExpr → Bool
  | 0, _, _, _ => false
  | fuel + 1, head, arguments, expr =>
    match appliedArguments expr with
    | (.constructor scope name, expected) =>
      bytesOf scope == head.scope && bytesOf name == head.name &&
        argumentsAdmit frame fuel arguments expected
    | _ => false

/-- Whether each resolved argument is named by the matching extractor type. -/
def argumentsAdmit (frame : Frame) : Nat → ResolvedList → List TypeExpr → Bool
  | 0, _, _ => false
  | _ + 1, .nil, [] => true
  | fuel + 1, .cons head tail, expr :: rest =>
    typeAdmits frame fuel head expr && argumentsAdmit frame fuel tail rest
  | _ + 1, _, _ => false

/-- Whether the parameters of a function pointer are the `signatureParameter` chain, which
    ends in `void`. -/
def chainAdmits (frame : Frame) : Nat → ResolvedList → TypeExpr → Bool
  | 0, _, _ => false
  | _ + 1, .nil, .void => true
  | fuel + 1, .cons head tail, .signatureParameter expected rest =>
    typeAdmits frame fuel head expected && chainAdmits frame fuel tail rest
  | _ + 1, _, _ => false

end

/-- Whether the resolved type is named by the extractor's type, with the usual nesting bound. -/
def Frame.admits (frame : Frame) (type : ResolvedType) (expr : TypeExpr) : Bool :=
  typeAdmits frame (resolveFuel + 2) type expr

end CIL.Extraction
