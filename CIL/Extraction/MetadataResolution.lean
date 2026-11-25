import CIL.Extraction.Signatures
import CIL.Extraction.Generics
import CIL.Extraction.PlatformDefinitions
import Std.Data.TreeMap.Raw.Basic

/-!
# Resolving metadata names and types

A signature type names its classes and value types by token of the slice the blob comes from.
This file gives a token a scoped name and a kind, following `TypeRef` scopes and nested types,
and finds the `TypeDef` of a type the carried slices define. `ResolvedType` is independent of
the slice a type was read in, so a call site's generic arguments can be substituted into a
callee's signature from another slice. `typeAdmits` states when an extractor's `TypeExpr`
names a resolved type; it is a relation because the extractor picks the `TypeExpr`
constructor (`atom`, `object`, `aggregate`, `enum`) among those the resolved kind allows.

Pinned types take their kinds from their carried metadata. For a platform type the extractor
supplies a scoped table entry, including the storage code of an enum. Lean checks each lookup.
Agreement with the platform image bytes remains trusted.
-/

namespace CIL.Extraction

/-- The storage kind of a named type. A resolved enum retains its integer element code.
    Other platform types record their value-or-reference marker. A modifier read by name alone
    has no marker. -/
inductive TypeKind where
  | valueType
  | enumType (underlying : Nat)
  | classType
  | interfaceType
  /-- The declaring name of a linked static import has no storage classification. -/
  | importedOwner
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
  platformArity : Nat := 0
  /-- Identity columns of the defining Assembly or the external AssemblyRef. -/
  assembly : Option AssemblyColumns := none
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

/-- The number of arguments supplied to a constructed head. -/
def ResolvedList.length : ResolvedList -> Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

/-- The chain of a list of types. -/
def ResolvedList.ofList : List ResolvedType → ResolvedList
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

/-- A prefix trie with indexed byte children and exact prefix membership at each node. -/
inductive AssemblyPrefixes where
  | node (terminal : Bool) (children : Std.TreeMap.Raw Nat AssemblyPrefixes)

/-- An empty trie contains no prefixes. -/
instance : EmptyCollection AssemblyPrefixes := ⟨.node false {}⟩

/-- Insert one prefix, retaining shared nodes. -/
def AssemblyPrefixes.insert : AssemblyPrefixes → List Nat → AssemblyPrefixes
  | .node _ children, [] => .node true children
  | .node terminal children, byte :: rest =>
    let child := (children[byte]?).getD {}
    .node terminal (children.insert byte (child.insert rest))

/-- Whether the supplied identity begins with any stored prefix. -/
def AssemblyPrefixes.matches : AssemblyPrefixes → List Nat → Bool
  | .node true _, _ => true
  | .node false _, [] => false
  | .node false children, byte :: rest =>
    match children[byte]? with
    | some child => child.matches rest
    | none => false

/-- The package's complete assembly identities, indexed by their exact bytes. -/
abbrev ExactPins := Std.TreeMap.Raw (List Nat) Unit

/-- Index each full pin once per package. -/
def indexPins (names : List (List Nat)) : ExactPins :=
  names.foldl (fun entries name => entries.insert name ()) {}

/-- Binary search of a materialized identity index, with structural fuel for kernel reduction. -/
def containsName (names : Array (List Nat)) (key : List Nat) : Bool :=
  search names.size 0 names.size
where
  /-- A half-open interval contains the key only if one of its two halves or its midpoint does. -/
  search : Nat -> Nat -> Nat -> Bool
    | 0, _, _ => false
    | fuel + 1, low, high => Id.run do
      if low >= high then return false
      let middle := (low + high) / 2
      let some atMiddle := names[middle]? | return false
      return match compare key atMiddle with
        | .eq => true
        | .lt => search fuel low middle
        | .gt => search fuel (middle + 1) high

/-- Indexed metadata and assembly identities derived together from checked metadata. -/
structure MetadataEnv where
  slices : SearchTree MetadataIndex
  identities : Std.TreeMap.Raw (List Nat) Nat
  pinned : AssemblyPrefixes
  exactPins : ExactPins
  /-- What the checks rely on about the types no carried slice defines. -/
  platform : PlatformTable
  /-- Exact value-layout identities published by the selected import slots. -/
  publishedLayouts : Array (List Nat) := #[]
  /-- Available when resolving a body against its program layout table. -/
  layoutDeclarations : Option (Array LayoutIdentity) := none

/-- Build all assembly lookups once, keeping the first occurrence of each identity. -/
def MetadataEnv.ofSlices (slices : List MetadataIndex) (pinned : AssemblyPrefixes := {})
    (platform : PlatformTable := {}) (exactPins : ExactPins := {}) : MetadataEnv := Id.run do
  let mut identities : Std.TreeMap.Raw (List Nat) Nat := {}
  let mut position := 0
  for index in slices do
    if !identities.contains index.identity then
      identities := identities.insert index.identity position
    position := position + 1
  return {
    slices := SearchTree.ofSorted (slices.zipIdx.map fun (index, position) => (position, index))
    identities := identities
    pinned := pinned
    exactPins := exactPins
    platform := platform }

/-- The slice at a position, or `unresolvedType` for a token that points outside the list. -/
def MetadataEnv.slice (env : MetadataEnv) (position token : Nat) :
    Except MetadataError MetadataIndex :=
  match env.slices.find? position with
  | some index => .ok index
  | none => .error (.unresolvedType token)

/-- The slice, link-resolved: the link of a kind from a token, if the slice states one. -/
def IndexTables.link (index : IndexTables) (kind source : Nat) : Option (Nat × Nat) :=
  index.links.find? (kind * 0x100000000 + source)

/-- How deeply names, enclosing types and signature types may nest. -/
def resolveFuel : Nat := 32

/-- The simple name of an assembly identity followed by `versionMarker`: every identity of an
    assembly of that name, at any version, culture or key, starts with it. -/
def assemblyStem : List Nat → List Nat
  | [] => []
  | byte :: rest =>
    if versionMarker.isPrefixOf (byte :: rest) then versionMarker else byte :: assemblyStem rest

/-- The package's complete pin identities and their checked prefix and exact lookup tables. -/
structure PinnedIndex where
  identities : List (List Nat)
  prefixes : AssemblyPrefixes
  indexed : prefixes = (identities.map assemblyStem).foldl AssemblyPrefixes.insert {}
  exact : ExactPins
  exactIndexed : exact = indexPins identities

/-- Construct a checked index directly from its complete identity list. -/
def PinnedIndex.ofIdentities (identities : List (List Nat)) : PinnedIndex :=
  { identities, prefixes := (identities.map assemblyStem).foldl AssemblyPrefixes.insert {},
    indexed := rfl, exact := indexPins identities, exactIndexed := rfl }

/-- Complete identities determine every component of a checked pin index. -/
theorem PinnedIndex.ext {first second : PinnedIndex}
    (identities : first.identities = second.identities) : first = second := by
  cases first with
  | mk first firstPrefixes firstIndexed firstExact firstBound =>
    cases second with
    | mk second secondPrefixes secondIndexed secondExact secondBound =>
      dsimp at identities
      subst second
      cases firstIndexed
      cases secondIndexed
      cases firstBound
      cases secondBound
      rfl
#print axioms PinnedIndex.ext

/-- Checked pin indexes are equal exactly when their complete identities are equal. -/
instance : DecidableEq PinnedIndex := fun first second =>
  if same : first.identities = second.identities then .isTrue (PinnedIndex.ext same)
  else .isFalse (fun equal => same (congrArg PinnedIndex.identities equal))

/-- The complete identities determine the displayed pin index. -/
instance : Repr PinnedIndex where
  reprPrec index precedence := reprPrec index.identities precedence

/-- `Namespace.Name`, or the bare name for the global namespace. -/
def qualifiedName (namespace_ name : List Nat) : List Nat :=
  if namespace_.isEmpty then name else namespace_ ++ 46 :: name

/-- The name of a type nested in an enclosing one. -/
def nestedName (enclosing name : List Nat) : List Nat := enclosing ++ 47 :: name

/-- The full name a type's name parts spell, as `typeRefQualified` spells it: the outermost
    type's namespace and name, then each nested type's name; `none` when the parts are no pairs. -/
def partsName : List (List Nat) → Option (List Nat)
  | space :: simple :: nested => nestedParts (qualifiedName space simple) nested
  | _ => none
where
  /-- The name of the types nested in `name` that the remaining parts give. -/
  nestedParts (name : List Nat) : List (List Nat) → Option (List Nat)
    | [] => some name
    | _ :: simple :: rest => nestedParts (nestedName name simple) rest
    | [_] => none

/-- Read one of the four unsigned 16-bit version components in a metadata assembly identity. -/
private def versionPart? (input : List Nat) : Option (List Nat) := do
  let digits := input.takeWhile fun b => 48 ≤ b && b ≤ 57
  let count := digits.length
  guard (0 < count && count ≤ 5 && (count == 1 || digits.head? != some 48))
  guard (digits.foldl (fun n b => 10 * n + (b - 48)) 0 ≤ 65535)
  return input.drop count

/-- The suffix after the remaining dotted version components. -/
private def versionSuffix? : Nat → List Nat → Option (List Nat)
  | 0, input => versionPart? input
  | n + 1, input => do
    let 46 :: next ← versionPart? input | none
    versionSuffix? n next
/-- Check the complete neutral core assembly identity, including its publisher and version. -/
def isCorlibScope (scope : List Nat) : Bool := Id.run do
  let name := scope.takeWhile (· != 44)
  let some metadataName := MetadataName.ofBytes? name | return false
  let some publisher := coreLibraryKey? metadataName | return false
  let rest := scope.drop name.length
  unless versionMarker.isPrefixOf rest do return false
  let some suffix := versionSuffix? 3 (rest.drop versionMarker.length) | return false
  return suffix == cultureMarker ++ neutralCulture ++ tokenMarker ++
    bytesOf (publicKeyTokenText (some publisher))

/-- A base TypeRef counts as a core-library type when its scope names the platform publisher. -/
def MetadataIndex.coreLibraryReference (index : MetadataIndex) (token : Nat) :
    Except MetadataError Bool := do
  let row ← index.typeRef token
  if metadataTableOf row.scope != Table.assemblyRef then return false
  index.coreAssemblyRef row.scope

/-- CoreLib defines its own primitives. Other slices identify their primitive assembly by its
    AssemblyRef row, if present. -/
def MetadataIndex.corlibIdentity (index : MetadataIndex) :
    Except MetadataError (Option (List Nat)) :=
  if index.corlib == 0 then
    .ok (if index.identity == bytesOf coreLibraryScope then some index.identity else none)
  else do
    let token ← checkedTokenOf Table.assemblyRef index.corlib .rowOverflow
    if !(← index.coreAssemblyRef token) then throw (.unsupportedAssemblyRef token)
    .ok (some (← index.assemblyRefIdentity token))

/-- A display-name lookup may select a carried slice only when all four identity fields agree
    with its Assembly row. A missing slice leaves resolution to the platform or import checks. -/
def MetadataEnv.referencePosition (env : MetadataEnv) (columns : AssemblyColumns) (token : Nat) :
    Except MetadataError (Option Nat) := do
  let some position := env.identities[columns.spelling]? | return none
  let target ← env.slice position token
  unless target.assembly == some columns do throw (.operandMismatch token)
  return some position

/-- A carried reference resolves only to a slice with the same assembly identity columns. -/
theorem MetadataEnv.referencePosition_columns {env : MetadataEnv} {columns : AssemblyColumns}
    {token position : Nat} (found : env.referencePosition columns token = .ok (some position)) :
    ∃ target, env.slice position token = .ok target ∧ target.assembly = some columns := by
  unfold MetadataEnv.referencePosition at found
  cases lookup : env.identities[columns.spelling]? with
  | none => simp [lookup, pure, Except.pure] at found
  | some selected =>
    cases read : env.slice selected token with
    | error err => simp [lookup, read, bind, Except.bind] at found
    | ok target =>
      by_cases same : target.assembly = some columns
      · simp [lookup, read, same, bind, Except.bind, pure, Except.pure] at found
        exact found ▸ ⟨target, read, same⟩
      · simp [lookup, read, same, bind, Except.bind, pure, Except.pure, throw, MonadExceptOf.throw] at found
#print axioms MetadataEnv.referencePosition_columns

/-- The scope, full name and name parts a `TypeRef` spells: its assembly, or the outermost
    enclosing type's. -/
def typeRefQualified (env : MetadataEnv) (position : Nat) :
    Nat → Nat → Except MetadataError (AssemblyColumns × List Nat × List (List Nat))
  | 0, token => .error (.unresolvedType token)
  | fuel + 1, token => do
    let index ← env.slice position token
    let row ← index.typeRef token
    let namespace_ ← index.string row.namespace_
    let simple ← index.string row.name
    let name := qualifiedName namespace_ simple
    match metadataTableOf row.scope with
    | 0x23 => do
      let columns ← index.referenceColumns row.scope
      let _ ← env.referencePosition columns token
      return (columns, name, [namespace_, simple])
    | 0x00 => do
      let some assembly := index.assembly | throw (.missingSlice token)
      return (assembly, name, [namespace_, simple])
    | 0x01 =>
      let (scope, enclosing, parts) ← typeRefQualified env position fuel row.scope
      .ok (scope, nestedName enclosing simple, parts ++ [namespace_, simple])
    | _ => .error (.unsupportedScope token)

/-- The first instance field among `count` consecutive `Field` rows from `row`: a scan that
    stops at the first instance field, which an enum declares before its constants. -/
def firstInstanceField (index : MetadataIndex) : Nat → Nat → Except MetadataError (Option Nat)
  | 0, _ => .ok none
  | count + 1, row => do
    let token ← checkedTokenOf Table.field row .rowOverflow
    let field ← index.field token
    if field.flags / 0x10 % 2 == 1 then firstInstanceField index count (row + 1)
    else .ok (some token)
/-- The first `Field` row after a type's own: the next `TypeDef`'s, or one past the table. -/
def MetadataIndex.fieldEnd (index : MetadataIndex) (token : Nat) (row : TypeDefRow) :
    Except MetadataError Nat :=
  if tokenRow token == index.header.rows Table.typeDef then
    .ok (index.header.rows Table.field + 1)
  else do
    let next ← index.typeDef (← checkedTokenOf Table.typeDef (tokenRow token + 1) .rowOverflow)
    if next.fieldList < row.fieldList then throw (.unresolvedType token)
    .ok next.fieldList

/-- The fields of a type, in table order. -/
def MetadataIndex.fieldRange (index : MetadataIndex) (token : Nat) :
    Except MetadataError (Nat × Nat) := do
  let row ← index.typeDef token
  .ok (row.fieldList, ← index.fieldEnd token row)

/-- Whether an element type code is one of the eight integer types an enum may have. -/
def integerElement (code : Nat) : Bool := 0x04 ≤ code && code ≤ 0x0B

/-- The integer element type of the single instance field of an enum. -/
def enumUnderlying (index : MetadataIndex) (token : Nat) : Except MetadataError Nat := do
  let (start, stop) ← index.fieldRange token
  if index.instanceTotal.find? token != some 1 then throw (.unresolvedType token)
  match ← firstInstanceField index (stop - start) start with
  | some field =>
    let row ← index.field field
    match ← decodeFieldSig (← index.blob row.signature) with
    | .primitive code =>
      if integerElement code then .ok code else .error (.unresolvedType token)
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

/-- An external storage root must have its exact core name and matching platform definition. -/
def baseFits (core : Bool) (parts : List (List Nat)) : PlatformKind → Bool
  | .enumRoot => core && parts == [systemNamespace, enumName]
  | .valueTypeRoot => core && parts == [systemNamespace, valueTypeName]
  | _ => false

/-- The kind of a type whose base `base` no carried slice defines, from the base's platform
    definition: an enum with the underlying type of its instance field, a value type or a
    class. -/
def MetadataEnv.externalBaseKind (env : MetadataEnv) (index : MetadataIndex) (token base : Nat)
    (scope : List Nat) (parts : List (List Nat)) (core : Bool) : Except MetadataError TypeKind :=
  if env.pinned.matches scope then .error (.missingSlice base)
  else if !core || (parts != [systemNamespace, enumName] &&
      parts != [systemNamespace, valueTypeName]) then .ok .classType
  else match env.platform.require base scope parts (baseFits core parts) with
    | .error error => .error error
    | .ok .enumRoot => .enumType <$> enumUnderlying index token
    | .ok .valueTypeRoot => .ok .valueType
    | .ok _ => .ok .classType

/-- A type is an enum or a value type through an external base only when the base's platform
    definition is `System.Enum` or `System.ValueType`, named so in a core-library scope. -/
theorem MetadataEnv.externalBaseKind_value {env : MetadataEnv} {index : MetadataIndex}
    {token base : Nat} {scope : List Nat} {parts : List (List Nat)} {core : Bool}
    {kind : TypeKind} (found : env.externalBaseKind index token base scope parts core = .ok kind)
    (value : kind = .valueType ∨ ∃ underlying, kind = .enumType underlying) :
    core = true ∧
      ({ scope, parts, kind := .enumRoot } ∈ env.platform.definitions ∧
          parts = [systemNamespace, enumName] ∨
        { scope, parts, kind := .valueTypeRoot } ∈ env.platform.definitions ∧
          parts = [systemNamespace, valueTypeName]) := by
  unfold MetadataEnv.externalBaseKind at found
  split at found
  · cases found
  split at found
  case isTrue =>
    cases found
    simp at value
  split at found
  · cases found
  · rename_i required
    have ⟨member, fits⟩ := PlatformTable.require_ok required
    simp only [baseFits, Bool.and_eq_true, beq_iff_eq] at fits
    exact ⟨fits.1, .inl ⟨member, fits.2⟩⟩
  · rename_i required
    have ⟨member, fits⟩ := PlatformTable.require_ok required
    simp only [baseFits, Bool.and_eq_true, beq_iff_eq] at fits
    exact ⟨fits.1, .inr ⟨member, fits.2⟩⟩
  · cases found
    rcases value with value | ⟨_, value⟩ <;> cases value

#print axioms MetadataEnv.externalBaseKind_value

/-! ## Generic parameter runs -/

/-- The `GenericParam` rows that name `owner`, from the row its link gives while they continue. -/
private def genericRun (index : MetadataIndex) (owner : Nat) :
    Nat → Nat → Except MetadataError (List GenericParamRow)
  | 0, _ => .ok []
  | fuel + 1, row =>
    if index.header.rows Table.genericParam < row then .ok []
    else do
      let entry ← index.genericParam (← checkedTokenOf Table.genericParam row .rowOverflow)
      if entry.owner != owner then .ok []
      else do .ok (entry :: (← genericRun index owner fuel (row + 1)))

/-- No `GenericParam` row names `owner`, given the table is sorted by coded owner as ECMA-335
    requires: the first carried row above the owner's code is row 1 or follows a carried row
    below it, or the table's last row lies below it, or the table has no rows. -/
def MetadataIndex.noGenericParameters (index : MetadataIndex) (owner : Nat) :
    Except MetadataError Unit := do
  let code := genericOwnerCode owner
  let codeAt (row : Nat) : Except MetadataError Nat := do
    let token ← checkedTokenOf Table.genericParam row .rowOverflow
    .ok (genericOwnerCode (← index.genericParam token).owner)
  let last := index.header.rows Table.genericParam
  let bracketed : Bool ← match index.genericOwners.above? code with
    | some (_, (first, _)) => do
      let above := decide (code < (← codeAt (tokenRow first)))
      if tokenRow first == 1 then pure above
      else do pure (above && decide ((← codeAt (tokenRow first - 1)) < code))
    | none => if last == 0 then pure true else do pure (decide ((← codeAt last) < code))
  if !bracketed then throw (.unresolvedMember owner)

/-- The generic parameters of a `TypeDef` or `MethodDef` owner: every carried parameter of
    the owner belongs to its contiguous zero-based run, and an owner with no carried parameter
    has neighbours that show it has none. An optional link must name the run's first row in the
    current metadata position. -/
def MetadataIndex.genericParameters (index : MetadataIndex) (position owner : Nat) :
    Except MetadataError (List GenericParamRow) := do
  let table := metadataTableOf owner
  if table != Table.typeDef && table != Table.methodDef then throw (.unsupportedTable owner)
  match index.genericOwners.find? (genericOwnerCode owner) with
  | none =>
    if (index.link linkGenericParams owner).isSome then throw (.unresolvedMember owner)
    index.noGenericParameters owner
    .ok []
  | some (first, count) => do
    if (index.link linkGenericParams owner).any (· != (position, first)) then
      throw (.unresolvedMember owner)
    if metadataTableOf first != Table.genericParam || tokenRow first == 0 then
      throw (.tokenOutOfScope first)
    if 1 < tokenRow first then
      let previous ← checkedTokenOf Table.genericParam (tokenRow first - 1) .rowOverflow
      if (← index.genericParam previous).owner == owner then throw (.unresolvedMember owner)
    let run ← genericRun index owner (index.header.rows Table.genericParam) (tokenRow first)
    if run.length == count &&
        (run.zipIdx.all fun (entry, number) => entry.number == number) then .ok run
    else .error (.unresolvedMember owner)

/-- The generic parameters of a `MethodDef` whose signature declares `declared` of them. A
    signature without the GENERIC flag declares none, as ECMA-335 requires of the method's rows,
    so a method with no carried run and no link has none without neighbours; carried rows are
    checked as for any owner. -/
def MetadataIndex.methodGenericParameters (index : MetadataIndex)
    (position method declared : Nat) : Except MetadataError (List GenericParamRow) :=
  if declared == 0 && (index.genericOwners.find? (genericOwnerCode method)).isNone &&
      (index.link linkGenericParams method).isNone then .ok []
  else index.genericParameters position method

/-- A forwarded class and every enclosing class are public in the destination image.
    Each NestedClass row must join the checked TypeDefs at the same metadata position. -/
private def publicForwarded (index : MetadataIndex) (position token : Nat) :
    List (List Nat) → Except MetadataError Unit
  | name :: space :: enclosing => do
    let row ← index.typeDef token
    unless (← index.string row.name) == name && (← index.string row.namespace_) == space do
      throw (.operandMismatch token)
    if enclosing.isEmpty then
      unless row.flags % 8 == 1 do throw (.operandMismatch token)
    else
      unless row.flags % 8 == 2 && space.isEmpty do throw (.operandMismatch token)
      let some (linked, nesting) := index.link linkNesting token | throw (.unresolvedType token)
      unless linked == position do throw (.unresolvedType token)
      let nested ← index.nestedClass nesting
      unless nested.nested == token do throw (.operandMismatch token)
      publicForwarded index position nested.enclosing enclosing
  | _ => .error (.operandMismatch token)

/-- Resolve a definition link in the referenced assembly or through a top-level forwarder.
    The facade's AssemblyRef names the implementation slice and its exported name matches
    the original TypeRef. -/
private def checkedDefinitionLink (env : MetadataEnv) (index : MetadataIndex)
    (token target : Nat) (scope : List Nat) (parts : List (List Nat)) :
    Except MetadataError (Nat × Nat × List Nat) := do
  let some (linked, definition) := index.link linkDefinition token | throw (.unresolvedType token)
  if linked == target then return (linked, definition, scope)
  let some (facade, exported) := index.link linkForwarder token | throw (.unresolvedType token)
  if facade != target then throw (.unresolvedType token)
  let source ← env.slice facade exported
  if source.identity != scope then throw (.operandMismatch token)
  let destination ← source.forwardedAssembly exported parts
  if (← env.referencePosition destination token) != some linked then throw (.operandMismatch token)
  let implementation ← env.slice linked definition
  publicForwarded implementation linked definition parts.reverse
  return (linked, definition, destination.spelling)

/-- A carried reference binds the qualified name in the checked defining assembly. -/
private def linkedType (env : MetadataEnv) (position token target : Nat) (scope : List Nat)
    (parts : List (List Nat)) (resolve : Nat → Nat → Except MetadataError NamedType) :
    Except MetadataError NamedType := do
  let index ← env.slice position token
  let (linked, definition, identity) ← checkedDefinitionLink env index token target scope parts
  let named ← resolve linked definition
  if named.scope != identity || named.parts != parts then throw (.operandMismatch token)
  return named

/-- A modifier needs the qualified name of each enclosing local definition. -/
private def modifierDefinition (env : MetadataEnv) (position : Nat) :
    Nat → Nat → Except MetadataError NamedType
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
        let enclosing ← modifierDefinition env position fuel nested.enclosing
        pure (nestedName enclosing.name simple, enclosing.parts ++ [namespace_, simple])
    .ok { scope := index.identity, name, parts, kind := .external none, pinned := false,
          assembly := index.assembly }

/-- The storage kind of a resolved platform type, including an enum's integer element code. -/
def PlatformKind.resolvedKind : PlatformKind → TypeKind
  | .enumType code _ => .enumType code
  | kind => .external (some kind.isValue)

/-- The named type of a reference to a type no carried slice defines: a scope of a pinned name
    is refused, and the type's platform definition must agree with the value-or-class hint and
    gives its kind. -/
def MetadataEnv.externalNamed (env : MetadataEnv) (token : Nat) (assembly : AssemblyColumns)
    (name : List Nat) (parts : List (List Nat)) (hint : Option Bool) : Except MetadataError NamedType :=
  let scope := assembly.spelling
  if env.pinned.matches scope then .error (.missingSlice token)
  else match env.platform.require token scope parts (PlatformKind.fitsHint hint) with
    | .error error => .error error
    | .ok kind =>
      .ok { scope, name, parts, kind := kind.resolvedKind, pinned := false,
            platformArity := kind.arity, assembly := some assembly }

/-- An external type has a platform definition of its scope and name parts that agrees with the
    hint it was read with and determines its storage kind. -/
theorem MetadataEnv.externalNamed_ok {env : MetadataEnv} {token : Nat} {scope : AssemblyColumns}
    {name : List Nat}
    {parts : List (List Nat)} {hint : Option Bool} {named : NamedType}
    (resolved : env.externalNamed token scope name parts hint = .ok named) :
    ∃ kind, { scope := named.scope, parts := named.parts, kind } ∈ env.platform.definitions ∧
      kind.fitsHint hint = true /\ named.kind = kind.resolvedKind /\
      named.platformArity = kind.arity /\ named.pinned = false := by
  simp only [MetadataEnv.externalNamed] at resolved
  split at resolved
  · cases resolved
  · split at resolved
    · cases resolved
    · rename_i kind required
      cases resolved
      exact Exists.intro kind (And.intro (PlatformTable.require_ok required).1
        (And.intro (PlatformTable.require_ok required).2 (And.intro rfl (And.intro rfl rfl))))

#print axioms MetadataEnv.externalNamed_ok

/-- Cecil qualifies each nested segment with its own namespace in a modifier's full name. -/
private def modifierFullName : List (List Nat) → List Nat
  | namespace_ :: simple :: rest =>
    let name := qualifiedName namespace_ simple
    if rest.isEmpty then name else name ++ 47 :: modifierFullName rest
  | _ => []

/-- A custom modifier names its assembly and enclosing types without requiring the definition
    of an externally referenced modifier or the base type of a local one. -/
def modifierNamed (env : MetadataEnv) (position token : Nat) : Except MetadataError NamedType := do
  let (assembly, _, parts) ← match metadataTableOf token with
    | 0x01 => typeRefQualified env position resolveFuel token
    | 0x02 => do
      let named ← modifierDefinition env position resolveFuel token
      let some columns := named.assembly | throw (.missingSlice token)
      pure (columns, named.name, named.parts)
    | _ => throw (.unsupportedTable token)
  pure { scope := assembly.spelling, name := modifierFullName parts, parts,
         kind := .external none, pinned := false, assembly := some assembly }

/-- A named type in a closed argument comes from a definition row or a scoped platform entry. -/
inductive ArgumentHead where
  | definition (scope : AssemblyColumns) (token : Nat)
  | platform (scope : AssemblyColumns) (parts : List (List Nat))
  deriving DecidableEq, Repr

mutual

/-- The primitive, named, vector-array and constructed types admitted as closed arguments. -/
inductive InstanceArgument where
  | primitive (code : Nat)
  | named (head : ArgumentHead)
  | szarray (element : InstanceArgument)
  | genericInst (head : ArgumentHead) (arguments : InstanceArguments)
  deriving DecidableEq, Repr

/-- The ordered arguments of a constructed type. -/
inductive InstanceArguments where
  | nil
  | cons (head : InstanceArgument) (tail : InstanceArguments)
  deriving DecidableEq, Repr

end

/-- Whether a signature's class-or-value-type byte agrees with a type found in a carried
    slice. -/
def hintAgrees : TypeKind → Option Bool → Bool
  | .importedOwner, _ => false
  | .valueType, some valueType | .enumType _, some valueType => valueType
  | .classType, some valueType | .interfaceType, some valueType => !valueType
  | _, _ => true

/-- The number of generic parameters of the definition a `TypeDef` token, or a `TypeRef` linked
    to a carried slice, names. -/
def MetadataEnv.definitionArity (env : MetadataEnv) (position token : Nat) :
    Except MetadataError Nat := do
  let index ← env.slice position token
  let (linked, definition) ← match metadataTableOf token with
    | 0x02 => pure (position, token)
    | 0x01 =>
      match index.link linkDefinition token with
      | some target => pure target
      | none => throw (.unresolvedType token)
    | _ => throw (.unsupportedTable token)
  .ok (← (← env.slice linked definition).genericParameters linked definition).length

/-- A named head takes the arity of its carried rows or its resolved platform definition. -/
def MetadataEnv.requireArity (env : MetadataEnv) (position token : Nat) (named : NamedType)
    (arity : Nat) : Except MetadataError Unit :=
  let check (count : Nat) : Except MetadataError Unit :=
    if count == arity then .ok () else .error (.genericMismatch token)
  if named.pinned then do check (<- env.definitionArity position token)
  else check named.platformArity

mutual

/-- Resolve every token of a signature type read in the slice at `position`. -/
def resolveType (env : MetadataEnv) (position : Nat)
    (readNamed : Nat -> Option Bool -> Except MetadataError NamedType) :
    Nat -> SigType -> Except MetadataError ResolvedType
  | 0, _ => .error (.unresolvedType 0)
  | _ + 1, .primitive code => .ok (.primitive code)
  | _ + 1, .named valueType token => do
    let named <- readNamed token (some valueType)
    env.requireArity position token named 0
    .ok (.named named)
  | _ + 1, .var index => .ok (.var index)
  | _ + 1, .mvar index => .ok (.mvar index)
  | fuel + 1, .byref element => do
    .ok (.byref (<- resolveType env position readNamed fuel element))
  | fuel + 1, .pointer element => do
    .ok (.pointer (<- resolveType env position readNamed fuel element))
  | fuel + 1, .szarray element => do
    .ok (.szarray (<- resolveType env position readNamed fuel element))
  | fuel + 1, .genericInst valueType token arguments => do
    if let .nil := arguments then throw (.genericMismatch token)
    let head <- readNamed token (some valueType)
    let resolved <- resolveList env position readNamed fuel arguments
    env.requireArity position token head resolved.length
    .ok (.genericInst head resolved)
  | fuel + 1, .functionPointer convention result parameters => do
    let resolved <- resolveType env position readNamed fuel result
    let types <- resolveList env position readNamed fuel parameters
    .ok (.functionPointer convention resolved types)
  | fuel + 1, .modified required modifier element => do
    let named <- modifierNamed env position modifier
    .ok (.modified required named (<- resolveType env position readNamed fuel element))

/-- Resolve a chain of signature types. -/
def resolveList (env : MetadataEnv) (position : Nat)
    (readNamed : Nat -> Option Bool -> Except MetadataError NamedType) :
    Nat -> SigList -> Except MetadataError ResolvedList
  | 0, _ => .error (.unresolvedType 0)
  | _ + 1, .nil => .ok .nil
  | fuel + 1, .cons head tail => do
    let type <- resolveType env position readNamed fuel head
    .ok (.cons type (<- resolveList env position readNamed fuel tail))

end

/-- The definition of a resolved reference, or its external scope, spelling and name parts. -/
abbrev ReferenceTarget := Sum NamedType (AssemblyColumns × List Nat × List (List Nat))

/-- A reference links to its scoped definition or identifies an external name. -/
private def referenceTarget (env : MetadataEnv) (position token : Nat)
    (resolve : Nat -> Nat -> Except MetadataError NamedType) :
    Except MetadataError ReferenceTarget := do
  let (scope, name, parts) <- typeRefQualified env position resolveFuel token
  match env.identities[scope.spelling]? with
  | none => return .inr (scope, name, parts)
  | some target => .inl <$> linkedType env position token target scope.spelling parts resolve

/-- A signature head resolves through its definition or its scoped platform entry. -/
private def signatureHead (env : MetadataEnv) (position : Nat)
    (resolve : Nat -> Nat -> Except MetadataError NamedType) (token : Nat) (hint : Option Bool) :
    Except MetadataError NamedType := do
  let named <- match metadataTableOf token with
    | 0x02 => resolve position token
    | 0x01 => do
      match <- referenceTarget env position token resolve with
      | .inl named => pure named
      | .inr (scope, name, parts) =>
        match env.externalNamed token scope name parts hint with
        | .error (.missingPlatformDefinition missing) =>
          let published := containsName env.publishedLayouts (scope.spelling ++ [58, 58] ++ name)
          if hint != some false && published then
            pure { scope := scope.spelling, name, parts, kind := .valueType, pinned := false,
                   assembly := some scope }
          else throw (.missingPlatformDefinition missing)
        | result => result
    | _ => throw (.unsupportedTable token)
  if hintAgrees named.kind hint then return named else throw (.operandMismatch token)

/-- The namespace and simple names of a definition, from the outermost type inwards. -/
private def definitionParts (index : MetadataIndex) (position fuel token : Nat) (row : TypeDefRow)
    (inner : List (List Nat) := []) : Except MetadataError (List (List Nat)) := do
  match fuel with
  | 0 => throw (.unresolvedType token)
  | rest + 1 =>
    let parts := (<- index.string row.namespace_) :: (<- index.string row.name) :: inner
    if row.flags % 8 < 2 then return parts
    let some (linked, nesting) := index.link linkNesting token | throw (.unresolvedType token)
    if linked != position then throw (.unresolvedType token)
    let nested <- index.nestedClass nesting
    if nested.nested != token then throw (.unresolvedType token)
    definitionParts index position rest nested.enclosing (<- index.typeDef nested.enclosing) parts

/-- A resolved nesting chain yields the same name parts with extra lookup fuel. -/
private theorem definitionParts_add (index : MetadataIndex) (position fuel extra token : Nat)
    (row : TypeDefRow) (inner result : List (List Nat))
    (h : definitionParts index position fuel token row inner = .ok result) :
    definitionParts index position (fuel + extra) token row inner = .ok result := by
  induction fuel generalizing token row inner with
  | zero => simp [definitionParts, throw] at h
  | succ fuel ih =>
    rw [Nat.succ_add]
    simp only [definitionParts] at h ⊢
    cases hn : index.string row.namespace_ <;> simp [hn, Bind.bind, Except.bind] at h ⊢
    cases hs : index.string row.name <;> simp [hs] at h ⊢
    split at h <;> rename_i branch
    · simpa [branch] using h
    · simp [branch]
      cases hl : index.link linkNesting token with
      | none => simp [hl, throw] at h
      | some pair =>
        obtain ⟨linked, nesting⟩ := pair
        simp [hl] at h ⊢
        by_cases scope : linked = position
        · simp [scope] at h ⊢
          cases hr : index.nestedClass nesting with
          | error err => simp [hr] at h
          | ok nested =>
            simp [hr] at h ⊢
            by_cases same : nested.nested = token
            · simp [same] at h ⊢
              cases ht : index.typeDef nested.enclosing <;> simp [ht] at h ⊢
              exact ih _ _ _ h
            · simp [same, throw] at h
        · simp [scope, throw] at h
#print axioms definitionParts_add

/-- A carried root gives a storage kind only under its own core assembly and exact name. -/
private def carriedRootKind (index : MetadataIndex) (token : Nat) (scope : List Nat)
    (parts : List (List Nat)) : Except MetadataError TypeKind := do
  if !isCorlibScope scope then return .classType
  if parts == [systemNamespace, enumName] then return .enumType (<- enumUnderlying index token)
  if parts == [systemNamespace, valueTypeName] then return .valueType
  return .classType

/-- Flags and the exact identity of an immediate named base determine the storage kind. -/
def typeDefKind (env : MetadataEnv) (index : MetadataIndex) (position token : Nat)
    (row : TypeDefRow) (ownParts : List (List Nat)) : Except MetadataError TypeKind := do
  if row.flags &&& 0x20 != 0 then return .interfaceType
  let kind <- match metadataTableOf row.extends_ with
    | 0x02 => do
      if tokenRow row.extends_ == 0 || !isCorlibScope index.identity then pure .classType
      else
        let base <- index.typeDef row.extends_
        carriedRootKind index token index.identity
          (<- definitionParts index position resolveFuel row.extends_ base)
    | 0x01 => do
      let (assembly, _, parts) <- typeRefQualified env position resolveFuel row.extends_
      let scope := assembly.spelling
      match env.identities[scope]? with
      | none => do
        let core <- index.coreLibraryReference row.extends_
        env.externalBaseKind index token row.extends_ scope parts core
      | some target => do
        let (linked, definition, identity) ← checkedDefinitionLink env index row.extends_ target scope parts
        let base <- env.slice linked definition
        let baseParts <- definitionParts base linked resolveFuel definition
          (<- base.typeDef definition)
        if base.identity != identity || baseParts != parts then throw (.operandMismatch row.extends_)
        carriedRootKind index token base.identity baseParts
    | _ => pure .classType
  if kind == .valueType && ownParts == [systemNamespace, enumName] &&
      isCorlibScope index.identity then return .classType
  return kind

/-- A carried definition's scoped name and kind, independent of its base's layout. -/
def typeDefNamed (env : MetadataEnv) (position fuel token : Nat) :
    Except MetadataError NamedType := do
  let index <- env.slice position token
  let row <- index.typeDef token
  let parts <- definitionParts index position fuel token row
  let some name := partsName parts | throw (.unresolvedType token)
  let kind <- typeDefKind env index position token row parts
  return { scope := index.identity, name, parts, kind, pinned := true, assembly := index.assembly }

/-- Once the enclosing names resolve, any larger nesting budget recovers the same definition. -/
theorem typeDefNamed_of_le {env : MetadataEnv} {position fuel budget token : Nat} {named : NamedType}
    (bound : fuel ≤ budget) (resolved : typeDefNamed env position fuel token = .ok named) :
    typeDefNamed env position budget token = .ok named := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  unfold typeDefNamed at resolved ⊢
  cases hi : env.slice position token with
  | error err => simp [hi, Bind.bind, Except.bind] at resolved
  | ok index =>
    simp [hi, Bind.bind, Except.bind] at resolved ⊢
    cases hr : index.typeDef token with
    | error err => simp [hr] at resolved
    | ok row =>
      simp [hr] at resolved ⊢
      cases hp : definitionParts index position fuel token row with
      | error err => simp [hp] at resolved
      | ok parts =>
        rw [definitionParts_add index position fuel extra token row [] parts hp]
        simpa only [hp] using resolved
#print axioms typeDefNamed_of_le

/-- What a `TypeRef` names before any platform lookup: for a scope that names a carried slice,
    the `TypeDef` the slice's definition link reaches, whose name must be the one the reference
    spells; for any other scope, the scope, name and name parts of a type no carried slice
    defines. -/
def typeRefTarget (env : MetadataEnv) (position : Nat) :
    Nat -> Nat -> Except MetadataError ReferenceTarget
  | 0, token => .error (.unresolvedType token)
  | fuel + 1, token => do
    referenceTarget env position token (fun linked => typeDefNamed env linked fuel)

/-- The named type of a `TypeRef` (`typeRefTarget`); a type no carried slice defines is external
    (`MetadataEnv.externalNamed`). -/
def typeRefNamed (env : MetadataEnv) (position fuel token : Nat) (hint : Option Bool) :
    Except MetadataError NamedType := do
  match <- typeRefTarget env position fuel token with
  | .inl named => .ok named
  | .inr (scope, name, parts) => env.externalNamed token scope name parts hint

/-- The named type of a `TypeDef` or `TypeRef` token read with a value-or-class byte. -/
def namedOf (env : MetadataEnv) (position token : Nat) (hint : Option Bool) :
    Except MetadataError NamedType :=
  signatureHead env position (fun linked => typeDefNamed env linked resolveFuel) token hint

/-- Resolve a closed argument's head and check the arity of a carried definition. -/
def ArgumentHead.resolve (env : MetadataEnv) (method arity : Nat) :
    ArgumentHead → Except MetadataError NamedType
  | .definition scope token => do
    if !env.exactPins.contains scope.spelling then throw (.missingSlice token)
    let some position ← env.referencePosition scope token | throw (.missingSlice token)
    let named ← typeDefNamed env position resolveFuel token
    env.requireArity position token named arity
    return named
  | .platform scope parts => do
    if env.identities.contains scope.spelling then throw (.unresolvedType method)
    let some name := partsName parts | throw (.unresolvedType method)
    let named <- env.externalNamed method scope name parts none
    if named.platformArity != arity then throw (.genericMismatch method)
    return named

mutual

/-- Resolve every named component of a closed argument before comparing its storage or name. -/
def InstanceArgument.resolve (env : MetadataEnv) (method : Nat) :
    Nat → InstanceArgument → Except MetadataError ResolvedType
  | 0, _ => .error (.unresolvedType method)
  | _ + 1, .primitive code => .ok (.primitive code)
  | _ + 1, .named head => .named <$> head.resolve env method 0
  | fuel + 1, .szarray element => .szarray <$> element.resolve env method fuel
  | fuel + 1, .genericInst head arguments => do
    if let .nil := arguments then throw (.genericMismatch method)
    let types <- InstanceArguments.resolve env method fuel arguments
    let named <- head.resolve env method types.length
    return .genericInst named types

/-- Resolve the arguments of a constructed type in declaration order. -/
def InstanceArguments.resolve (env : MetadataEnv) (method : Nat) :
    Nat → InstanceArguments → Except MetadataError ResolvedList
  | _, .nil => .ok .nil
  | 0, _ => .error (.unresolvedType method)
  | fuel + 1, .cons head tail => do
    return .cons (← head.resolve env method fuel) (← tail.resolve env method fuel)

end

/-- Resolve a signature type read in the slice at `position`. -/
def MetadataEnv.resolve (env : MetadataEnv) (position : Nat) (type : SigType) :
    Except MetadataError ResolvedType :=
  resolveType env position (namedOf env position) (resolveFuel + 2) type

/-- The signature of a TypeSpec, including the marker and token of a generic head. -/
def MetadataIndex.typeSpec (index : MetadataIndex) (token : Nat) :
    Except MetadataError SigType := do
  decodeTypeSpec (← index.blob (← index.signatureOf Table.typeSpec token))

/-- The type a `TypeDef`, `TypeRef` or `TypeSpec` token names. -/
def MetadataEnv.resolveToken (env : MetadataEnv) (position token : Nat) :
    Except MetadataError ResolvedType :=
  match metadataTableOf token with
  | 0x02 | 0x01 => do
    let named ← namedOf env position token none
    env.requireArity position token named 0
    .ok (.named named)
  | 0x1B => do
    let index ← env.slice position token
    env.resolve position (← index.typeSpec token)
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

/-- An aggregate identity scopes its head and each argument. A primitive argument uses the
    primitive assembly of the signature that contains it. -/
def aggregateSpelling (corlib : Option (List Nat)) : Nat -> ResolvedType -> Option (List Nat)
  | 0, _ => none
  | _ + 1, .primitive code => do
    let name ← primitiveName code
    some ((<- corlib) ++ [58, 58] ++ name)
  | _ + 1, .named named => some (named.scope ++ [58, 58] ++ named.name)
  | fuel + 1, .genericInst head arguments => do
    let inner <- aggregateSpellings corlib fuel arguments
    some (head.scope ++ [58, 58] ++ head.name ++ [60] ++ inner ++ [62])
  | _ + 1, _ => none

/-- The identities of a chain of types, separated by commas. -/
def aggregateSpellings (corlib : Option (List Nat)) : Nat -> ResolvedList -> Option (List Nat)
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
  /-- A member declaration numbers each owner's variables from zero in its own signature. -/
  rawIndices : Bool := false
  /-- Standalone signature checks have no layout table. Certified bodies always supply it. -/
  layoutDeclarations : Option (Array LayoutIdentity) := none

/-- Each namespace and name in the resolved nesting chain has its own metadata column. -/
def declarationMatches : List TypeLevel → List (List Nat) → Bool
  | [], [] => true
  | level :: rest, space :: name :: parts =>
    MetadataName.ofBytes? space == some level.typeNamespace &&
      MetadataName.ofBytes? name == some level.name && declarationMatches rest parts
  | _, _ => false

mutual

/-- Compare a closed layout argument with the type that the physical signature resolved. -/
private def layoutArgumentMatches : Nat → LayoutArgument → ResolvedType → Bool
  | fuel + 1, claim, resolved =>
    match claim, resolved with
    | .primitive expected, .primitive actual => expected == actual
    | .named scope levels, .named named =>
      bytesOf scope == named.scope && declarationMatches levels named.parts
    | .instanceType scope levels claims, .genericInst head actual =>
      bytesOf scope == head.scope && declarationMatches levels head.parts &&
        layoutArgumentsMatch fuel claims actual
    | _, _ => false
  | 0, _, _ => false

/-- Each supplied argument has to match in order, with both lists ending together. -/
private def layoutArgumentsMatch : Nat → LayoutArguments → ResolvedList → Bool
  | _ + 1, .nil, .nil => true
  | fuel + 1, .cons head tail, .cons actual rest =>
    layoutArgumentMatches fuel head actual && layoutArgumentsMatch fuel tail rest
  | _, _, _ => false

end

/-- The indexed row matches the physical declaration and all arguments of the operand. -/
def Frame.layoutMatches (frame : Frame) (index : Nat) (identity : String) (head : NamedType)
    (arguments : Option ResolvedList) : Bool :=
  match frame.layoutDeclarations with
  | none => true
  | some rows => (rows[index]?).any fun row =>
    row.spelling == identity && declarationMatches row.levels head.parts &&
      match row.arguments, arguments with
      | none, none => true
      | some claims, some actual => layoutArgumentsMatch resolveFuel claims actual
      | _, _ => false

/-- A class, interface or external type that may be a class. -/
def classLike : TypeKind → Bool
  | .classType | .interfaceType | .external (some false) | .external none => true
  | _ => false

/-- A named type an extractor `object` names outside a class field: a class of a carried slice,
    whose instances record their lineage, or `System.String` of the runtime assembly. An
    interface or external class records no lineage a type test or array store could decide. -/
def objectNamed (named : NamedType) : Bool :=
  named.pinned && named.kind == .classType ||
    named.scope == runtimeScopeBytes && named.name == systemStringName &&
      (named.kind == .external (some false) || named.kind == .classType)

/-- Whether a generic definition of this kind is a reference type, when the metadata decides it:
    a class or interface of a carried slice or a reference the signature marks as a class is one,
    a struct, an enum or a reference the signature marks as a value type is not. -/
def TypeKind.reference? : TypeKind → Option Bool
  | .classType | .interfaceType | .external (some false) => some true
  | .valueType | .enumType _ | .external (some true) => some false
  | .external none | .importedOwner => none

/-- A value type, or an external type that may be one. -/
def valueLike : TypeKind → Bool
  | .valueType | .external (some true) | .external none => true
  | _ => false

/-- Whether the resolved definition gives the named type enum storage. -/
def NamedType.isEnum (named : NamedType) : Bool :=
  match named.kind with
  | .enumType _ => true
  | _ => false

mutual

/-- A value argument of a closed aggregate may itself be a closed value instance. -/
private def aggregateValueArgument : Nat -> ResolvedType -> Bool
  | 0, _ => false
  | _ + 1, .primitive code => code != 0x01 && code != 0x0E && code != 0x1C
  | _ + 1, .named named => valueLike named.kind || named.isEnum
  | fuel + 1, .genericInst head arguments =>
    (valueLike head.kind || head.isEnum) && aggregateValueArgs fuel arguments
  | _ + 1, _ => false

/-- Every argument of a preclosed aggregate must have a value kind throughout its type. -/
private def aggregateValueArgs : Nat -> ResolvedList -> Bool
  | 0, _ => false
  | _ + 1, .nil => true
  | fuel + 1, .cons head tail => aggregateValueArgument fuel head && aggregateValueArgs fuel tail

end

/-- Whether a name is that of a primitive type to which `typeStorage` gives value storage as an
    atom of the runtime scope, or a floating-point primitive. -/
def valueAtomName (name : List Nat) : Bool :=
  [0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x18, 0x19].any
      fun code =>
    primitiveName code == some name

/-- The longest primitive names are System.Boolean and System.UIntPtr, each fourteen bytes. -/
private def longestPrimitiveName : Nat := 14

/-- A named runtime primitive has fixed storage and cannot use a supplied layout. -/
def NamedType.fixedStorage (named : NamedType) : Bool :=
  (named.name.drop longestPrimitiveName).isEmpty && named.scope == runtimeScopeBytes &&
    (named.name == systemStringName || named.name == systemObjectName || valueAtomName named.name)

/-- Whether an atom spells one of the 14 primitives in the runtime scope. Resolution refuses
    every such atom: `.primitive` is the only form of a runtime primitive, and the spelling
    cannot tell `System`.`Int32` from an empty-namespace type named `System.Int32`. -/
def runtimePrimitiveAtom (scope name : List Nat) : Bool :=
  (name.drop longestPrimitiveName).isEmpty && valueAtomName name && scope == runtimeScopeBytes

/-- The namespace and simple-name columns of a runtime primitive: `System` and `Int32` for
    `Int32`. -/
def primitiveParts (type : PrimitiveType) : List (List Nat) :=
  [systemNamespace, ((primitiveName type.elementType).getD []).drop systemPrefix.length]

mutual

/-- Whether the extractor's `TypeExpr` names the resolved type. The scope, the name and the kind
    facts come from the metadata; the constructor is the extractor's choice among those the kind
    allows. `fuel` bounds the nesting. -/
def typeAdmits (frame : Frame) : Nat → ResolvedType → TypeExpr → Bool
  | 0, _, _ => false
  | fuel + 1, type, expr =>
    match type, expr with
    | .primitive code, .void => code == 0x01
    | .primitive code, .primitive type =>
      frame.corlib == some runtimeScopeBytes && type.elementType == code
    | .primitive code, .atom scope name =>
      code != 0x01 && frame.corlib == some (bytesOf scope) &&
        primitiveName code == some (bytesOf name) &&
        !runtimePrimitiveAtom (bytesOf scope) (bytesOf name)
    | .primitive 0x0E, .object scope name =>
      frame.corlib == some (bytesOf scope) && name.levels == [⟨name!"System", name!"String"⟩]
    -- A runtime primitive is selected by its namespace and simple-name columns.
    | .named named, .primitive type =>
      named.scope == runtimeScopeBytes && named.parts == primitiveParts type && !named.isEnum &&
        named.kind.reference? == some false
    -- `System.String` and `System.Object` keep their atoms only as references.
    | .named named, .atom scope name =>
      named.scope == bytesOf scope && named.name == bytesOf name && !named.isEnum &&
        named.kind != .importedOwner &&
        (!named.fixedStorage || named.kind.reference? == some true &&
          (named.name == systemStringName || named.name == systemObjectName)) &&
        !runtimePrimitiveAtom (bytesOf scope) (bytesOf name)
    | .named named, .object scope name =>
      named.scope == bytesOf scope && declarationMatches name.levels named.parts &&
        objectNamed named &&
        (!named.fixedStorage || named.name == systemStringName)
    | .named named, .aggregate identity index =>
      bytesOf identity == named.scope ++ [58, 58] ++ named.name && valueLike named.kind &&
        !named.fixedStorage && frame.layoutMatches index identity named none
    | .named named, .enum identity storage =>
      (named.assembly.any (·.matches identity.assembly) &&
        declarationMatches identity.levels named.parts) &&
        match named.kind with
        | .enumType code =>
          (named.pinned || partsName named.parts == some named.name) && !named.fixedStorage &&
            integerElement code && storage.primitive.elementType == code
        | _ => false
    | .var index, .ownerParameter number =>
      frame.rawIndices && index < frame.ownerArity && number == index
    | .var index, .parameter number =>
      !frame.rawIndices && index < frame.ownerArity && number == frame.arity + index
    -- Past the arity, a method parameter's index would be an owner parameter's.
    | .mvar index, .parameter number => index < frame.arity && number == index
    | .byref element, .byref inner => typeAdmits frame fuel element inner
    | .pointer element, .pointer inner => typeAdmits frame fuel element inner
    | .szarray element, .array inner => typeAdmits frame fuel element inner
    | .genericInst head arguments, .aggregate identity index =>
      frame.layoutMatches index identity head (some arguments) && valueLike head.kind &&
        aggregateValueArgs fuel arguments &&
        (if head.pinned || (head.parts == [systemNamespace, valueTuplePairName] &&
            head.scope == bytesOf runtimeScope) ||
            arguments.toList.any (fun | .primitive _ => false | _ => true) then
          match frame.corlib with
          | some corlib => aggregateSpelling (some corlib) fuel (.genericInst head arguments)
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
    | .modified required modifier element, .modified claimed scope name inner =>
      frame.rawIndices && required == claimed && modifier.scope == bytesOf scope &&
        modifier.name == bytesOf name && typeAdmits frame fuel element inner
    | .modified required modifier element, .atom scope name =>
      !frame.rawIndices && bytesOf scope == frame.anchor &&
        cecilName false fuel (.modified required modifier element) == some (bytesOf name) &&
        !runtimePrimitiveAtom (bytesOf scope) (bytesOf name)
    | _, _ => false

/-- A generic instance binds the constructor's scope, name and value or reference kind. -/
def appliedAdmits (frame : Frame) : Nat → NamedType → ResolvedList → TypeExpr → Bool
  | 0, _, _, _ => false
  | fuel + 1, head, arguments, expr =>
    argumentsAdmit frame fuel arguments (fun
      | .constructor scope name =>
        head.kind.reference? == some false && bytesOf scope == head.scope &&
          declarationMatches name.levels head.parts
      | .objectConstructor scope name =>
        head.kind.reference? == some true && bytesOf scope == head.scope &&
          declarationMatches name.levels head.parts
      | _ => false) expr

/-- The last decoded argument matches the outermost application. Each match consumes one
    constructor, stopping on the first mismatch and preserving the fuel of each decoded type. -/
def argumentsAdmit (frame : Frame) : Nat → ResolvedList → (TypeExpr → Bool) → TypeExpr → Bool
  | 0, _, _, _ => false
  | _ + 1, .nil, prefixMatches, expr => prefixMatches expr
  | fuel + 1, .cons argument rest, prefixMatches, expr =>
    argumentsAdmit frame fuel rest (fun
      | .apply constructor last => typeAdmits frame fuel argument last && prefixMatches constructor
      | _ => false) expr

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

/-- A method parameter can carry a root object reference when its signature spells
    ELEMENT_TYPE_OBJECT in the frame's core library. -/
def Frame.admitsParameter (frame : Frame) (type : ResolvedType) (expr : TypeExpr) : Bool :=
  match type, expr with
  | .primitive 0x1C, .object scope name =>
    frame.corlib == some (bytesOf scope) && name.levels == [⟨name!"System", name!"Object"⟩]
  | _, _ => frame.admits type expr

/-- Whether the extractor's type names the type a class instance field holds: as `admits` does,
    or as an object for any class or interface, since the slot keeps a reference never read
    through. -/
def Frame.admitsHeld (frame : Frame) (type : ResolvedType) (expr : TypeExpr) : Bool :=
  frame.admitsParameter type expr ||
    match type, expr with
    | .named named, .object scope name =>
      named.scope == bytesOf scope && declarationMatches name.levels named.parts &&
        classLike named.kind &&
        (!named.fixedStorage || (named.kind.reference? == some true &&
          (named.name == systemStringName || named.name == systemObjectName)))
    | _, _ => false

/-- An application chain never admits an atom, since each prefix test admits only an application
    or a generic definition. -/
private theorem argumentsAdmit_atom {frame : Frame} {scope name : String} :
    ∀ (fuel : Nat) (arguments : ResolvedList) (prefixMatches : TypeExpr → Bool),
      prefixMatches (.atom scope name) = false →
      argumentsAdmit frame fuel arguments prefixMatches (.atom scope name) = false
  | 0, _, _, _ => by simp [argumentsAdmit]
  | _ + 1, .nil, _, refused => by simpa [argumentsAdmit] using refused
  | fuel + 1, .cons _ rest, _, _ => by
    simp only [argumentsAdmit]
    exact argumentsAdmit_atom fuel rest _ rfl
#print axioms argumentsAdmit_atom

/-- Resolution refuses an atom that spells a runtime primitive, whatever the resolved type, the
    frame and the nesting bound. -/
theorem typeAdmits_runtimePrimitiveAtom {frame : Frame} {fuel : Nat} {type : ResolvedType}
    {scope name : String} (spelled : runtimePrimitiveAtom (bytesOf scope) (bytesOf name) = true) :
    typeAdmits frame fuel type (.atom scope name) = false := by
  cases fuel with
  | zero => simp [typeAdmits]
  | succ fuel =>
    cases type with
    | genericInst head arguments =>
      cases fuel with
      | zero => simp [typeAdmits, appliedAdmits]
      | succ fuel =>
        simp only [typeAdmits, appliedAdmits]
        exact argumentsAdmit_atom _ _ _ rfl
    | _ => simp [typeAdmits, spelled]
#print axioms typeAdmits_runtimePrimitiveAtom

/-- Every admitted enum parameter has the assembly columns of its resolved definition or reference. -/
theorem typeAdmits_enum_assembly {frame : Frame} {fuel : Nat} {named : NamedType}
    {identity : TypeIdentity} {storage : EnumStorage}
    (admitted : typeAdmits frame (fuel + 1) (.named named) (.enum identity storage) = true) :
    ∃ columns, named.assembly = some columns ∧ columns.matches identity.assembly = true := by
  cases row : named.assembly with
  | none => simp [typeAdmits, row] at admitted
  | some columns =>
    simp only [typeAdmits, row, Option.any, Bool.and_eq_true] at admitted
    exact ⟨columns, rfl, admitted.1.1⟩
#print axioms typeAdmits_enum_assembly

/-- An admitted platform enum has the name and integer storage of its scoped definition. -/
theorem typeAdmits_external_enum {env : MetadataEnv} {token : Nat} {scope : AssemblyColumns}
    {name : List Nat}
    {parts : List (List Nat)} {hint : Option Bool} {frame : Frame} {fuel : Nat}
    {named : NamedType} {identity : TypeIdentity} {storage : EnumStorage}
    (resolved : env.externalNamed token scope name parts hint = .ok named)
    (admitted : typeAdmits frame (fuel + 1) (.named named) (.enum identity storage) = true) :
    partsName named.parts = some named.name ∧
      Exists fun code => Membership.mem env.platform.definitions
        { scope := named.scope, parts := named.parts, kind := .enumType code named.platformArity }
        /\ integerElement code = true /\
        storage.primitive.elementType = code := by
  cases env.externalNamed_ok resolved with
  | intro kind facts =>
    have known := facts.2.2.1
    have outside := facts.2.2.2.2
    have arity := facts.2.2.2.1
    cases kind <;> simp [typeAdmits, known, PlatformKind.resolvedKind, outside] at admitted
    rename_i code count
    refine And.intro admitted.2.1.1.1 (Exists.intro code (And.intro ?_ ?_))
    . simpa only [arity, PlatformKind.arity] using facts.1
    . exact And.intro admitted.2.1.2 admitted.2.2

#print axioms typeAdmits_external_enum

end CIL.Extraction
