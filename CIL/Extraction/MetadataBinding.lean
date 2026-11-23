import CIL.Extraction.MetadataResolution
import CIL.Extraction.Assemblies
import CIL.Extraction.MetadataContractIdentity

/-!
# Binding token operands and method definitions to metadata

Each token of a method body names a type, a field, a method, a signature or a string. The
extractor states what each means as a `RawOperand`; `checkEntry` recomputes everything the
bytes decide: the scope and full name of every type, the value or class kind of types the
carried slices define, field indices and static flags, the arguments of generic instances and
method specifications, the definition a member reference resolves to, the owner and name an
external call target spells, and the text of a string. The extractor's constructor choice
(`atom`, `object`, `aggregate`) is accepted when it names the same scoped type with a form the
kind allows. `checkLocals` does the same for local variable types and `methodIdentityValid`
for the method definition itself.

Not checked, as `docs/SOUNDNESS-EVIDENCE.md` states: that the carried rows are the image's,
definitions in platform assemblies, imported implementation definitions and public key tokens.
-/

namespace CIL.Extraction

/-- What a token says that depends on the instruction using it: whether a `Field` row is
    static, when the row is carried. -/
structure TokenFacts where
  staticField : Option Bool := none
  deriving DecidableEq, Repr

/-- The frame of the primitive assembly and the method and owner generic arities a method's
    types are read in. -/
def MetadataEnv.frame (env : MetadataEnv) (arity ownerArity : Nat) :
    Except MetadataError Frame := do
  let index ← env.slice 0 0
  let corlib ← index.corlibIdentity
  .ok { corlib, anchor := corlib.getD [], arity, ownerArity }

/-- The type of a signature blob read in the slice at `position`. -/
def MetadataEnv.resolveBlob (env : MetadataEnv) (position token blobOffset : Nat) :
    Except MetadataError ResolvedType := do
  let index ← env.slice position token
  env.resolve position (← decodeFieldSig (← index.blob blobOffset))

/-- Resolve each signature type of a list. -/
def MetadataEnv.resolveAll (env : MetadataEnv) (position : Nat) :
    List SigType → Except MetadataError (List ResolvedType)
  | [] => .ok []
  | type :: rest => do
    let first ← env.resolve position type
    .ok (first :: (← env.resolveAll position rest))

/-! ## Where a member is declared -/

/-- The `TypeDef` that declares a `Field` or `MethodDef` token, from the slice's link, with the
    check that the token lies in the type's range of members. -/
def MetadataEnv.declaringType (env : MetadataEnv) (position token : Nat) :
    Except MetadataError Nat := do
  let index ← env.slice position token
  let some (linked, owner) := index.link linkDeclaring token
    | throw (.unresolvedMember token)
  if linked != position then throw (.unresolvedMember token)
  let row ← index.typeDef owner
  let table := metadataTableOf token
  let (start, stop) ←
    if table == Table.field then do .ok (row.fieldList, ← index.fieldEnd owner row)
    else do
      let end_ ←
        if tokenRow owner == index.header.rows Table.typeDef then
          pure (index.header.rows Table.methodDef + 1)
        else do
          let next ← checkedTokenOf Table.typeDef (tokenRow owner + 1) .rowOverflow
          .ok (← index.typeDef next).methodList
      .ok (row.methodList, end_)
  if tokenRow token < start || stop ≤ tokenRow token then throw (.unresolvedMember token)
  .ok owner

/-- The type a definition token's owner names, with its generic parameters left open. -/
def MetadataEnv.ownerOf (env : MetadataEnv) (position token : Nat) :
    Except MetadataError NamedType := do
  typeDefNamed env position resolveFuel (← env.declaringType position token)

/-- The type a `Field` or `MethodDef` token used as an operand is declared on, which takes no
    generic arguments: the token names no instance to supply them. -/
def MetadataEnv.plainOwnerOf (env : MetadataEnv) (token : Nat) :
    Except MetadataError NamedType := do
  let declaring ← env.declaringType 0 token
  let owner ← typeDefNamed env 0 resolveFuel declaring
  env.requireArity 0 declaring owner 0
  .ok owner

/-- The type a resolved owner names: its head, with generic arguments aside. -/
def ResolvedType.head : ResolvedType → Option NamedType
  | .named type => some type
  | .genericInst head _ => some head
  | _ => none

/-- The generic arguments of a resolved owner. -/
def ResolvedType.arguments : ResolvedType → Option (List ResolvedType)
  | .genericInst _ arguments => some arguments.toList
  | _ => none

/-! ## Strings -/

/-- Whether the user string of a token has the code units of the claimed text. -/
def userStringMatches (index : MetadataIndex) (token : Nat) (text : String) :
    Except MetadataError Bool := do
  let units ← index.userString (tokenRow token)
  let bytes := bytesOf text
  .ok (utf16Units bytes.length bytes == some units)

/-! ## Types -/

/-- Check a `.type` operand: the token's type is the one the extractor spells. -/
def checkTypeOperand (env : MetadataEnv) (frame : Frame) (token : Nat) (expr : TypeExpr) :
    Except MetadataError TokenFacts := do
  let resolved ← env.resolveToken 0 token
  if frame.admits resolved expr then .ok {} else .error (.operandMismatch token)

/-! ## Fields -/

/-- A field token read from the slice: its declaring type as the operand names it, its name,
    its declared type, and the definition when a carried slice defines it. -/
structure FieldSite where
  owner : ResolvedType
  name : List Nat
  declared : ResolvedType
  definition : Option (Nat × Nat)
  /-- The head token of a generic owner marked VALUETYPE in the field reference's slice. -/
  valueHead : Option Nat := none

/-- Where a field's `Field` row lives, with the checks that tie a `MemberRef` to it: the
    definition lies in the declaring type's range and has the member's name and signature. -/
def MetadataEnv.fieldDefinition (env : MetadataEnv) (token : Nat) (owner : NamedType)
    (name : List Nat) (declared : ResolvedType) : Except MetadataError (Option (Nat × Nat)) := do
  if !owner.pinned then return none
  let own ← env.slice 0 token
  let some (position, definition) := own.link linkDefinition token
    | throw (.unresolvedMember token)
  let index ← env.slice position token
  let row ← index.field definition
  let declaring ← env.ownerOf position definition
  if declaring.scope != owner.scope || declaring.parts != owner.parts then
    throw (.unresolvedMember token)
  let found ← env.resolveBlob position definition row.signature
  if (← index.string row.name) != name || found != declared then throw (.unresolvedMember token)
  .ok (some (position, definition))

/-- Read a `Field` or `MemberRef` token as a field. -/
def MetadataEnv.fieldSite (env : MetadataEnv) (token : Nat) : Except MetadataError FieldSite := do
  let index ← env.slice 0 token
  if metadataTableOf token == Table.field then
    let row ← index.field token
    .ok { owner := .named (← env.plainOwnerOf token), name := ← index.string row.name,
          declared := ← env.resolveBlob 0 token row.signature, definition := some (0, token) }
  else
    let row ← index.memberRef token
    let (owner, valueHead) ← if metadataTableOf row.parent == Table.typeSpec then do
      let signature ← index.typeSpec row.parent
      let head := match signature with
        | .genericInst true token _ => some token
        | _ => none
      pure (← env.resolve 0 signature, head)
    else pure (← env.resolveToken 0 row.parent, none)
    let name ← index.string row.name
    let declared ← env.resolveBlob 0 token row.signature
    let definition ← match owner.head with
      | some head => env.fieldDefinition token head name declared
      | none => .error (.unresolvedMember token)
    .ok { owner, name, declared, definition, valueHead }

/-- The end of a class chain at a base no carried slice defines: `System.Object`, named through
    a reference to an assembly of a core-library name, whose platform definition states that it
    is the root class. One lookup reads the definition, refusing as `MetadataEnv.externalNamed`
    refuses a class before the name and the root kind are checked. -/
def MetadataEnv.chainRoot (env : MetadataEnv) (token base : Nat) (scope : List Nat)
    (parts : List (List Nat)) (core : Bool) : Except MetadataError (List (Nat × Nat)) := do
  if env.pinned.matches scope then throw (.missingSlice base)
  let kind ← env.platform.require base scope parts (PlatformKind.fitsHint (some false))
  if !(core && parts == [systemNamespace, objectName]) then throw (.unsupportedBase token)
  if kind == .objectRoot then .ok [] else .error (.platformKindMismatch base)

/-- A class chain ends outside the carried slices only at a type whose platform definition is
    the root class `System.Object`. -/
theorem MetadataEnv.chainRoot_ok {env : MetadataEnv} {token base : Nat} {scope : List Nat}
    {parts : List (List Nat)} {core : Bool} {chain : List (Nat × Nat)}
    (ended : env.chainRoot token base scope parts core = .ok chain) :
    { scope, parts, kind := .objectRoot } ∈ env.platform.definitions ∧
      parts = [systemNamespace, objectName] ∧ core = true := by
  unfold MetadataEnv.chainRoot at ended
  by_cases pinned : env.pinned.matches scope = true
  · simp [pinned, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ended
  cases required : env.platform.require base scope parts (PlatformKind.fitsHint (some false)) with
  | error error => simp [pinned, required, bind, Except.bind] at ended
  | ok kind =>
    have member := (PlatformTable.require_ok required).1
    by_cases named : (core && parts == [systemNamespace, objectName]) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at named
      by_cases root : kind = .objectRoot
      · cases root
        exact ⟨member, named.2, named.1⟩
      · simp only [pinned, required, bind, Except.bind] at ended
        simp [named, root] at ended
    · simp [pinned, required, named, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
        at ended

#print axioms MetadataEnv.chainRoot_ok

/-- A carried root has the public, nongeneric, fieldless System.Object definition in CoreLib. -/
def MetadataEnv.carriedObjectRoot (env : MetadataEnv) (index : MetadataIndex)
    (position token : Nat) (row : TypeDefRow) : Except MetadataError Bool := do
  unless index.identity == bytesOf coreLibraryScope &&
      row.flags &&& 0x27 == 1 && index.instanceTotal.find? token == some 0 do return false
  let namespaceBytes ← index.string row.namespace_
  let name ← index.string row.name
  return namespaceBytes == systemNamespace && name == objectName &&
    (← env.definitionArity position token) == 0

/-- The base classes of a class definition, nearest first, as slice positions and `TypeDef`
    tokens. Traversal includes each base except System.Object. -/
def MetadataEnv.classChain (env : MetadataEnv) (fuel position token : Nat)
    (includeOwner : Bool := false) : Except MetadataError (List (Nat × Nat)) :=
  match fuel with
  | 0 => .error (.unsupportedBase token)
  | fuel + 1 => do
    let index ← env.slice position token
    let row ← index.typeDef token
    let lineage (bases : List (Nat × Nat)) :=
      if includeOwner then (position, token) :: bases else bases
    match metadataTableOf row.extends_ with
    | 0x02 =>
      if tokenRow row.extends_ == 0 then
        if ← env.carriedObjectRoot index position token row then pure []
        else throw (.unsupportedBase token)
      else if (← env.definitionArity position row.extends_) != 0 then
        .error (.unsupportedBase token)
      else lineage <$> env.classChain fuel position row.extends_ true
    | 0x01 =>
      match ← typeRefTarget env position resolveFuel row.extends_ with
      | .inl _ =>
        let some (linked, definition) := index.link linkDefinition row.extends_
          | throw (.unsupportedBase token)
        if (← env.definitionArity position row.extends_) != 0 then throw (.unsupportedBase token)
        lineage <$> env.classChain fuel linked definition true
      | .inr (scope, _, parts) =>
        lineage <$> env.chainRoot token row.extends_ scope parts
          (← index.coreLibraryReference row.extends_)
    | _ => .error (.unsupportedBase token)

/-- The number of instance fields of the types of a chain. -/
def MetadataEnv.chainFieldCount (env : MetadataEnv) : List (Nat × Nat) → Except MetadataError Nat
  | [] => .ok 0
  | (position, token) :: rest => do
    let index ← env.slice position token
    let some own := index.instanceTotal.find? token | throw (.missingRow token)
    .ok (own + (← env.chainFieldCount rest))

/-- The model index of an instance field: counting the fields of the bases of a class first,
    then the instance fields of the owner before the field. -/
def MetadataEnv.instanceIndex (env : MetadataEnv) (position field : Nat) (classOwner : Bool) :
    Except MetadataError Nat := do
  let index ← env.slice position field
  let some before := index.instanceBefore.find? field | throw (.unresolvedMember field)
  if classOwner then
    let owner ← env.declaringType position field
    let inherited ← env.chainFieldCount (← env.classChain resolveFuel position owner)
    .ok (inherited + before)
  else .ok before

/-- Storage width of a primitive field signature on the supported 64-bit profiles. -/
private def primitiveWidth : Nat → Option Nat
  | 0x02 | 0x04 | 0x05 => some 1
  | 0x03 | 0x06 | 0x07 => some 2
  | 0x08 | 0x09 => some 4
  | 0x0A | 0x0B | 0x18 | 0x19 => some 8
  | _ => none

/-- The `platform` constant field, the one static field of an owner no carried slice defines
    that a body may name: its index is 0, and its owner's platform definition must state the byte
    order. -/
def MetadataEnv.platformConstant (env : MetadataEnv) (token : Nat) (site : FieldSite)
    (held : ResolvedType) (isStatic platform : Bool) :
    Except MetadataError (Nat × ResolvedType × Option Bool) :=
  if !isStatic then .error (.unboundInstanceField token)
  else if !platform then .error (.unboundStaticField token)
  else match site.owner.head with
    | none => .error (.unboundStaticField token)
    | some head =>
      (fun _ => (0, held, none)) <$>
        env.platform.require token head.scope head.parts (· == .byteOrder)

/-- The constant field's owner has a platform definition that states the byte order. -/
theorem MetadataEnv.platformConstant_ok {env : MetadataEnv} {token : Nat} {site : FieldSite}
    {held : ResolvedType} {isStatic platform : Bool} {result : Nat × ResolvedType × Option Bool}
    (found : env.platformConstant token site held isStatic platform = .ok result) :
    result = (0, held, none) ∧ ∃ head, site.owner.head = some head ∧
      { scope := head.scope, parts := head.parts, kind := .byteOrder } ∈
        env.platform.definitions := by
  unfold MetadataEnv.platformConstant at found
  split at found
  · cases found
  · split at found
    · cases found
    · split at found
      · cases found
      · rename_i head owned
        cases required : env.platform.require token head.scope head.parts (· == .byteOrder) with
        | error error => simp [required, Functor.map, Except.map] at found
        | ok kind =>
          simp only [required, Functor.map, Except.map, Except.ok.injEq] at found
          have ⟨member, fits⟩ := PlatformTable.require_ok required
          simp only [beq_iff_eq] at fits
          cases fits
          exact ⟨found.symm, head, owned, member⟩

#print axioms MetadataEnv.platformConstant_ok

/-- The index and held type of a field whose owner no carried slice defines: an item of the
    platform pair, whose owner's platform definition must state the pair, read as an instance
    field, or the `platform` constant field (`MetadataEnv.platformConstant`). -/
def MetadataEnv.platformField (env : MetadataEnv) (token : Nat) (site : FieldSite)
    (held : ResolvedType) (isStatic platform : Bool) :
    Except MetadataError (Nat × ResolvedType × Option Bool) :=
  -- The pair is known by its own reference, never by the slice's `corlib` number.
  match site.owner with
  | .genericInst head arguments =>
    match arguments.toList with
    | [first, second] =>
      if isCorlibScope head.scope && head.parts == [systemNamespace, valueTuplePairName] then
        match env.platform.require token head.scope head.parts (· == .valuePair) with
        | .error error => .error error
        | .ok _ =>
          if site.name == firstItemName && site.declared == .var 0 then .ok (0, first, some false)
          else if site.name == secondItemName && site.declared == .var 1 then
            .ok (1, second, some false)
          else if site.name == firstItemName || site.name == secondItemName then
            .error (.operandMismatch token)
          else .error (.unboundInstanceField token)
      else env.platformConstant token site held isStatic platform
    | _ => env.platformConstant token site held isStatic platform
  | _ => env.platformConstant token site held isStatic platform

/-- A platform pair field reads the argument selected by both its name and declared signature. -/
theorem MetadataEnv.platformField_pair {env : MetadataEnv} {token : Nat} {site : FieldSite}
    {held type : ResolvedType} {isStatic platform : Bool} {index : Nat}
    (found : env.platformField token site held isStatic platform = .ok (index, type, some false)) :
    ∃ head arguments, site.owner = .genericInst head arguments ∧
      { scope := head.scope, parts := head.parts, kind := .valuePair } ∈
        env.platform.definitions ∧ site.declared = .var index ∧
      arguments.toList[index]? = some type ∧
      ((index = 0 ∧ site.name = firstItemName) ∨ (index = 1 ∧ site.name = secondItemName)) := by
  unfold MetadataEnv.platformField at found
  split at found
  · rename_i head arguments owner
    split at found
    · split at found
      · split at found
        · cases found
        · rename_i required
          have ⟨member, fits⟩ := PlatformTable.require_ok required
          simp only [beq_iff_eq] at fits
          cases fits
          refine ⟨head, arguments, owner, member, ?_⟩
          split at found
          · rename_i selected
            simp only [Bool.and_eq_true, beq_iff_eq] at selected
            cases found
            simp_all
          · split at found
            · rename_i selected
              simp only [Bool.and_eq_true, beq_iff_eq] at selected
              cases found
              simp_all
            · split at found <;> cases found
      · cases (MetadataEnv.platformConstant_ok found).1
    · cases (MetadataEnv.platformConstant_ok found).1
  · cases (MetadataEnv.platformConstant_ok found).1

#print axioms MetadataEnv.platformField_pair

/-- The index a field operand must carry, and the type it must hold. A field signature's `!n`
    names the declaring type's parameter, so the held type reads it as the declaring instance's
    argument, which may itself be a parameter of the reading method or its owner. No carried
    row gives a field of an owner no carried slice defines, so such a field is refused except
    as an item of the platform pair, read as an instance field whose reference declares it as
    the pair's own parameter (`!0` for `Item1`, `!1` for `Item2`), and as the `platform`
    constant field; any other member of the pair is refused too. -/
def MetadataEnv.expectedField (env : MetadataEnv) (token : Nat) (site : FieldSite)
    (classOwner isStatic platform : Bool) :
    Except MetadataError (Nat × ResolvedType × Option Bool) := do
  let some held := substituteResolved none site.owner.arguments resolveFuel site.declared
    | throw (.operandMismatch token)
  match site.definition with
  | some (position, definition) =>
    let index ← env.slice position definition
    let row ← index.field definition
    let declaredStatic := row.flags / 0x10 % 2 == 1
    if declaredStatic then
      let owner ← env.declaringType position definition
      let (start, _) ← index.fieldRange owner
      .ok (tokenRow definition - start, held, some true)
    else .ok (← env.instanceIndex position definition classOwner, held, some false)
  | none =>
    -- The pair is known by its own reference, never by the slice's `corlib` number.
    let pair ← match site.owner, site.valueHead with
      | .genericInst head (.cons (.primitive first) (.cons (.primitive second) .nil)),
          some reference => do
        if metadataTableOf reference != Table.typeRef ||
            head.parts != [systemNamespace, valueTuplePairName] ||
            !(primitiveWidth first).any (fun width => primitiveWidth second == some width) then
          pure false
        else
          let index ← env.slice 0 token
          let scope := (← index.typeRef reference).scope
          if metadataTableOf scope == Table.assemblyRef then
            pure ((← index.assemblyRefName scope runtimeAssembly) == some runtimeAssembly)
          else pure false
      | _, _ => pure false
    if pair || (isStatic && platform) then env.platformField token site held isStatic platform
    else if isStatic then throw (.unboundStaticField token)
    else throw (.unboundInstanceField token)

/-- Check a `.field` operand: the owner, the field's model index, the type it holds and the
    name, which must spell the name of the row the token names. -/
def checkFieldOperand (env : MetadataEnv) (frame : Frame) (token : Nat) (owner : TypeExpr)
    (index : Nat) (fieldType : TypeExpr) (name : MetadataName) (isStatic : Bool) :
    Except MetadataError TokenFacts := do
  if metadataTableOf token != Table.field && metadataTableOf token != Table.memberRef then
    throw (.unsupportedTable token)
  let site ← env.fieldSite token
  if !name.spells site.name then throw (.operandMismatch token)
  if isStatic && site.owner.arguments.isSome then throw (.instantiatedStaticField token)
  let classOwner := match owner with
    | .object .. => true
    | _ => false
  let platform := isStatic && ({ owner, index, type := fieldType, name } : FieldRef) ==
    littleEndianField
  let (expected, held, isStaticFact) ← env.expectedField token site classOwner isStatic platform
  if isStaticFact.any (· != isStatic) then throw (.operandMismatch token)
  if index != expected then throw (.fieldIndexMismatch token index expected)
  if !(frame.admits site.owner owner) then throw (.operandMismatch token)
  let heldAdmitted := if classOwner && !isStatic then frame.admitsHeld held fieldType
    else frame.admits held fieldType
  if !heldAdmitted then throw (.operandMismatch token)
  .ok { staticField := isStaticFact }

/-! ## Methods and calls -/

/-- A method token read from the slice: its declaring type as the operand names it, its name,
    its signature resolved, the definition when a carried slice defines it and the method
    arguments of a specification. -/
structure MethodSite where
  owner : ResolvedType
  name : List Nat
  convention : Nat
  genericArity : Nat
  result : ResolvedType
  parameters : List ResolvedType
  definition : Option (Nat × Nat)
  methodArguments : Option (List ResolvedType)

/-- The convention, generic arity, result and parameters of a method blob, resolved in the
    slice at `position`. -/
def MetadataEnv.resolveMethod (env : MetadataEnv) (position : Nat) (blob : List Nat) :
    Except MetadataError (Nat × Nat × ResolvedType × List ResolvedType) := do
  let signature ← decodeMethodSig blob
  let result ← env.resolve position signature.result
  .ok (signature.convention, signature.genericArity, result,
    ← env.resolveAll position signature.parameters)

/-- The `MethodDef` of a carried slice a `MemberRef` resolves to: it lies in the owner's
    methods and has the member's name, convention, arity and resolved signature. -/
def MetadataEnv.methodDefinition (env : MetadataEnv) (token : Nat) (owner : NamedType)
    (name : List Nat) (signature : Nat × Nat × ResolvedType × List ResolvedType) :
    Except MetadataError (Option (Nat × Nat)) := do
  if !owner.pinned then return none
  let own ← env.slice 0 token
  let some (position, definition) := own.link linkDefinition token
    | throw (.unresolvedMember token)
  let index ← env.slice position token
  let row ← index.methodDef definition
  let declaring ← env.ownerOf position definition
  if declaring.scope != owner.scope || declaring.parts != owner.parts then
    throw (.unresolvedMember token)
  let found ← env.resolveMethod position (← index.blob row.signature)
  if (← index.string row.name) != name || found != signature then
    throw (.unresolvedMember token)
  .ok (some (position, definition))

/-- Only a missing external TypeRef at the declaring position can name an opaque owner. -/
private def MetadataEnv.callOwner (env : MetadataEnv) (token : Nat) (linked : Bool) :
    Except MetadataError ResolvedType := do
  if !linked then return <- { env with publishedLayouts := #[] }.resolveToken 0 token
  if metadataTableOf token != Table.typeRef then throw (.unresolvedMember token)
  let (scope, name, parts) <- typeRefQualified env 0 resolveFuel token
  if env.identities.contains scope || env.pinned.matches scope ||
      (env.platform.kindOf scope parts).isSome then throw (.unresolvedMember token)
  return .named { scope, name, parts, kind := .importedOwner, pinned := false }

/-- Read a definition or member reference, resolving an opaque owner only for a linked call. -/
private def MetadataEnv.readMemberSite (env : MetadataEnv) (token : Nat) (linked : Bool) :
    Except MetadataError MethodSite := do
  let index ← env.slice 0 token
  match metadataTableOf token with
  | 0x06 =>
    let row ← index.methodDef token
    let signature ← env.resolveMethod 0 (← index.blob row.signature)
    .ok { owner := .named (← env.plainOwnerOf token), name := ← index.string row.name,
          convention := signature.1, genericArity := signature.2.1, result := signature.2.2.1,
          parameters := signature.2.2.2, definition := some (0, token), methodArguments := none }
  | 0x0A =>
    let row ← index.memberRef token
    let owner <- env.callOwner row.parent linked
    let name ← index.string row.name
    let signature ← env.resolveMethod 0 (← index.blob row.signature)
    let definition ← match owner.head with
      | some head => env.methodDefinition token head name signature
      | none => .error (.unresolvedMember token)
    .ok { owner := owner, name := name, convention := signature.1, genericArity := signature.2.1,
          result := signature.2.2.1, parameters := signature.2.2.2, definition := definition,
          methodArguments := none }
  | _ => .error (.unsupportedTable token)

/-- Read a `MethodDef`, `MemberRef` or `MethodSpec` token as a method; a specification adds the
    method arguments of its instantiation blob. -/
private def MetadataEnv.readMethodSite (env : MetadataEnv) (token : Nat) (linked : Bool) :
    Except MetadataError MethodSite := do
  if metadataTableOf token == Table.methodSpec then
    let index ← env.slice 0 token
    let row ← index.methodSpec token
    let site <- env.readMemberSite row.method linked
    let arguments ← decodeMethodSpec (← index.blob row.instantiation)
    if arguments.isEmpty || arguments.length != site.genericArity then
      throw (.genericMismatch token)
    .ok { site with methodArguments := some (← env.resolveAll 0 arguments) }
  else env.readMemberSite token linked

/-- A method reference with a declaring type resolved from carried or platform metadata. -/
def MetadataEnv.methodSite (env : MetadataEnv) (token : Nat) : Except MetadataError MethodSite :=
  env.readMethodSite token false

/-- Cecil's full name of a method, `result Owner::name(parameters)`, from the full names of its
    parts. -/
def methodFullName (result owner name : List Nat) (parameters : List (List Nat)) : List Nat :=
  result ++ [32] ++ owner ++ [58, 58] ++ name ++ [40] ++ (parameters.intersperse [44]).flatten ++
    [41]

/-- A successful metadata read supplies the value used by the remaining checks. -/
private theorem metadataBind_ok {α β : Type} {read : Except MetadataError α}
    {next : α → Except MetadataError β} {result : β} :
    (read >>= next) = .ok result ↔ ∃ value, read = .ok value ∧ next value = .ok result := by
  cases read <;> simp [Bind.bind, Except.bind]

#print axioms metadataBind_ok

/-- A resolved declaring TypeDef takes its scope from the assembly of its physical slice. -/
private theorem definition_scope {env : MetadataEnv} {position fuel token : Nat} {owner : NamedType}
    (found : typeDefNamed env position fuel token = .ok owner) :
    ∃ index, env.slice position token = .ok index ∧ index.identity = owner.scope := by
  unfold typeDefNamed at found
  simp only [metadataBind_ok] at found
  obtain ⟨index, slice, row, _, parts, _, named⟩ := found
  cases names : partsName parts with
  | none => simp [names, throw, throwThe, MonadExceptOf.throw] at named
  | some name =>
    simp only [names, metadataBind_ok] at named
    obtain ⟨kind, _, same⟩ := named
    cases same
    exact ⟨index, slice, rfl⟩

#print axioms definition_scope

/-- The resolved owner's assembly and the MethodDef row selected in that assembly. -/
def ResolvedType.DefinesMethod (owner : ResolvedType) (env : MetadataEnv)
    (position token : Nat) : Prop :=
  ∃ head index row, owner.head = some head ∧ env.slices.find? position = some index ∧
    index.identity = head.scope ∧ index.methodDef token = .ok row

/-- A successful slice lookup returns the entry at that position, independently of the token. -/
private theorem slice_found {env : MetadataEnv} {position token} {index : MetadataIndex}
    (read : env.slice position token = .ok index) : env.slices.find? position = some index := by
  unfold MetadataEnv.slice at read
  split at read <;> simp_all

#print axioms slice_found

/-- A MemberRef definition link resolves to the MethodDef row of the operand owner's assembly. -/
private theorem member_definition {env : MetadataEnv} {operand position token : Nat}
    {owner : NamedType} {name signature}
    (found : env.methodDefinition operand owner name signature = .ok (some (position, token))) :
    ResolvedType.DefinesMethod (.named owner) env position token := by
  unfold MetadataEnv.methodDefinition at found
  split at found
  · simp [pure, Except.pure] at found
  simp only [metadataBind_ok] at found
  obtain ⟨own, _, linked⟩ := found
  split at linked
  next linkedPosition definition link =>
    simp only [metadataBind_ok] at linked
    obtain ⟨index, slice, row, rowRead, declaring, declared, check⟩ := linked
    split at check
    · contradiction
    next agrees =>
      simp only [metadataBind_ok] at check
      obtain ⟨_, _, _, _, _, _, check⟩ := check
      split at check
      · contradiction
      cases check
      unfold MetadataEnv.ownerOf at declared
      obtain ⟨_, _, named⟩ := metadataBind_ok.mp declared
      obtain ⟨ownerIndex, ownerSlice, scopeEq⟩ := definition_scope named
      have lookup := slice_found slice
      have same := (slice_found ownerSlice).symm.trans lookup
      cases Option.some.inj same
      simp only [Bool.or_eq_true, bne_iff_ne, not_or] at agrees
      exact ⟨owner, index, row, rfl, lookup, scopeEq.trans (by simpa using agrees.1), rowRead⟩
  · contradiction

#print axioms member_definition

/-- The owner of a local MethodDef has the scope of the slice containing its row. -/
private theorem plain_owner_scope {env : MetadataEnv} {token : Nat} {owner : NamedType}
    (found : env.plainOwnerOf token = .ok owner) :
    ∃ index, env.slices.find? 0 = some index ∧ index.identity = owner.scope := by
  unfold MetadataEnv.plainOwnerOf at found
  simp only [metadataBind_ok] at found
  obtain ⟨_, _, selected, named, _, _, same⟩ := found
  cases same
  obtain ⟨index, slice, scopeEq⟩ := definition_scope named
  exact ⟨index, slice_found slice, scopeEq⟩

#print axioms plain_owner_scope

/-- Both a direct MethodDef token and a resolved MemberRef identify a physical method row. -/
private theorem member_site_definition {env : MetadataEnv} {operand position token : Nat}
    {site : MethodSite} {linked}
    (found : env.readMemberSite operand linked = .ok site)
    (definition : site.definition = some (position, token)) :
    site.owner.DefinesMethod env position token := by
  unfold MetadataEnv.readMemberSite at found
  obtain ⟨index, slice, found⟩ := metadataBind_ok.mp found
  split at found
  · simp only [metadataBind_ok] at found
    obtain ⟨row, method, _, _, _, _, owner, declared, _, _, same⟩ := found
    cases same
    cases definition
    obtain ⟨ownerIndex, ownerSlice, scopeEq⟩ := plain_owner_scope declared
    have lookup := slice_found slice
    cases Option.some.inj (ownerSlice.symm.trans lookup)
    exact ⟨owner, index, row, rfl, lookup, scopeEq, method⟩
  · simp only [metadataBind_ok] at found
    obtain ⟨_, _, owner, _, _, _, _, _, _, _, tail⟩ := found
    cases head : owner.head with
    | none => simp [head, Bind.bind, Except.bind] at tail
    | some name =>
      simp only [head, metadataBind_ok] at tail
      obtain ⟨location, resolved, same⟩ := tail
      cases same
      change location = some (position, token) at definition
      subst location
      obtain ⟨other, index, row, named, lookup, scopeEq, method⟩ := member_definition resolved
      change some name = some other at named
      cases Option.some.inj named
      exact ⟨name, index, row, head, lookup, scopeEq, method⟩
  · contradiction

#print axioms member_site_definition

/-- Resolving a MethodSpec preserves the defining slice, owner and MethodDef row of its member. -/
theorem MetadataEnv.methodSite_definition {env : MetadataEnv} {operand position token : Nat}
    {site : MethodSite} (found : env.methodSite operand = .ok site)
    (definition : site.definition = some (position, token)) :
    site.owner.DefinesMethod env position token := by
  unfold MetadataEnv.methodSite MetadataEnv.readMethodSite at found
  split at found
  · simp only [metadataBind_ok] at found
    obtain ⟨_, _, _, _, member, read, _, _, _, _, rest⟩ := found
    split at rest
    · contradiction
    obtain ⟨_, _, same⟩ := metadataBind_ok.mp rest
    cases same
    exact member_site_definition (site := member) read definition
  · exact member_site_definition found definition

#print axioms MetadataEnv.methodSite_definition

/-- The identity an external call target spells: the declaring type's scope, then Cecil's full
    name of the method. -/
def MethodSite.externalName (site : MethodSite) : Option (List Nat) := do
  let head ← site.owner.head
  let result ← cecilName false resolveFuel site.result
  let owner ← cecilName false resolveFuel site.owner
  let parameters ← site.parameters.mapM (cecilName false resolveFuel)
  some (head.scope ++ [58, 58] ++ methodFullName result owner site.name parameters)

/-- The exact open definition fields of a generic imported contract. -/
def MethodSite.contractDefinitionKey (site : MethodSite) (frame : Frame) :
    Option (List Nat) := do
  let owner ← site.owner.head
  let result ← contractTypeKey frame resolveFuel site.result
  let parameters ← site.parameters.mapM (contractTypeKey frame resolveFuel)
  let fields := [contractPart owner.scope ++ contractPart owner.name, site.name,
    bytesOf (toString site.genericArity), bytesOf (toString (site.convention % 0x20)),
    bytesOf (if site.convention / hasThisFlag % 2 == 1 then "1" else "0"),
    bytesOf (if site.convention / explicitThisFlag % 2 == 1 then "1" else "0"), result,
    bytesOf (toString parameters.length)] ++ parameters
  pure (bytesOf "contract-definition-v1:" ++ (fields.map contractPart).flatten)

/-- The exact closed contract identity, retaining its open definition and scoped arguments. -/
def MethodSite.contractName (site : MethodSite) (frame : Frame) : Option (List Nat) := do
  let .named owner := site.owner | none
  let some arguments := site.methodArguments | none
  if site.definition.isSome || arguments.isEmpty || arguments.length != site.genericArity ||
      site.convention != 0x10 || frame.corlib != some runtimeScopeBytes ||
      !arguments.all contractInteger then none else do
    let definition ← site.contractDefinitionKey frame
    let keys ← arguments.mapM (contractTypeKey frame resolveFuel)
    let argumentNames ← arguments.mapM (cecilName false resolveFuel)
    let indexedNames := SearchTree.ofSorted
      (argumentNames.zipIdx.map fun (name, index) => (index, name))
    let result ← contractClosedName indexedNames resolveFuel site.result
    let parameters ← site.parameters.mapM (contractClosedName indexedNames resolveFuel)
    let name := site.name ++ [60] ++ (argumentNames.intersperse [44]).flatten ++ [62] ++
      bytesOf "|definition|" ++ contractHex definition ++ bytesOf "|arguments|" ++
      (keys.map contractPart).flatten
    pure (owner.scope ++ [58, 58] ++ methodFullName result owner.name name parameters)

/-- Whether the external target exactly spells its member or its closed generic contract. -/
def MethodSite.externalMatches (site : MethodSite) (frame : Frame) (identity : String) : Bool :=
  site.externalName == some (bytesOf identity) ||
    site.contractName frame == some (bytesOf identity)

/-- A reconstructed generic contract identity passes the exact target comparison. -/
theorem MethodSite.externalMatches_contract (site : MethodSite) (frame : Frame)
    (identity : String) (matched : site.contractName frame = some (bytesOf identity)) :
    site.externalMatches frame identity = true := by
  simp [MethodSite.externalMatches, matched]
#print axioms MethodSite.externalMatches_contract

/-- A static import resolves only under the exact ordinary or closed generic export identity. -/
def MetadataEnv.importMethodSite (env : MetadataEnv) (token : Nat) (frame : Frame)
    (identity : String) : Except MetadataError MethodSite := do
  let site <- env.readMethodSite token true
  let .named owner := site.owner | throw (.unresolvedMember token)
  if owner.kind != .importedOwner || site.definition.isSome then throw (.unresolvedMember token)
  let expected := if site.methodArguments.isSome then site.contractName frame
    else if site.convention == 0 && site.genericArity == 0 then site.externalName else none
  if expected != some (bytesOf identity) then throw (.operandMismatch token)
  return site

/-- The claimed parameter list names every parameter of the member, in order. -/
private def parametersAdmitted (frame : Frame) : List ResolvedType → List TypeExpr → Bool
  | [], [] => true
  | type :: types, claim :: claims =>
    frame.admitsParameter type claim && parametersAdmitted frame types claims
  | _, _ => false

/-- The reference and open declaration describe the same metadata member in its type frame. -/
def checkCallReference (env : MetadataEnv) (frame : Frame) (token : Nat) (site : MethodSite)
    (call : CallSite) : Except MetadataError Unit := do
  if site.genericArity != 0 && site.methodArguments.isNone then throw (.genericMismatch token)
  let extracted := site.definition.isSome
  let ownerArguments := site.owner.arguments
  let ownerList := ownerArguments.getD []
  let head ← match site.owner.head with
    | some head => pure head
    | none => throw (.unresolvedType token)
  if bytesOf call.name != site.name then throw (.operandMismatch token)
  if !call.method.name.spells site.name then throw (.operandMismatch token)
  if call.staticVirtualInterfaceSlot then
    let some (position, definition) := site.definition | throw (.operandMismatch token)
    let index ← env.slice position definition
    let row ← index.methodDef definition
    -- MethodAttributes.Static and Virtual, on a type whose metadata declares an interface.
    if call.hasThis || head.kind != .interfaceType || row.flags &&& 0x50 != 0x50 then
      throw (.operandMismatch token)
  let expected := site.methodArguments.getD [] ++ (if extracted then ownerList else [])
  if call.typeArguments.length != expected.length || !(expected.zip call.typeArguments).all
      (fun (type, claimed) => frame.admits type claimed) then
    throw (.genericMismatch token)
  if call.ownerArgumentCount != (if extracted then ownerList.length else 0) then
    throw (.genericMismatch token)
  if call.method.genericArity != site.genericArity ||
      call.method.methodArguments != siteMethodArguments call then
    throw (.genericMismatch token)
  -- The full flat identity is checked by located.admits below.
  if call.declaringType.headScope.any (bytesOf · != head.scope) then
    throw (.scopeMismatch token)
  let located := { frame with anchor := head.scope }
  if head.kind == .importedOwner then
    let .atom scope name := call.declaringType | throw (.operandMismatch token)
    if bytesOf scope != head.scope || bytesOf name != head.name then throw (.operandMismatch token)
  else if !(located.admits site.owner call.declaringType) then throw (.operandMismatch token)
  let declared := call.declared
  if declared.convention != site.convention ||
      call.hasThis != (declared.convention / hasThisFlag % 2 == 1) ||
      call.parameterCount != site.parameters.length then throw (.operandMismatch token)
  let member := { located with
    arity := site.genericArity, ownerArity := ownerList.length, rawIndices := true }
  if !member.admits site.result declared.returnType ||
      !parametersAdmitted member site.parameters declared.parameters then
    throw (.operandMismatch token)
  -- A nongeneric MethodDef supplies the closed signature in its own module's primitive scope.
  let closed ← match site.definition with
    | some (position, definition) =>
      if position == 0 || site.genericArity != 0 || !ownerList.isEmpty then pure located
      else do
        let index ← env.slice position definition
        pure { located with corlib := ← index.corlibIdentity }
    | none => pure located
  let some returned := siteReturn site.methodArguments ownerArguments site.result
    | throw (.operandMismatch token)
  if call.returnsValue != (returned != .primitive 1) || !(closed.admits returned call.returnType)
  then throw (.operandMismatch token)
  let some parameters := site.parameters.mapM (siteParameter site.methodArguments ownerArguments)
    | throw (.operandMismatch token)
  if !parametersAdmitted closed parameters call.parameterTypes then throw (.operandMismatch token)
  return ()

/-- A scoped call operand agrees with the assembly of its resolved declaring type. -/
theorem checkCallReference_scope {env : MetadataEnv} {frame : Frame} {token : Nat}
    {site : MethodSite} {call : CallSite} {head : NamedType} {scope : String}
    (checked : checkCallReference env frame token site call = .ok ())
    (declared : site.owner.head = some head)
    (named : call.declaringType.headScope = some scope) : bytesOf scope = head.scope := by
  by_cases different : bytesOf scope = head.scope
  · exact different
  exfalso
  have bad : (bytesOf scope != head.scope) = true := by simpa using different
  simp [checkCallReference, declared, named, bad, throw, throwThe, MonadExceptOf.throw,
    Bind.bind, Except.bind, pure, Except.pure] at checked
  repeat first | contradiction | split at checked
#print axioms checkCallReference_scope

/-- Resolve the token through the selected import, or through the ordinary metadata environment. -/
def resolveCallMember (env : MetadataEnv) (frame : Frame) (token : Nat) (call : CallSite)
    (slot : Option ImportSlot) : Except MetadataError MethodSite :=
  match slot, call.target with
    | some binding, .external identity => do
      if binding.hasThis || binding.identity != identity || !importSignatureMatches binding call ||
          binding.parameterCount != call.parameterCount || binding.returnsValue != call.returnsValue then
        throw (.operandMismatch token)
      env.importMethodSite token frame identity
    | some _, _ => throw (.unresolvedMember token)
    | none, _ => env.methodSite token

/-- The operand target and typed reference both name the method at the token. -/
def checkCallOperand (env : MetadataEnv) (frame : Frame) (token : Nat) (call : CallSite)
    (slot : Option ImportSlot := none) : Except MetadataError TokenFacts := do
  let site ← resolveCallMember env frame token call slot
  checkCallReference env frame token site call
  match call.target with
  | .managed target =>
    match site.definition with
    | some (_, definition) =>
      if target == definition then .ok {} else .error (.operandMismatch token)
    | none => .error (.operandMismatch token)
  | .external identity =>
    if site.definition.isSome || !(site.externalMatches frame identity) then
      .error (.operandMismatch token)
    else .ok {}

/-- A checked managed operand resolves to a definition in a carried slice. The MethodDef token
    in that slice is the target of the call, and its signature checks the same typed reference. -/
theorem checkCallOperand_managed {env : MetadataEnv} {frame : Frame} {token target : Nat}
    {call : CallSite} {facts : TokenFacts}
    (checked : checkCallOperand env frame token call = .ok facts)
    (managed : call.target = .managed target) :
    ∃ site position, env.methodSite token = .ok site ∧
      checkCallReference env frame token site call = .ok () ∧
      site.definition = some (position, target) := by
  unfold checkCallOperand at checked
  simp only [resolveCallMember] at checked
  cases resolved : env.methodSite token with
  | error fault => simp [resolved, bind, Except.bind] at checked
  | ok site =>
    cases reference : checkCallReference env frame token site call with
    | error fault => simp [resolved, reference, bind, Except.bind] at checked
    | ok result =>
      cases result
      cases definition : site.definition with
      | none => simp [resolved, reference, managed, definition, bind, Except.bind] at checked
      | some pair =>
        obtain ⟨position, method⟩ := pair
        by_cases same : target = method
        · exact ⟨site, position, rfl, reference, same ▸ definition⟩
        · simp [resolved, reference, managed, definition, same, bind, Except.bind] at checked

#print axioms checkCallOperand_managed

/-- The same member binds the typed reference and both permitted external identity spellings. -/
theorem checkCallOperand_external {env : MetadataEnv} {frame : Frame} {token : Nat}
    {call : CallSite} {identity : String} {facts : TokenFacts} {slot : Option ImportSlot}
    (checked : checkCallOperand env frame token call slot = .ok facts)
    (externalTarget : call.target = .external identity) :
    ∃ site, resolveCallMember env frame token call slot = .ok site ∧
      checkCallReference env frame token site call = .ok () ∧ site.definition = none ∧
      (site.externalName = some (bytesOf identity) ∨
        site.contractName frame = some (bytesOf identity)) := by
  unfold checkCallOperand at checked
  simp only [externalTarget, bind, Except.bind] at checked
  cases resolved : resolveCallMember env frame token call slot with
  | error fault => simp [resolved] at checked
  | ok site =>
    refine ⟨site, rfl, ?_⟩
    cases reference : checkCallReference env frame token site call with
    | error fault => simp [resolved, reference, bind, Except.bind] at checked
    | ok result =>
      cases result
      simp [resolved, reference, bind, Except.bind] at checked
      split at checked
      · contradiction
      · rename_i accepted
        by_cases named : site.externalName = some (bytesOf identity) <;>
          simpa [MethodSite.externalMatches, named] using accepted

#print axioms checkCallOperand_external

/-! ## Indirect calls and strings -/

/-- Check an `.indirectCall` operand against its standalone signature. -/
def checkIndirectOperand (env : MetadataEnv) (frame : Frame) (token : Nat) (result : TypeExpr)
    (parameters : List TypeExpr) (hasThis explicitThis : Bool) (convention : Nat) :
    Except MetadataError TokenFacts := do
  let index ← env.slice 0 token
  let blob ← index.blob (← index.signatureOf Table.standAloneSig token)
  let signature ← env.resolveMethod 0 blob
  let (stated, arity, returned, types) := signature
  if arity != 0 || stated / genericFlag % 2 == 1 then throw (.unsupportedSignature 0 stated)
  if convention != stated % 0x20 || hasThis != (stated / hasThisFlag % 2 == 1) ||
      explicitThis != (stated / explicitThisFlag % 2 == 1) ||
      !(frame.admits returned result) || parameters.length != types.length ||
      !(types.zip parameters).all (fun (type, claimed) => frame.admits type claimed) then
    throw (.operandMismatch token)
  .ok {}

/-- Check one token-table entry, read in a frame built once for the method: what the token names
    must be what the operand says. -/
def checkEntryIn (env : MetadataEnv) (frame : Frame) (token : Nat) (operand : RawOperand) :
    Except MetadataError TokenFacts := do
  match operand with
  | .type expr =>
    if metadataTableOf token == Table.typeRef || metadataTableOf token == Table.typeDef ||
        metadataTableOf token == Table.typeSpec then checkTypeOperand env frame token expr
    else .error (.unsupportedTable token)
  | .field owner index fieldType name isStatic =>
    checkFieldOperand env frame token owner index fieldType name isStatic
  | .call site => checkCallOperand env frame token site
  | .indirectCall result parameters hasThis explicitThis convention =>
    checkIndirectOperand env frame token result parameters hasThis explicitThis convention
  | .text text =>
    if metadataTableOf token != Table.userString then throw (.unsupportedTable token)
    let index ← env.slice 0 token
    if (← userStringMatches index token text) then .ok {} else .error (.operandMismatch token)
  | _ => .error (.operandMismatch token)

/-- Check one token-table entry of a method with `arity` generic parameters whose owner has
    `ownerArity`. -/
def checkEntry (env : MetadataEnv) (arity : Nat) (token : Nat) (operand : RawOperand)
    (ownerArity : Nat := 0) : Except MetadataError TokenFacts := do
  checkEntryIn env (← env.frame arity ownerArity) token operand

/-- The facts that depend on the opcode using a token: a static field access names a static
    field, an instance access an instance field, `ldtoken` of a field takes the static form, and
    the platform constant field is only loaded. -/
def checkSite (opcode : Nat) (facts : TokenFacts) : RawOperand → Bool
  | .field owner index type name isStatic =>
    if ({ owner, index, type, name } : FieldRef) == littleEndianField && opcode != 0x7E then false
    else if opcode == 0x7E || opcode == 0x7F || opcode == 0x80 then
      isStatic && facts.staticField != some false
    else if opcode == 0x7B || opcode == 0x7C || opcode == 0x7D then
      !isStatic && facts.staticField != some true
    else if opcode == 0xD0 then isStatic
    else false
  | _ => true

/-! ## Locals -/

/-- Check the local variable types against the standalone signature the header names, for a
    method with `arity` generic parameters whose owner has `ownerArity`. -/
def checkLocals (env : MetadataEnv) (arity signature : Nat) (locals : List TypeExpr)
    (ownerArity : Nat := 0) : Except MetadataError Unit := do
  if signature == 0 then
    if locals.isEmpty then return () else throw (.localMismatch 0)
  if metadataTableOf signature != Table.standAloneSig then throw (.unsupportedTable signature)
  let frame ← env.frame arity ownerArity
  let index ← env.slice 0 signature
  let blob ← index.blob (← index.signatureOf Table.standAloneSig signature)
  let types ← env.resolveAll 0 (← decodeLocalSig blob)
  if types.length != locals.length then throw (.localMismatch (min types.length locals.length))
  let rec compare : Nat → List ResolvedType → List TypeExpr → Except MetadataError Unit
    | _, [], _ | _, _, [] => .ok ()
    | position, type :: types, claimed :: locals =>
      if frame.admits type claimed then compare (position + 1) types locals
      else .error (.localMismatch position)
  compare 0 types locals

/-! ## The method definition -/

/-- Whether generic parameter rows have the attribute flags the extractor states. -/
def flagsAgree (rows : List GenericParamRow) (claimed : List GenericConstraint) : Bool :=
  rows.length == claimed.length && (rows.zip claimed).all fun (row, constraint) =>
    row.flags == constraint.flags

/-- The names of a method's definition as its metadata spells them: the scoped name of its owner
    type, `scope::name`, the scope and name of each base class of an object receiver's type, from
    the nearest, and the signature a proof selects the method by. The extractor states them as
    strings, which `MethodNames.spelling` and `MethodNames.Selects` read from the bytes. -/
structure MethodNames where
  owner : List Nat := []
  bases : List (List Nat × List Nat) := []
  /-- Cecil's full name of the extracted method: the instance's, for a generic instance. -/
  signature : List Nat := []
  deriving DecidableEq, Repr

/-- The owner string and base class types these names spell, or `none` when a name is not
    well-formed UTF-8. -/
def MethodNames.spelling (names : MethodNames) : Option (String × List TypeExpr) := do
  let owner ← spelled? names.owner
  let bases ← names.bases.mapM fun (scope, name) => do
    pure (TypeExpr.object (← spelled? scope) (← spelled? name))
  pure (owner, bases)

/-- The names are the owner and base class types the method states. An equation between strings
    and bytes, so an extraction proves it with `cil_kernel_rfl`. -/
abbrev MethodNames.Spell (names : MethodNames) (method : RawMethod) : Prop :=
  names.spelling = some (method.owner, method.objectBases)

/-- Whether each base class name is the bytes of the object type at its position. -/
def basesSpelled : List (List Nat × List Nat) → List TypeExpr → Bool
  | [], [] => true
  | (scope, name) :: bases, .object scopeText nameText :: types =>
    scope == bytesOf scopeText && name == bytesOf nameText && basesSpelled bases types
  | _, _ => false

/-- Whether the names are the bytes of the owner and base classes the method states. A decision
    over bytes, so a method whose strings are stored as bytes proves `Spell` without the kernel
    encoding them. -/
def MethodNames.spelledBy (names : MethodNames) (method : RawMethod) : Bool :=
  names.owner == bytesOf method.owner && basesSpelled names.bases method.objectBases

private theorem bases_of_basesSpelled : ∀ (bases : List (List Nat × List Nat))
    (types : List TypeExpr), basesSpelled bases types = true →
      bases.mapM (fun entry => (spelled? entry.1).bind fun scope =>
        (spelled? entry.2).bind fun name => pure (TypeExpr.object scope name)) = some types
  | [], [], _ => rfl
  | (scope, name) :: bases, .object scopeText nameText :: types, spelled => by
    simp only [basesSpelled, Bool.and_eq_true, beq_iff_eq] at spelled
    obtain ⟨⟨rfl, rfl⟩, rest⟩ := spelled
    simp only [List.mapM_cons, spelled?_bytesOf, Option.bind_some]
    rw [bases_of_basesSpelled bases types rest]
    rfl

/-- Names whose bytes are those of the method's owner and base classes spell them. -/
theorem MethodNames.spell_of_spelledBy {names : MethodNames} {method : RawMethod}
    (spelled : names.spelledBy method = true) : names.Spell method := by
  simp only [MethodNames.spelledBy, Bool.and_eq_true, beq_iff_eq] at spelled
  obtain ⟨owner, bases⟩ := spelled
  simp only [MethodNames.Spell, MethodNames.spelling, owner, spelled?_bytesOf]
  simp only [bind]
  rw [bases_of_basesSpelled _ _ bases]
  rfl
#print axioms MethodNames.spell_of_spelledBy

/-- The names spell `signature`, the string a proof selects the method by. An equation between a
    string and bytes, so an extraction proves it with `cil_kernel_rfl`. -/
abbrev MethodNames.Selects (names : MethodNames) (signature : String) : Prop :=
  spelled? names.signature = some signature

/-- The `MethodDef` flag of an abstract method, which has no body. -/
def abstractMethodFlag : Nat := 0x0400

/-- The `MethodDef` flag of a platform invoke, whose body is native code outside the image. -/
def platformInvokeFlag : Nat := 0x2000

/-- The `MethodDef` implementation flag of a method the runtime implements itself. -/
def internalCallFlag : Nat := 0x1000

/-- The `MethodDef` implementation flag of a runtime-async method, whose body returns the result
    its signature states as a task. -/
def runtimeAsyncFlag : Nat := 0x2000

/-- Whether a `MethodDef` row's flags say the method has no IL body in the image. -/
def hasNoBody (flags implFlags : Nat) : Bool :=
  implFlags % 4 != 0 || flags / abstractMethodFlag % 2 == 1 ||
    flags / platformInvokeFlag % 2 == 1 || implFlags / internalCallFlag % 2 == 1

/-- `.ctor` and `.cctor` as bytes. -/
def constructorName : List Nat := [46, 99, 116, 111, 114]
def classConstructorName : List Nat := [46, 99, 99, 116, 111, 114]

/-- Whether a `MethodDef` row is a constructor as Cecil reads one: its special-name and
    runtime-special-name flags are set and it is named `.ctor` or `.cctor`. -/
def isConstructorRow (flags : Nat) (name : List Nat) : Bool :=
  flags / 0x800 % 2 == 1 && flags / 0x1000 % 2 == 1 &&
    (name == constructorName || name == classConstructorName)

/-- Cecil's full name of the method a `MethodDef` row defines, instantiated at `instantiation`,
    method arguments first: the result and parameters substituted as Cecil substitutes them, and
    an instantiated method other than a constructor named with its arguments. An empty
    instantiation leaves the declared types, which then must name no generic parameter. -/
def instanceSignature (owner name : List Nat) (constructor : Bool) (arity : Nat)
    (instantiation : List ResolvedType) (returned : ResolvedType)
    (parameters : List ResolvedType) : Option (List Nat) := do
  let methodArguments := instantiation.take arity
  let ownerArguments := instantiation.drop arity
  let spell (type : ResolvedType) : Option (List Nat) :=
    instanceType methodArguments ownerArguments type >>= cecilName true resolveFuel
  let result ← spell returned
  let spelledParameters ← parameters.mapM spell
  let named ←
    if instantiation.isEmpty || constructor then pure name
    else (fun spelled => name ++ [60] ++ spelled ++ [62]) <$>
      cecilNames true resolveFuel (ResolvedList.ofList instantiation)
  pure (methodFullName result owner named spelledParameters)

/-- Check the method definition against its `MethodDef` row: flags, name, signature, generic
    parameters, owner and class layout facts, and return the names it resolves, which the caller
    ties to the extractor's strings. Each closed argument resolves from `sources` and must
    admit the corresponding type in `arguments`. The row's relative virtual
    address, which the extractor zeroes in the rows it carries, and its parameter list are not
    read: where a body sits in the image is the strict audit's to confirm. A modified return or
    parameter is refused, except an `init` accessor's void and an `in` reference. -/
def methodIdentityValid (env : MetadataEnv) (method : RawMethod)
    (sources : List InstanceArgument) (arguments : List TypeExpr) :
    Except MetadataError MethodNames := do
  let index ← env.slice 0 method.token
  if metadataTableOf method.token != Table.methodDef then
    throw (.unsupportedTable method.token)
  let row ← index.methodDef method.token
  if row.flags != method.attributes || row.implFlags != method.implementation then
    throw (.methodMismatch method.token)
  -- A row with native, runtime or no code has no IL body for the decoded bytes to be.
  if hasNoBody row.flags row.implFlags then throw (.bodyLocation method.token)
  -- A runtime-async body returns its task's result, which the model would read as the task itself.
  if row.implFlags / runtimeAsyncFlag % 2 == 1 then throw (.runtimeAsync method.token)
  let signature ← decodeMethodSig (← index.blob row.signature)
  let convention := signature.convention
  -- EXPLICITTHIS puts the receiver in the parameter list, outside the implicit receiver model.
  if method.explicitThis || method.hasThis != (convention / hasThisFlag % 2 == 1) ||
      method.explicitThis != (convention / explicitThisFlag % 2 == 1) ||
      method.callingConvention != convention % 0x20 then throw (.methodMismatch method.token)
  let ownerToken ← env.declaringType 0 method.token
  let owner ← typeDefNamed env 0 resolveFuel ownerToken
  let methodParameters ← index.methodGenericParameters 0 method.token signature.genericArity
  let ownerParameters ← index.genericParameters 0 ownerToken
  if methodParameters.length != signature.genericArity ||
      !flagsAgree methodParameters method.genericParameters ||
      !flagsAgree ownerParameters method.ownerParameters || method.ownerArgumentCount != 0 then
    throw (.methodMismatch method.token)
  let frame ← env.frame method.genericParameters.length method.ownerParameters.length
  let returned ← env.resolve 0 signature.result
  let normalizedReturn := declaredReturn returned
  if hasModifier resolveFuel normalizedReturn then throw (.methodMismatch method.token)
  let parameters ← env.resolveAll 0 signature.parameters
  -- An argument read narrows by the declared type, so no parameter may hide a modifier in an atom.
  if parameters.any (hasModifier resolveFuel ∘ declaredParameter) then
    throw (.methodMismatch method.token)
  if !(frame.admits normalizedReturn method.returnType) ||
      !parametersAdmitted frame (parameters.map declaredParameter) method.parameters then
    throw (.methodMismatch method.token)
  -- A row with generic parameters is extracted only as an instance naming an argument for each.
  let instantiation ← sources.mapM (InstanceArgument.resolve env method.token resolveFuel)
  if instantiation.length != arguments.length ||
      instantiation.length != methodParameters.length + ownerParameters.length ||
      !(instantiation.zip arguments).all (fun (type, claimed) => frame.admits type claimed) then
    throw (.genericMismatch method.token)
  let name ← index.string row.name
  let some selected := instanceSignature owner.name name (isConstructorRow row.flags name)
      signature.genericArity instantiation returned parameters
    | throw (.methodMismatch method.token)
  let ownerName := owner.scope ++ [58, 58] ++ owner.name
  let receiverMatches :=
    if method.hasThis then
      match owner.kind with
      | .classType => method.objectReceiver
      | .valueType | .enumType _ => !method.objectReceiver
      | .interfaceType | .importedOwner | .external _ => false
    else !method.objectReceiver
  if !receiverMatches then throw (.methodMismatch method.token)
  if method.objectReceiver then
    let chain ← env.classChain resolveFuel 0 ownerToken
    let some own := index.instanceTotal.find? ownerToken | throw (.missingRow ownerToken)
    let bases ← chain.mapM fun (position, token) => typeDefNamed env position resolveFuel token
    if method.objectFieldCount != (← env.chainFieldCount chain) + own then
      throw (.methodMismatch method.token)
    .ok { owner := ownerName, bases := bases.map fun base => (base.scope, base.name),
          signature := selected }
  else if method.objectFieldCount != 0 then throw (.methodMismatch method.token)
  else .ok { owner := ownerName, signature := selected }

end CIL.Extraction
