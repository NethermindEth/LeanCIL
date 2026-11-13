import CIL.Extraction.MetadataResolution
import CIL.Extraction.Assemblies

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
definitions in platform assemblies, public key tokens and the hashed part of generic import
identities.
-/

namespace CIL.Extraction

/-- What a token says that depends on the instruction using it: whether a `Field` row is
    static, when the row is carried. -/
structure TokenFacts where
  staticField : Option Bool := none
  deriving DecidableEq, Repr

/-- The frame of the primitive assembly and generic arity a method's types are read in. -/
def MetadataEnv.frame (env : MetadataEnv) (arity : Nat) : Except MetadataError Frame := do
  let index ← env.slice 0 0
  let corlib ← index.corlibIdentity
  .ok { corlib := corlib, anchor := corlib.getD [], arity := arity }

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
        else do .ok (← index.typeDef (owner + 1)).methodList
      .ok (row.methodList, end_)
  if tokenRow token < start || stop ≤ tokenRow token then throw (.unresolvedMember token)
  .ok owner

/-- The type a definition token's owner names, with its generic parameters left open. -/
def MetadataEnv.ownerOf (env : MetadataEnv) (position token : Nat) :
    Except MetadataError NamedType := do
  typeDefNamed env position resolveFuel (← env.declaringType position token)

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

/-- The scope an extractor type spells for its head: the atom's, object's or constructor's, or
    the scope an aggregate or enum identity starts with. -/
def TypeExpr.headScope : TypeExpr → Option String
  | .atom scope _ | .object scope _ | .constructor scope _ => some scope
  | .apply applied _ => applied.headScope
  | _ => none

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
    .ok { owner := .named (← env.ownerOf 0 token), name := ← index.string row.name,
          declared := ← env.resolveBlob 0 token row.signature, definition := some (0, token) }
  else
    let row ← index.memberRef token
    let owner ← env.resolveToken 0 row.parent
    let name ← index.string row.name
    let declared ← env.resolveBlob 0 token row.signature
    let definition ← match owner.head with
      | some head => env.fieldDefinition token head name declared
      | none => .error (.unresolvedMember token)
    .ok { owner := owner, name := name, declared := declared, definition := definition }

/-- The base classes of a class definition, nearest first, as slice positions and `TypeDef`
    tokens. The chain ends at `System.Object` of the primitive assembly. -/
def MetadataEnv.classChain (env : MetadataEnv) :
    Nat → Nat → Nat → Except MetadataError (List (Nat × Nat))
  | 0, _, token => .error (.unsupportedBase token)
  | fuel + 1, position, token => do
    let index ← env.slice position token
    let row ← index.typeDef token
    match metadataTableOf row.extends_ with
    | 0x02 =>
      if tokenRow row.extends_ == 0 then .error (.unsupportedBase token)
      else do .ok ((position, row.extends_) :: (← env.classChain fuel position row.extends_))
    | 0x01 =>
      let named ← typeRefNamed env position resolveFuel row.extends_ (some false)
      if named.pinned then
        let some (linked, definition) := index.link linkDefinition row.extends_
          | throw (.unsupportedBase token)
        .ok ((linked, definition) :: (← env.classChain fuel linked definition))
      else
        let corlib ← index.corlibIdentity
        if some named.scope == corlib && named.name == bytesOf "System.Object" then .ok []
        else .error (.unsupportedBase token)
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

/-- The index a field operand must carry, and the type it must hold. A field signature's `!n`
    names the declaring type's parameter, so the held type reads it as the declaring instance's
    argument, which may itself be a parameter of the reading method or its owner. -/
def MetadataEnv.expectedField (env : MetadataEnv) (token : Nat) (site : FieldSite)
    (classOwner : Bool) : Except MetadataError (Nat × ResolvedType × Option Bool) := do
  let some held := substituteResolved none site.owner.arguments resolveFuel site.declared
    | throw (.operandMismatch token)
  match site.definition with
  | some (position, definition) =>
    let index ← env.slice position definition
    let row ← index.field definition
    let isStatic := row.flags / 0x10 % 2 == 1
    if isStatic then
      let owner ← env.declaringType position definition
      let (start, _) ← index.fieldRange owner
      .ok (tokenRow definition - start, held, some true)
    else .ok (← env.instanceIndex position definition classOwner, held, some false)
  | none =>
    let corlib ← (← env.slice 0 token).corlibIdentity
    match site.owner with
    | .genericInst head arguments =>
      match arguments.toList with
      | [first, second] =>
        if some head.scope == corlib && head.name == bytesOf "System.ValueTuple`2" then
          if site.name == bytesOf "Item1" then .ok (0, first, none)
          else if site.name == bytesOf "Item2" then .ok (1, second, none)
          else .ok (0, held, none)
        else .ok (0, held, none)
      | _ => .ok (0, held, none)
    | _ => .ok (0, held, none)

/-- Check a `.field` operand: the owner, the field's model index and the type it holds. -/
def checkFieldOperand (env : MetadataEnv) (frame : Frame) (token : Nat) (owner : TypeExpr)
    (index : Nat) (fieldType : TypeExpr) (isStatic : Bool) : Except MetadataError TokenFacts := do
  if metadataTableOf token != Table.field && metadataTableOf token != Table.memberRef then
    throw (.unsupportedTable token)
  let site ← env.fieldSite token
  let classOwner := match owner with
    | .object .. => true
    | _ => false
  let (expected, held, isStaticFact) ← env.expectedField token site classOwner
  if isStaticFact.any (· != isStatic) then throw (.operandMismatch token)
  if !(frame.admits site.owner owner) then throw (.operandMismatch token)
  if index != expected then throw (.fieldIndexMismatch token index expected)
  if !(frame.admits held fieldType) then throw (.operandMismatch token)
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

/-- Read a `MethodDef` or `MemberRef` token as a method. -/
def MetadataEnv.memberSite (env : MetadataEnv) (token : Nat) :
    Except MetadataError MethodSite := do
  let index ← env.slice 0 token
  match metadataTableOf token with
  | 0x06 =>
    let row ← index.methodDef token
    let signature ← env.resolveMethod 0 (← index.blob row.signature)
    .ok { owner := .named (← env.ownerOf 0 token), name := ← index.string row.name,
          convention := signature.1, genericArity := signature.2.1, result := signature.2.2.1,
          parameters := signature.2.2.2, definition := some (0, token), methodArguments := none }
  | 0x0A =>
    let row ← index.memberRef token
    let owner ← env.resolveToken 0 row.parent
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
def MetadataEnv.methodSite (env : MetadataEnv) (token : Nat) :
    Except MetadataError MethodSite := do
  if metadataTableOf token == Table.methodSpec then
    let index ← env.slice 0 token
    let row ← index.methodSpec token
    let site ← env.memberSite row.method
    let arguments ← decodeMethodSpec (← index.blob row.instantiation)
    .ok { site with methodArguments := some (← env.resolveAll 0 arguments) }
  else env.memberSite token

/-- Cecil's full name of a method, `result Owner::name(parameters)`, from the full names of its
    parts. -/
def methodFullName (result owner name : List Nat) (parameters : List (List Nat)) : List Nat :=
  result ++ [32] ++ owner ++ [58, 58] ++ name ++ [40] ++ (parameters.intersperse [44]).flatten ++
    [41]

/-- The identity an external call target spells: the declaring type's scope, then Cecil's full
    name of the method. -/
def MethodSite.externalName (site : MethodSite) : Option (List Nat) := do
  let head ← site.owner.head
  let result ← cecilName resolveFuel site.result
  let owner ← cecilName resolveFuel site.owner
  let parameters ← site.parameters.mapM (cecilName resolveFuel)
  some (head.scope ++ [58, 58] ++ methodFullName result owner site.name parameters)

/-- Whether an external identity is exactly the one the member spells. -/
def MethodSite.externalMatches (site : MethodSite) (identity : String) : Bool :=
  site.externalName == some (bytesOf identity)

/-- Check a `.call` operand against the member its token names. -/
def checkCallOperand (env : MetadataEnv) (frame : Frame) (token : Nat) (call : CallSite) :
    Except MetadataError TokenFacts := do
  let site ← env.methodSite token
  let extracted := site.definition.isSome
  let ownerArguments := site.owner.arguments
  let ownerList := ownerArguments.getD []
  let head ← match site.owner.head with
    | some head => pure head
    | none => throw (.unresolvedType token)
  if bytesOf call.name != site.name then throw (.operandMismatch token)
  let expected := site.methodArguments.getD [] ++ (if extracted then ownerList else [])
  if call.typeArguments.length != expected.length || !(expected.zip call.typeArguments).all
      (fun (type, claimed) => frame.admits type claimed) then
    throw (.genericMismatch token)
  if call.ownerArgumentCount != (if extracted then ownerList.length else 0) then
    throw (.genericMismatch token)
  if call.declaringType.headScope.any (bytesOf · != head.scope) then
    throw (.scopeMismatch token)
  let located := { frame with anchor := head.scope }
  if !(located.admits site.owner call.declaringType) then throw (.operandMismatch token)
  if call.hasThis != (site.convention / hasThisFlag % 2 == 1) ||
      call.parameterCount != site.parameters.length then throw (.operandMismatch token)
  let some returned := siteReturn site.methodArguments ownerArguments site.result
    | throw (.operandMismatch token)
  if call.returnsValue != (returned != .primitive 1) || !(located.admits returned call.returnType)
  then throw (.operandMismatch token)
  let some parameters := site.parameters.mapM (siteParameter site.methodArguments ownerArguments)
    | throw (.operandMismatch token)
  if call.parameterTypes.length != parameters.length ||
      !(parameters.zip call.parameterTypes).all
        (fun (type, claimed) => located.admits type claimed)
  then throw (.operandMismatch token)
  match call.target with
  | .managed target =>
    match site.definition with
    | some (_, definition) =>
      if target == definition then .ok {} else .error (.operandMismatch token)
    | none => .error (.operandMismatch token)
  | .external identity =>
    if extracted || !(site.externalMatches identity) then .error (.operandMismatch token)
    else .ok {}

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
  | .field owner index fieldType isStatic =>
    checkFieldOperand env frame token owner index fieldType isStatic
  | .call site => checkCallOperand env frame token site
  | .indirectCall result parameters hasThis explicitThis convention =>
    checkIndirectOperand env frame token result parameters hasThis explicitThis convention
  | .text text =>
    if metadataTableOf token != Table.userString then throw (.unsupportedTable token)
    let index ← env.slice 0 token
    if (← userStringMatches index token text) then .ok {} else .error (.operandMismatch token)
  | _ => .error (.operandMismatch token)

/-- Check one token-table entry of a method with arity generic parameters. -/
def checkEntry (env : MetadataEnv) (arity : Nat) (token : Nat) (operand : RawOperand) :
    Except MetadataError TokenFacts := do
  checkEntryIn env (← env.frame arity) token operand

/-- The facts that depend on the opcode using a token: a static field access names a static
    field, an instance access an instance field, and `ldtoken` of a field takes the static form. -/
def checkSite (opcode : Nat) (facts : TokenFacts) : RawOperand → Bool
  | .field _ _ _ isStatic =>
    if opcode == 0x7E || opcode == 0x7F || opcode == 0x80 then
      isStatic && facts.staticField != some false
    else if opcode == 0x7B || opcode == 0x7C || opcode == 0x7D then
      !isStatic && facts.staticField != some true
    else if opcode == 0xD0 then isStatic
    else false
  | _ => true

/-! ## Locals -/

/-- Check the local variable types against the standalone signature the header names. -/
def checkLocals (env : MetadataEnv) (arity signature : Nat) (locals : List TypeExpr) :
    Except MetadataError Unit := do
  if signature == 0 then
    if locals.isEmpty then return () else throw (.localMismatch 0)
  if metadataTableOf signature != Table.standAloneSig then throw (.unsupportedTable signature)
  let frame ← env.frame arity
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

/-- The `GenericParam` rows that name `owner`, from the row its link gives while they continue. -/
private def genericRun (index : MetadataIndex) (owner : Nat) :
    Nat → Nat → Except MetadataError (List GenericParamRow)
  | 0, _ => .ok []
  | fuel + 1, row =>
    if index.header.rows Table.genericParam < row then .ok []
    else do
      let entry ← index.genericParam (tokenOf Table.genericParam row)
      if entry.owner != owner then .ok []
      else do .ok (entry :: (← genericRun index owner fuel (row + 1)))

/-- The generic parameters of a `TypeDef` or `MethodDef`, numbered from 0 in order. The link
    names the first row of the run; the row before it must name another owner, so the run is
    not cut short. -/
def MetadataIndex.genericParameters (index : MetadataIndex) (owner : Nat) :
    Except MetadataError (List GenericParamRow) :=
  match index.link linkGenericParams owner with
  | none => .ok []
  | some (_, first) => do
    if first != tokenOf Table.genericParam (tokenRow first) || tokenRow first == 0 then
      throw (.tokenOutOfScope first)
    if 1 < tokenRow first then
      if (← index.genericParam (first - 1)).owner == owner then throw (.unresolvedMember owner)
    let run ← genericRun index owner (index.header.rows Table.genericParam) (tokenRow first)
    if (run.zipIdx.all fun (entry, position) => entry.number == position) then .ok run
    else .error (.unresolvedMember owner)

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

/-- The names spell `signature`, the string a proof selects the method by. An equation between a
    string and bytes, so an extraction proves it with `cil_kernel_rfl`. -/
abbrev MethodNames.Selects (names : MethodNames) (signature : String) : Prop :=
  spelled? names.signature = some signature

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
    instanceType methodArguments ownerArguments type >>= cecilName resolveFuel
  let result ← spell returned
  let spelledParameters ← parameters.mapM spell
  let named ←
    if instantiation.isEmpty || constructor then pure name
    else (fun spelled => name ++ [60] ++ spelled ++ [62]) <$>
      cecilNames resolveFuel (ResolvedList.ofList instantiation)
  pure (methodFullName result owner named spelledParameters)

/-- Check the method definition against its `MethodDef` row: flags, name, signature, generic
    parameters, owner and class layout facts, and return the names it resolves, which the caller
    ties to the extractor's strings. A generic instance names its type arguments in
    `instantiation`, which must be the types `arguments` name. The row's relative virtual
    address, which the extractor zeroes in the rows it carries, and its parameter list are not
    read: where a body sits in the image is the strict audit's to confirm. -/
def methodIdentityValid (env : MetadataEnv) (method : RawMethod)
    (instantiation : List ResolvedType) (arguments : List TypeExpr) :
    Except MetadataError MethodNames := do
  let index ← env.slice 0 method.token
  if metadataTableOf method.token != Table.methodDef then
    throw (.unsupportedTable method.token)
  let row ← index.methodDef method.token
  if row.flags != method.attributes || row.implFlags != method.implementation then
    throw (.methodMismatch method.token)
  if row.implFlags % 4 != 0 then throw (.bodyLocation method.token)
  let signature ← decodeMethodSig (← index.blob row.signature)
  let convention := signature.convention
  if method.hasThis != (convention / hasThisFlag % 2 == 1) ||
      method.explicitThis != (convention / explicitThisFlag % 2 == 1) ||
      method.callingConvention != convention % 0x20 then throw (.methodMismatch method.token)
  let ownerToken ← env.declaringType 0 method.token
  let owner ← typeDefNamed env 0 resolveFuel ownerToken
  let methodParameters ← index.genericParameters method.token
  let ownerParameters ← index.genericParameters ownerToken
  if methodParameters.length != signature.genericArity ||
      !flagsAgree methodParameters method.genericParameters ||
      !flagsAgree ownerParameters method.ownerParameters || method.ownerArgumentCount != 0 then
    throw (.methodMismatch method.token)
  let frame ← env.frame method.genericParameters.length
  let returned ← env.resolve 0 signature.result
  let parameters ← env.resolveAll 0 signature.parameters
  if !(frame.admits (declaredReturn returned) method.returnType) ||
      parameters.length != method.parameters.length ||
      !(parameters.zip method.parameters).all
        (fun (type, claimed) => frame.admits (declaredParameter type) claimed) then
    throw (.methodMismatch method.token)
  if instantiation.length != arguments.length || (!instantiation.isEmpty &&
        instantiation.length != methodParameters.length + ownerParameters.length) ||
      !(instantiation.zip arguments).all (fun (type, claimed) => frame.admits type claimed) then
    throw (.genericMismatch method.token)
  let name ← index.string row.name
  let some selected := instanceSignature owner.name name (isConstructorRow row.flags name)
      signature.genericArity instantiation returned parameters
    | throw (.methodMismatch method.token)
  let ownerName := owner.scope ++ [58, 58] ++ owner.name
  if method.objectReceiver then
    if !method.hasThis || owner.kind != .classType then throw (.methodMismatch method.token)
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
