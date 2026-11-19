import CIL.CallSite
import CIL.Extraction.TypeStorage
import CIL.Extraction.FlowIndex
import CIL.Extraction.LinkIndex
import CIL.Imports
import CIL.Extraction.MetadataNames

/-!
# Raw methods, generic instantiation and call binding

The raw CIL vocabulary that extraction evidence is checked against: instructions with
their decoded operands, method bodies with metadata types, and call sites. A generic
method is extracted once per closed instantiation; `SpecializationValid` reproduces the
closed body by substitution from the original, and `ManagedCallsValid` checks that every
emitted call selects the right instantiation or import slot.

Opcodes are numeric ECMA-335 encodings; two-byte opcodes `0xFE nn` appear as `0xFE00 + nn`.
-/

namespace CIL.Extraction


/-- A decoded instruction operand. A field operand names its owner type, the field's index in
    the owner's raw layout, the type it holds and the name of the metadata row its token names. -/
inductive RawOperand where
  | none
  | integer (value : Int)
  | text (value : String)
  | argument (index : Nat)
  | local (index : Nat)
  | target (pc : Nat)
  | targets (pcs : List Nat)
  | type (value : TypeExpr)
  | field (owner : TypeExpr) (index : Nat) (type : TypeExpr) (name : MetadataName)
      (isStatic : Bool)
  | call (site : CallSite)
  | indirectCall (returnType : TypeExpr) (parameters : List TypeExpr)
      (hasThis explicitThis : Bool) (callingConvention : Nat)
  deriving DecidableEq, Repr

/-- The typed reference a field operand names: its owner, index, held type and name. `none` for
    any other operand; the opcode, not the reference, says whether the field is static. -/
def FieldRef.ofOperand? : RawOperand → Option FieldRef
  | .field owner index type name _ => some { owner, index, type, name }
  | _ => none

/-- A reference is built exactly from a field operand with its owner, index, type and name. -/
theorem FieldRef.ofOperand?_eq_some {operand : RawOperand} {reference : FieldRef} :
    FieldRef.ofOperand? operand = some reference ↔ ∃ isStatic,
      operand = .field reference.owner reference.index reference.type reference.name isStatic := by
  cases operand
  case field owner index type name isStatic =>
    cases reference
    simp only [FieldRef.ofOperand?, Option.some.injEq, FieldRef.mk.injEq, RawOperand.field.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨isStatic, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl⟩
  all_goals simp [FieldRef.ofOperand?]

#print axioms FieldRef.ofOperand?_eq_some

/-- One CIL instruction: its byte offset, opcode and operand. Branch operands are
    already instruction indices. -/
structure RawInstruction where
  offset : Nat
  opcode : Nat
  operand : RawOperand
  deriving DecidableEq, Repr

/-- Direct calls, virtual calls and constructions take a method token. -/
def methodTokenCall (opcode : Nat) : Bool :=
  opcode == 40 || opcode == 111 || opcode == 115

/-- A generic parameter's attribute flags and constraint types. -/
structure GenericConstraint where
  flags : Nat
  /-- Closed constraint identities. -/
  types : List String
  /-- Interface constraints naming generic parameters, such as `T : I<T>`, in the method-then-owner
      parameter numbering; each is closed at the instantiation's arguments before it is checked. -/
  interfaces : List TypeExpr := []
  deriving DecidableEq, Repr

/-- The declared class size and extracted storage of an RVA field come from separate PE data. -/
structure RvaField where
  declaredSize : Nat
  descriptor : StaticDescriptor
  deriving DecidableEq, Repr

/-- A method definition as read from metadata: signature, locals and body. -/
structure RawMethod where
  token : Nat
  owner : String
  hasThis : Bool
  explicitThis : Bool
  callingConvention : Nat
  attributes : Nat
  implementation : Nat
  returnType : TypeExpr
  parameters : List TypeExpr
  locals : List TypeExpr
  initLocals : Bool
  maxStack : Nat
  genericParameters : List GenericConstraint
  code : List RawInstruction
  /-- Declaring-type constraints follow method constraints in the substitution environment. -/
  ownerParameters : List GenericConstraint := []
  /-- Closed bodies retain the owner arity after their parameter constraints are discharged. -/
  ownerArgumentCount : Nat := 0
  /-- The declaring type is a class, so `this` is an object reference rather than a byref. -/
  objectReceiver : Bool := false
  /-- The instance field count of a class declaring type, its bases' fields included; each field
      takes one model slot. -/
  objectFieldCount : Nat := 0
  /-- The admitted base classes of a class declaring type, nearest first. -/
  objectBases : List TypeExpr := []
  /-- Each RVA access carries its field, immutable bytes and declared packing at its pc. -/
  rvaSites : List (Nat × RvaField) := []
  deriving DecidableEq, Repr

/-- Close metadata storage after substitution without changing callable owner expressions. -/
def substituteStorageType (layouts : List RawLayout) (arguments : List TypeExpr)
    (type : TypeExpr) : Option TypeExpr :=
  closeLayoutType layouts <$> substituteType arguments type

/-- The closed type of an operand that names a runtime span also names a runtime span. -/
theorem substituteStorageType_span {layouts : List RawLayout} {arguments : List TypeExpr}
    {original closed : TypeExpr} (span : original.isRuntimeSpan = true)
    (storage : substituteStorageType layouts arguments original = some closed) :
    closed.isRuntimeSpan = true := by
  cases original <;> try cases span
  case apply owner element =>
    change owner.isSpanHead = true at span
    cases owner <;> try cases span
    case constructor scope name =>
      simp only [substituteStorageType, substituteType, Option.pure_def, Option.bind_some,
        Option.map_eq_map, Option.bind_eq_bind] at storage
      cases found : substituteType arguments element <;>
        simp [found, closeLayoutType_span layouts scope name _ span] at storage
      subst closed
      exact span
#print axioms substituteStorageType_span

/-- Whether a type mentions a generic parameter of the method being instantiated. -/
private def mentionsParameter : TypeExpr → Bool
  | .parameter _ => true
  | .byref element | .pointer element | .array element | .enum _ element
  | .modified _ _ _ element =>
    mentionsParameter element
  | .functionPointer result parameters .. | .signatureParameter result parameters =>
    mentionsParameter result || mentionsParameter parameters
  | .apply constructor argument => mentionsParameter constructor || mentionsParameter argument
  | _ => false

/-- A call owner's runtime signature spelling. Parameters below `methodArity` are the method's
    (`!!n`); the rest are the declaring type's (`!n`), as ECMA-335 writes them. -/
def ownerTypeName (methodArity : Nat) : TypeExpr → Option (List Char)
  | .parameter index => some (if index < methodArity then '!' :: '!' :: (toString index).toList
      else '!' :: (toString (index - methodArity)).toList)
  | .aggregate identity _ => aggregateName identity
  | .apply constructor argument => do
    let argument ← ownerTypeName methodArity argument
    match constructor with
    | .apply .. => do
      -- A curried owner `C<A>` applied to `B` is spelled `C<A,B>`.
      let head ← ownerTypeName methodArity constructor
      return head.dropLast ++ ',' :: argument ++ ['>']
    | _ => return (← plainTypeName constructor) ++ '<' :: argument ++ ['>']
  | type => plainTypeName type

/-- Split a reversed identity at its last `::`, returning the member in original order. -/
private def splitMember : List Char → List Char → Option (List Char × List Char)
  | member, ':' :: ':' :: rest => some (member, rest)
  | member, char :: rest => splitMember (char :: member) rest
  | _, [] => none

/-- Split a reversed identity head at its last space, returning the owner in original order. -/
private def splitOwner : List Char → List Char → Option (List Char × List Char)
  | owner, ' ' :: rest => some (owner, rest)
  | owner, char :: rest => splitOwner (char :: owner) rest
  | _, [] => none

/-- The assembly scope of an owner's generic type definition. -/
private def ownerScope : TypeExpr → Option String
  | .constructor scope _ | .objectConstructor scope _ => some scope
  | .apply constructor _ => ownerScope constructor
  | _ => none

/-- An external identity `scope::result owner::member` instantiated at a closed owner. The scope
    is the owner's, the open owner segment must be exactly `openOwner`'s spelling, and no other
    part of the identity changes. Only the unscoped remainder is decoded. -/
def substituteTarget (methodArity : Nat) (openOwner closedOwner : TypeExpr) :
    MethodId → Option MethodId
  | .external identity => do
    let scope ← ownerScope openOwner
    let signature ← stripIdentityPrefix (scope.toByteArray.data.toList ++ [58, 58])
      identity.toByteArray.data.toList
    let (member, head) ← splitMember [] (← asciiChars signature).reverse
    let (owner, front) ← splitOwner [] head
    if owner != (← ownerTypeName methodArity openOwner) then none else
    let closed ← ownerTypeName methodArity closedOwner
    return .external (scope ++ "::" ++
      String.ofList (front.reverse ++ ' ' :: closed ++ ':' :: ':' :: member))
  | target => some target

/-- Substitutes type arguments through every type an operand mentions, including the owner
    instantiation an external call target names. `methodArity` splits method and owner
    parameters. -/
def substituteOperand (arguments : List TypeExpr) (layouts : List RawLayout := [])
    (methodArity : Nat := 0) : RawOperand → Option RawOperand
  | .type type => RawOperand.type <$> substituteStorageType layouts arguments type
  | .field owner index type name isStatic => do
    return .field (← substituteStorageType layouts arguments owner) index
      (← substituteStorageType layouts arguments type) name isStatic
  | .call site => do
    let declaringType ← substituteType arguments site.declaringType
    return .call { site with
      method := { site.method with
        owner := declaringType,
        returnType := ← substituteStorageType layouts arguments site.returnType,
        parameters := ← site.parameterTypes.mapM (substituteStorageType layouts arguments),
        methodArguments :=
          ← site.method.methodArguments.mapM (substituteStorageType layouts arguments) },
      target := ← if mentionsParameter site.declaringType then
        substituteTarget methodArity site.declaringType declaringType site.target
        else pure site.target,
      typeArguments := ← site.typeArguments.mapM (substituteStorageType layouts arguments) }
  | .indirectCall returnType parameters hasThis explicitThis convention => do
    return .indirectCall (← substituteStorageType layouts arguments returnType)
      (← parameters.mapM (substituteStorageType layouts arguments)) hasThis explicitThis convention
  | operand => some operand

/-- A closed, non-reference type argument with a known storage. -/
private def admittedTypeArgument (layouts : List RawLayout) (type : TypeExpr) : Bool :=
  substituteType [] type == some type && match typeStorage layouts type with
    | some .reference | some (.span ..) | some (.aggregateSpan ..) | some (.array _) | none => false
    | some _ => true

/-- A generic type application split into its constructor and ordered arguments. -/
def appliedArguments (type : TypeExpr) : TypeExpr × List TypeExpr := collect type []
where
  /-- Peeled arguments form the suffix after the remaining constructor's own arguments. -/
  collect : TypeExpr → List TypeExpr → TypeExpr × List TypeExpr
    | .apply constructor argument, suffix => collect constructor (argument :: suffix)
    | head, suffix => (head, suffix)

/-- An interface constraint naming generic parameters holds when its closure at `arguments`
    is among the direct interfaces of the constrained argument's layout. -/
def openConstraintValid (layouts : List RawLayout) (arguments : List TypeExpr)
    (argument constraint : TypeExpr) : Bool :=
  match substituteType arguments constraint with
  | none => false
  | some closed =>
    let (owner, ownerArguments) := appliedArguments closed
    match genericOwnerIdentity owner ownerArguments, argument with
    | some identity, .aggregate argumentIdentity index => match layouts[index]? with
      | some layout => layout.identity == argumentIdentity && layout.interfaces.contains identity
      | none => false
    | _, _ => false

/-- Instantiation preserves instruction encodings, offsets and branch targets exactly.
    Explicit receiver signatures have no supported instantiation. -/
def instantiateMethod (layouts : List RawLayout) (original : RawMethod)
    (arguments : List TypeExpr) : Option RawMethod := do
  if original.explicitThis || original.ownerArgumentCount != 0 ||
      arguments.length != original.genericParameters.length + original.ownerParameters.length ||
      !arguments.all (admittedTypeArgument layouts) ||
      !((original.genericParameters ++ original.ownerParameters).zip arguments).all
        (fun (constraint, argument) =>
          genericConstraintValid layouts argument constraint.flags constraint.types &&
            constraint.interfaces.all (openConstraintValid layouts arguments argument)) then none
  else
    let returnType ← substituteStorageType layouts arguments original.returnType
    let parameters ← original.parameters.mapM (substituteStorageType layouts arguments)
    let locals ← original.locals.mapM (substituteStorageType layouts arguments)
    let code ← original.code.mapM fun instruction => do
      let operand ← substituteOperand arguments layouts original.genericParameters.length
        instruction.operand
      return { instruction with operand }
    -- Masking with 239 clears the generic calling-convention bit (0x10).
    return { original with
      returnType, parameters, locals, code, genericParameters := [], ownerParameters := [],
      ownerArgumentCount := original.ownerParameters.length,
      callingConvention := original.callingConvention &&& 239 }

/-- Instantiation keeps the metadata token, so a closed body names the definition it closes. -/
theorem instantiateMethod_token {layouts : List RawLayout} {original closed : RawMethod}
    {arguments : List TypeExpr}
    (instantiated : instantiateMethod layouts original arguments = some closed) :
    closed.token = original.token := by
  unfold instantiateMethod at instantiated
  split at instantiated
  · cases instantiated
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at instantiated
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := instantiated
    rfl

#print axioms instantiateMethod_token

/-- A closed method retains its definition's local initialization flag. -/
theorem instantiateMethod_initLocals {layouts : List RawLayout} {original closed : RawMethod}
    {arguments : List TypeExpr}
    (instantiated : instantiateMethod layouts original arguments = some closed) :
    closed.initLocals = original.initLocals := by
  unfold instantiateMethod at instantiated
  split at instantiated
  · cases instantiated
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at instantiated
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := instantiated
    rfl

#print axioms instantiateMethod_initLocals

/-- Closed argument metadata is derived from this checked body, including short opcodes. -/
def argumentOperation (instruction : RawInstruction) : Option ArgumentOp :=
  match instruction.opcode, instruction.operand with
  -- `ldarg.0` to `ldarg.3`.
  | 2, .none => some (.load 0) | 3, .none => some (.load 1)
  | 4, .none => some (.load 2) | 5, .none => some (.load 3)
  -- `ldarg`, `ldarga` and `starg`, short and long forms.
  | 14, .argument index | 65033, .argument index => some (.load index)
  | 15, .argument index | 65034, .argument index => some (.address index)
  | 16, .argument index | 65035, .argument index => some (.store index)
  -- An argument opcode with a malformed operand is rejected, not treated as `other`.
  | opcode, _ =>
    if opcode ∈ [2, 3, 4, 5, 14, 15, 16, 65033, 65034, 65035] then none else some .other

/-- Whether `instruction` names `pc` as a branch destination or switch arm. -/
def branchesTo (pc : Nat) (instruction : RawInstruction) : Bool :=
  match instruction.operand with
  | .target target => target == pc
  | .targets targets => targets.contains pc
  | _ => false

/-- All decoded branch destinations, including switch arms and unreachable instructions. -/
def branchTargets (raw : List RawInstruction) : List Nat :=
  raw.flatMap fun instruction => match instruction.operand with
    | .target target => [target]
    | .targets targets => targets
    | _ => []

/-- Collecting branch destinations once answers, for every pc, whether some instruction
    branches to it. -/
theorem branchTargets_contains (raw : List RawInstruction) (pc : Nat) :
    (branchTargets raw).contains pc = raw.any (branchesTo pc) := by
  induction raw with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction with
    | mk offset opcode operand =>
      change _ = (branchesTo pc ⟨offset, opcode, operand⟩ || rest.any (branchesTo pc))
      simp only [branchTargets, List.flatMap_cons, List.contains_append]
      change (_ || (branchTargets rest).contains pc) = _
      rw [ih]
      cases operand <;> simp [branchesTo, BEq.beq, eq_comm]

#print axioms branchTargets_contains

/-- The unique raw managed indirect signature and native locals directly consumed as targets. -/
structure NativeDispatchContext where
  signature : Option ManagedSignature := none
  pointerLocals : List Nat := []
  deriving DecidableEq, Repr

/-- Native integer metadata eligible for an authenticated table element. -/
def nativeDispatchInteger : TypeExpr → Bool
  | .atom scope name => scope == runtimeScope && name ∈ ["System.IntPtr", "System.UIntPtr"]
  | _ => false

/-- Derive callable homes from raw call sites, never from emitted kinds or numerical values. -/
def nativeDispatchContext (raw : RawMethod) : NativeDispatchContext := Id.run do
  let mut signature : Option ManagedSignature := none
  let mut locals := []
  let mut previous : Option RawInstruction := none
  for instruction in raw.code do
    if instruction.opcode == 41 then
      let .indirectCall result parameters false false 0 := instruction.operand | return {}
      let current : ManagedSignature := ⟨callableType result, parameters.map callableType⟩
      if managedSignature current.typeExpr != some current then return {}
      if let some expected := signature then
        if expected != current then return {}
      signature := some current
      if let some before := previous then
        if before.opcode ∈ [6, 7, 8, 9] then locals := (before.opcode - 6) :: locals
        else if before.opcode ∈ [17, 65036] then
          if let .local index := before.operand then locals := index :: locals
    if instruction.opcode != 65044 then previous := some instruction
  return ⟨signature, locals⟩

/-- A native pointer is an input table view; only raw target-feeding integer locals, those
    `pointer` holds, are callable. -/
def nativeDispatchStorage (context : NativeDispatchContext) (type : TypeExpr)
    (localIndex : Option Nat := none) (pointer : Nat → Bool := context.pointerLocals.contains) :
    Option StorageType := do
  let signature ← context.signature
  if let .pointer element := type then
    if nativeDispatchInteger element then return .methodTable signature
  if nativeDispatchInteger type && localIndex.any pointer then
    return .methodPointer signature
  none

/-- Closed argument and local storage, including typed span views, and argument accesses, where
    `pointer` holds the locals a `calli` consumes. -/
def closedArgumentsWith (layouts : List RawLayout) (closed : RawMethod)
    (context : NativeDispatchContext) (pointer : Nat → Bool) : Option RawArguments := do
  let parameters ← closed.parameters.mapM fun type =>
    nativeDispatchStorage context type <|> typeStorage layouts type
  let locals ← closed.locals.zipIdx.mapM fun (type, index) =>
    nativeDispatchStorage context type (some index) pointer <|> typeStorage layouts type
  let code ← closed.code.mapM argumentOperation
  let receiver := if closed.objectReceiver then StorageType.object else .reference
  return ⟨(if closed.hasThis then [receiver] else []) ++ parameters, locals, code⟩

/-- Closed argument and local storage, including typed span views, and argument accesses, with
    the locals a `calli` consumes read from a `Std.TreeSet` built once per body. -/
def closedArguments (layouts : List RawLayout) (closed : RawMethod) : Option RawArguments :=
  let context := nativeDispatchContext closed
  closedArgumentsWith layouts closed context
    (Std.TreeSet.ofList context.pointerLocals compare).contains

/-- Reading pointer locals from a set built once gives exactly the storage that scanning the
    pointer local list at each local gives. -/
theorem closedArguments_eq_list (layouts : List RawLayout) (closed : RawMethod) :
    closedArguments layouts closed = closedArgumentsWith layouts closed
      (nativeDispatchContext closed) (nativeDispatchContext closed).pointerLocals.contains := by
  have pointer : (Std.TreeSet.ofList (nativeDispatchContext closed).pointerLocals
      compare).contains = (nativeDispatchContext closed).pointerLocals.contains := by
    funext index
    rw [Std.TreeSet.contains_ofList]
  dsimp only [closedArguments]
  rw [pointer]

#print axioms closedArguments_eq_list

/-- `closed` is `original` instantiated at `arguments`, and `parameterInput` is the
    argument metadata derived from it. -/
def SpecializationValid (layouts : List RawLayout) (original : RawMethod)
    (arguments : List TypeExpr) (closed : RawMethod) (parameterInput : RawArguments) : Prop :=
  instantiateMethod layouts original arguments = some closed ∧
  closedArguments layouts closed = some parameterInput

instance (layouts : List RawLayout) (original : RawMethod) (arguments : List TypeExpr)
    (closed : RawMethod) (parameterInput : RawArguments) :
    Decidable (SpecializationValid layouts original arguments closed parameterInput) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem validated_specialization {layouts : List RawLayout} {original closed : RawMethod}
    {arguments : List TypeExpr} {parameterInput : RawArguments}
    (valid : SpecializationValid layouts original arguments closed parameterInput) :
    instantiateMethod layouts original arguments = some closed := valid.1

theorem validated_closed_arguments {layouts : List RawLayout} {original closed : RawMethod}
    {arguments : List TypeExpr} {parameterInput : RawArguments}
    (valid : SpecializationValid layouts original arguments closed parameterInput) :
    closedArguments layouts closed = some parameterInput := valid.2


/-- One entry of the program's method table: the type arguments and closed body of the
    extracted method at that index. -/
structure SpecializedMethod where
  arguments : List TypeExpr
  closed : RawMethod
  deriving DecidableEq, Repr

/-- The callee index and argument count of an emitted call, if its kind matches the raw
    opcode: `call` (40) for `.call`, whose callee is the `.direct` link of its pc, and `callvirt`
    (111) for a receiver-checked call. -/
private def managedCallTarget (opcode : Nat) (link : Option Link) :
    Instruction → Option (Nat × Nat)
  | .call method _ => match link with
    | some (.direct target) => if opcode = 40 then some (target, method.argumentCount) else none
    | _ => none
  | .callvirt method => match link with
    | some (.direct target) => if opcode = 111 then some (target, method.argumentCount) else none
    | _ => none
  | _ => none

/-- A `call` names the method its raw operand names, unless a `constrained.` prefix lowered the
    operand to the resolved implementation; the constrained-call check ties that operand. -/
def callOperandMatches (site : CallSite) : Instruction → Bool
  | .call method prefixes => prefixes.constrained.isSome || method == site.method
  | .callvirt method => method == site.method
  | _ => true

/-- Split a scoped declaring type from its ordered generic arguments. -/
def managedOwner : TypeExpr → Option (String × List TypeExpr)
  | .atom scope name | .constructor scope name | .objectConstructor scope name
  | .object scope name => some (scope ++ "::" ++ name, [])
  | .aggregate identity _ => some (identity, [])
  | .apply owner argument => do
    let (identity, arguments) ← managedOwner owner
    return (identity, arguments ++ [argument])
  | _ => none

/-- Owner arguments occupy the suffix after method arguments, with independently checked arity. -/
def managedOwnerMatches (site : CallSite) (owner : String) (ownerCount : Nat) : Bool :=
  match managedOwner site.declaringType with
  | some (identity, arguments) => identity == owner && ownerCount == site.ownerArgumentCount &&
    arguments.length == ownerCount && ownerCount ≤ site.typeArguments.length &&
    site.typeArguments.drop (site.typeArguments.length - ownerCount) == arguments
  | none => false

/-- `callee` is the extracted method a managed site with metadata token `token` names: the same
    owner with its type arguments, token, method type arguments and declared signature. -/
def calleeMatchesSite (site : CallSite) (token : Nat) (callee : SpecializedMethod) : Bool :=
  managedOwnerMatches site callee.closed.owner callee.closed.ownerArgumentCount &&
  callee.closed.token == token && callee.arguments == site.typeArguments &&
  callee.closed.parameters.length == site.parameterCount &&
  callee.closed.hasThis == site.hasThis &&
  (callee.closed.returnType != .void) == site.returnsValue &&
  callee.closed.returnType == site.returnType &&
  callee.closed.parameters == site.parameterTypes

/-- What a live `newobj` of `constructor` may be linked to. Its raw instruction is `newobj` (115)
    of a managed site naming `constructor`, and the linked method is the one the site names. A
    value-type constructor, whose owner is no class and whose receiver is no object, is linked
    `.aggregate`; a class constructor taking its instance as object receiver is linked `.object`
    with the class's bases and one slot per instance field. A dead site passes. -/
def validateConstructionWith (methods : Nat → Option SpecializedMethod) (raw : RawInstruction)
    (live : Bool) (link : Option Link) (constructor : MethodRef) : Bool :=
  if !live then true else
  match link with
  | none => false
  | some link =>
    let isClass := match constructor.owner with | .object .. => true | _ => false
    raw.opcode == 115 && match raw.operand with
    | .call site => site.method == constructor && match site.target with
      | .managed token => match link with
        | .aggregate index _ => match methods index with
          | some callee => calleeMatchesSite site token callee && !isClass &&
            !callee.closed.objectReceiver
          | none => false
        | .object index bases size => match methods index with
          | some callee => calleeMatchesSite site token callee && isClass &&
            callee.closed.objectReceiver && bases == callee.closed.objectBases &&
            size == objectFieldOffset callee.closed.objectFieldCount
          | none => false
        | _ => false
      | .external _ => false
    | _ => false


/-- The `Virtual` flag of a method's metadata attributes (ECMA-335 II.23.1.10). -/
def virtualMethodAttribute : Nat := 0x40

/-- Whether a method's metadata marks it virtual, so `callvirt` selects its body by runtime type. -/
def RawMethod.isVirtual (method : RawMethod) : Bool :=
  method.attributes &&& virtualMethodAttribute != 0

/-- A receiver-checked call enters a non-virtual method of an admitted class, whose receiver is an
    object reference; no other managed call checks its receiver. A virtual callee would need
    dispatch, which one fixed target does not perform. -/
def checkedReceiverMatches (callee : RawMethod) : Instruction → Bool
  | .callvirt .. => callee.objectReceiver && !callee.isVirtual
  | _ => true

/-- Legacy slots accept only primitive signatures; new families require exact typed metadata. -/
def importSignatureMatches (slot : ImportSlot) (site : CallSite) : Bool :=
  site.parameterTypes.length == site.parameterCount &&
  (site.returnType != .void) == site.returnsValue &&
  match slot.signature with
  | none => site.typeArguments.isEmpty &&
    ImportSignature.supported ⟨site.declaringType, site.name, [], site.returnType,
      site.parameterTypes⟩ []
  | some signature =>
    signature.owner == site.declaringType && signature.name == site.name &&
    signature.arguments == site.typeArguments && signature.returnType == site.returnType &&
    signature.parameters == site.parameterTypes && signature.supported slot.layouts.actual

/-- An external call must bind exact instance metadata as well as identity and arity. -/
def validateImportCallWith (methodCount : Nat) (imports : Nat → Option ImportSlot)
    (opcode : Nat) (site : CallSite) (identity : String) (target count : Nat) : Bool :=
  opcode == 40 && methodCount ≤ target && match imports (target - methodCount) with
  | none => false
  | some slot =>
    slot.identity == identity && slot.parameterCount == site.parameterCount &&
    slot.hasThis == site.hasThis && slot.returnsValue == site.returnsValue &&
    count == site.parameterCount + (if site.hasThis then 1 else 0) &&
      importSignatureMatches slot site

/-- A callable catalog entry binds stable metadata and its signature to one extracted body. -/
def managedTargetMatches (methods : Nat → Option SpecializedMethod)
    (signature : ManagedSignature) (target : ManagedTarget) : Bool :=
  match methods target.method with
  | none => false
  | some callee =>
    target.identity.owner == callee.closed.owner &&
    target.identity.token == callee.closed.token &&
    target.identity.arguments == callee.arguments.map callableType &&
    !callee.closed.hasThis && !callee.closed.explicitThis && callee.closed.callingConvention == 0 &&
    callableType callee.closed.returnType == signature.result &&
    callee.closed.parameters.map callableType == signature.parameters &&
    managedSignature signature.typeExpr == some signature

/-- Exact function address evidence; integer constants cannot acquire callable provenance. -/
def managedAddressMatches (methods : Nat → Option SpecializedMethod)
    (raw : RawInstruction) (target : ManagedTarget) (signature : ManagedSignature) : Bool :=
  raw.opcode == 65030 && managedTargetMatches methods signature target &&
  match raw.operand with
  | .call site => site.target == .managed target.identity.token &&
    (match methods target.method with
      | some callee => managedOwnerMatches site target.identity.owner callee.closed.ownerArgumentCount &&
        site.typeArguments == callee.arguments &&
        site.returnType == callee.closed.returnType && site.parameterTypes == callee.closed.parameters
      | none => false) &&
    site.typeArguments.map callableType == target.identity.arguments && !site.hasThis &&
    callableType site.returnType == signature.result &&
    site.parameterTypes.map callableType == signature.parameters &&
    site.parameterCount == signature.parameters.length &&
    site.returnsValue == (signature.result != .void)
  | _ => false

/-- Indirect calls bind the exact raw managed signature and every possible selected target. -/
def managedIndirectMatches (methods : Nat → Option SpecializedMethod)
    (raw : RawInstruction) (signature : ManagedSignature) (catalog : List ManagedTarget) : Bool :=
  raw.opcode == 41 && !catalog.isEmpty &&
    (catalog.map (·.identity)).Nodup &&
  match raw.operand with
  | .indirectCall result parameters false false 0 =>
    callableType result == signature.result && parameters.map callableType == signature.parameters &&
    catalog.all fun target => managedTargetMatches methods signature target &&
      match methods target.method with
      | some callee => result == callee.closed.returnType && parameters == callee.closed.parameters
      | none => false
  | _ => false

/-- Every live managed call must select the independently instantiated definition
with the exact substituted type arguments and signature; an external one, a matching import slot.
`link` is the link of the call's pc, which names the body a `call` enters. -/
def validateManagedCallWith (methodCount : Nat)
    (methods : Nat → Option SpecializedMethod) (imports : Nat → Option ImportSlot)
    (raw : RawInstruction) (live : Bool) (link : Option Link) (emitted : Instruction) : Bool :=
  if !live then true else
  match emitted, link with
  | .managed (.address identity signature), some (.address index) =>
    managedAddressMatches methods raw ⟨identity, index⟩ signature
  | .managed (.call signature _), some (.indirect catalog) =>
    managedIndirectMatches methods raw signature catalog
  | .managed _, _ => false
  -- Each listed body is a virtual instance method of a class with the slot's signature; which
  -- body each class selects is checked against the dispatch catalog.
  | .callvirt method, some (.virtual targets) => match raw.operand with
    | .call site => raw.opcode == 111 && method == site.method && site.hasThis &&
      !targets.isEmpty && (match site.target with | .managed _ => true | .external _ => false) &&
      method.argumentCount == site.parameterCount + 1 &&
      targets.all fun (_, index) => match methods index with
        | some callee => callee.arguments.isEmpty && callee.closed.objectReceiver &&
          callee.closed.hasThis && callee.closed.isVirtual &&
          callee.closed.parameters == site.parameterTypes &&
          callee.closed.returnType == site.returnType
        | none => false
    | _ => false
  -- A live construction is checked with its link by `validateConstructionWith`; without the link
  -- it passes nothing.
  | .newobj _, _ => false
  | _, _ =>
  match raw.operand with
  | .call site => match site.target with
    | .managed token => match managedCallTarget raw.opcode link emitted with
      | none => false
      | some (target, count) => match methods target with
        | none => false
        | some callee =>
          calleeMatchesSite site token callee &&
          count == site.parameterCount + (if site.hasThis then 1 else 0) &&
          checkedReceiverMatches callee.closed emitted && callOperandMatches site emitted
    | .external identity => match emitted, link with
      | .call method prefixes, some (.direct target) =>
        !prefixes.tail && prefixes.constrained.isNone && method == site.method &&
          validateImportCallWith methodCount imports raw.opcode site identity target
            method.argumentCount
      | .call .., _ | .callvirt .., _ => false
      | _, _ => true
  | .indirectCall .. => false
  | _ => match emitted with
    | .call .. | .callvirt .. => false
    | _ => true

/-- Link kinds for receiver calls, managed addresses and indirect calls. -/
private def operandLinkFits (emitted : Instruction) (link : Option Link) : Bool :=
  match emitted, link with
  | .callvirt _, some (.direct _) | .callvirt _, some (.virtual _)
  | .managed (.address ..), some (.address _) | .managed (.call ..), some (.indirect _) => true
  | .callvirt _, _ | .managed _, _ => false
  | _, _ => link.isNone

/-- The link kind permitted at an instruction other than a construction. -/
def _root_.CIL.Instruction.linkFits (modelled : MethodRef → Bool) (emitted : Instruction)
    (link : Option Link) : Bool :=
  match emitted with
  | .call method _ => match link with
    | some (.direct _) => !modelled method
    | none => modelled method
    | some _ => false
  | _ => operandLinkFits emitted link

/-- A live call that states no link keeps the call its raw site makes: a `call` of an external
    method, naming the site's own method, with no prefix. A dead one passes. -/
def validateModelCall (raw : RawInstruction) (live : Bool) (emitted : Instruction) : Bool :=
  !live || match raw.opcode, raw.operand, emitted with
  | 40, .call site, .call method prefixes =>
    (site.target matches .external _) && method == site.method && !prefixes.tail &&
      prefixes.constrained.isNone
  | _, _, _ => false

/-- Whether `raw` is a `call` of a method that `modelled` gives a runtime model. -/
def modelledCallSite (modelled : MethodRef → Bool) (raw : RawInstruction) : Bool :=
  match raw.opcode, raw.operand with
  | 40, .call site => modelled site.method
  | _, _ => false

/-- `link` is what the method's link table gives this pc. A construction is checked with it by
    `validateConstructionWith`. Any other instruction must fit it, live or not, so a key sits only
    at a call-family pc, a call has one exactly when `modelled` gives its method no model,
    and every other call-family pc has one. A call without a link must pass
    `validateModelCall`, and any other instruction `validateManagedCallWith` with its link; a
    live call of a modelled method emits nothing but its call. -/
def validateLinkedCallWith (modelled : MethodRef → Bool) (methodCount : Nat)
    (methods : Nat → Option SpecializedMethod) (imports : Nat → Option ImportSlot)
    (raw : RawInstruction) (live : Bool) (link : Option Link) (emitted : Instruction) : Bool :=
  match emitted.constructor? with
  | some constructor => validateConstructionWith methods raw live link constructor
  | none =>
    -- The arms decide `Instruction.linkFits` in the same match, since a second match on the
    -- instruction costs the kernel about 700 heartbeats at every pc.
    match emitted, link with
    | .call method _, none => modelled method && validateModelCall raw live emitted
    | .call method _, some (.direct _) => !modelled method &&
        ((!live || !modelledCallSite modelled raw) &&
          validateManagedCallWith methodCount methods imports raw live link emitted)
    | .call .., some _ => false
    | _, _ => operandLinkFits emitted link &&
        ((!live || !modelledCallSite modelled raw) &&
          validateManagedCallWith methodCount methods imports raw live link emitted)

/-- A pc other than a construction that passes the linked call rule fits its link. -/
theorem validateLinkedCallWith_linkFits {modelled : MethodRef → Bool} {methodCount : Nat}
    {methods : Nat → Option SpecializedMethod} {imports : Nat → Option ImportSlot}
    {raw : RawInstruction} {live : Bool} {link : Option Link} {emitted : Instruction}
    (unnamed : emitted.constructor? = none)
    (checked : validateLinkedCallWith modelled methodCount methods imports raw live link emitted =
      true) :
    emitted.linkFits modelled link = true := by
  simp only [validateLinkedCallWith, unnamed] at checked
  split at checked
  · simp only [Bool.and_eq_true] at checked
    simp [Instruction.linkFits, checked.1]
  · simp only [Bool.and_eq_true] at checked
    simp [Instruction.linkFits, checked.1]
  · simp at checked
  · rename_i noModel _ noOther
    simp only [Bool.and_eq_true] at checked
    unfold Instruction.linkFits
    split
    · cases link with
      | none => exact (noModel _ _ rfl rfl).elim
      | some _ => exact (noOther _ _ _ rfl rfl).elim
    · exact checked.1

#print axioms validateLinkedCallWith_linkFits

/-- The external-call rule stated against the original lists, including bounds and offset. -/
def validateImportCall (methods : List SpecializedMethod) (imports : List ImportSlot)
    (opcode : Nat) (site : CallSite) (identity : String) (target count : Nat) : Bool :=
  validateImportCallWith methods.length (imports[·]?) opcode site identity target count

/-- The call rule stated against the original lists for use in semantic consequences. -/
def validateManagedCall (methods : List SpecializedMethod) (imports : List ImportSlot)
    (raw : RawInstruction) (live : Bool) (link : Option Link) (emitted : Instruction) : Bool :=
  validateManagedCallWith methods.length (methods[·]?) (imports[·]?) raw live link emitted

/-- The linked call rule stated against the original lists. -/
def validateLinkedCall (modelled : MethodRef → Bool) (methods : List SpecializedMethod)
    (imports : List ImportSlot) (raw : RawInstruction) (live : Bool) (link : Option Link)
    (emitted : Instruction) : Bool :=
  validateLinkedCallWith modelled methods.length (methods[·]?) (imports[·]?) raw live link
    emitted

/-- The emitted links have ascending, in-range keys. Each live `ldftn` requires an `.address`
    link binding its identity to its method. Each `calli` checks its indirect catalog, and
    each live construction checks its constructor link. A modelled `call` keeps its external
    operand and has no link. Other emitted calls bind to the method table or an import slot.
    An external site may instead emit a non-call translation checked by other validators. -/
def ManagedCallsValid (methods : List SpecializedMethod) (imports : List ImportSlot)
    (modelled : MethodRef → Bool) (raw : RawMethod) (reachable : List Bool) (emitted : Method) :
    Prop :=
  keysAscend 0 emitted.links = true ∧
  emitted.links.all (fun entry => decide (entry.1 < emitted.code.length)) = true ∧
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
  all3 (fun instruction (live, link) op => validateLinkedCallWith modelled methods.length
      (FlowIndex.ofList methods).get? (FlowIndex.ofList imports).get? instruction live link op)
    raw.code (reachable.zip (linkWalk emitted.links emitted.links 0
      (List.range emitted.code.length))) emitted.code = true

/-- The check accepts exactly the bodies whose instructions pass the list-indexed rules with the
    link a scan of the table gives each pc: indexed lookups and links read beside the code lose
    no evidence the scans accept and admit none they reject. -/
theorem ManagedCallsValid_iff_original (methods : List SpecializedMethod)
    (imports : List ImportSlot) (modelled : MethodRef → Bool) (raw : RawMethod)
    (reachable : List Bool) (emitted : Method) :
    ManagedCallsValid methods imports modelled raw reachable emitted ↔
      keysAscend 0 emitted.links = true ∧
      emitted.links.all (fun entry => decide (entry.1 < emitted.code.length)) = true ∧
      raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
      all3 (fun instruction (live, link) op => validateLinkedCallWith modelled methods.length
          (methods[·]?) (imports[·]?) instruction live link op)
        raw.code (reachable.zip ((List.range emitted.code.length).map emitted.linkAt))
        emitted.code = true := by
  have index {α : Type} (values : List α) :
      (FlowIndex.ofList values).get? = (values[·]?) := by
    funext target
    exact FlowIndex.get?_ofList values target
  have reads (ascending : keysAscend 0 emitted.links = true) :
      linkWalk emitted.links emitted.links 0 (List.range emitted.code.length) =
        (List.range emitted.code.length).map emitted.linkAt :=
    linkWalk_eq _ ascending _ _ 0 (dropBelow_zero _).symm
  unfold ManagedCallsValid
  rw [index, index]
  constructor
  · rintro ⟨ascending, rest⟩
    rw [reads ascending] at rest
    exact ⟨ascending, rest⟩
  · rintro ⟨ascending, rest⟩
    rw [reads ascending]
    exact ⟨ascending, rest⟩

#print axioms ManagedCallsValid_iff_original

/-- An admitted body gives every pc of an instruction other than a construction a link the
    instruction fits: no link at a `call` of a modelled method, a `.direct` link at any other
    `call` and the link its program index implies elsewhere, so a step of such an instruction
    never takes the `unlinkedCall` branch for want of a link. -/
theorem ManagedCallsValid.linkFits {methods : List SpecializedMethod}
    {imports : List ImportSlot} {modelled : MethodRef → Bool} {raw : RawMethod}
    {reachable : List Bool} {emitted : Method}
    (valid : ManagedCallsValid methods imports modelled raw reachable emitted) {pc : Nat}
    {op : Instruction} (found : emitted.code[pc]? = some op) (implied : op.constructs = false) :
    op.linkFits modelled (emitted.linkAt pc) = true := by
  obtain ⟨_, _, statesLength, codeLength, checks⟩ :=
    (ManagedCallsValid_iff_original _ _ _ _ _ _).mp valid
  have inside : pc < emitted.code.length := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨instruction, rawFound⟩ :
      ∃ instruction, raw.code[pc]? = some instruction :=
    ⟨raw.code[pc]'(codeLength ▸ inside), List.getElem?_eq_getElem _⟩
  have liveInside : pc < reachable.length := statesLength ▸ codeLength ▸ inside
  have paired : (reachable.zip ((List.range emitted.code.length).map emitted.linkAt))[pc]? =
      some (reachable[pc], emitted.linkAt pc) := by
    simp [List.getElem?_zip_eq_some, liveInside, inside]
  have checked := all3_at checks rawFound paired found
  have unnamed : op.constructor? = none := by
    simpa [Instruction.constructs] using implied
  exact validateLinkedCallWith_linkFits unnamed checked

#print axioms ManagedCallsValid.linkFits

/-- At a live `call` whose raw operand names managed token `token`, the method its `.direct`
    link enters has that token and the site's type arguments. Its operand passes the name check. -/
theorem ManagedCallsValid.direct_operand {methods : List SpecializedMethod}
    {imports : List ImportSlot} {modelled : MethodRef → Bool} {raw : RawMethod}
    {reachable : List Bool} {emitted : Method}
    (valid : ManagedCallsValid methods imports modelled raw reachable emitted)
    {pc target token : Nat} {method : MethodRef} {prefixes : CallPrefixes}
    {instruction : RawInstruction} {site : CallSite}
    (found : emitted.code[pc]? = some (.call method prefixes))
    (live : reachable[pc]? = some true) (rawFound : raw.code[pc]? = some instruction)
    (operand : instruction.operand = .call site) (managed : site.target = .managed token)
    (linked : emitted.linkAt pc = some (.direct target)) :
    callOperandMatches site (.call method prefixes) = true ∧
    ∃ callee, methods[target]? = some callee ∧ callee.closed.token = token ∧
      callee.arguments = site.typeArguments := by
  obtain ⟨_, _, _, _, checks⟩ := (ManagedCallsValid_iff_original _ _ _ _ _ _).mp valid
  have inside : pc < emitted.code.length := (List.getElem?_eq_some_iff.mp found).1
  have paired : (reachable.zip ((List.range emitted.code.length).map emitted.linkAt))[pc]? =
      some (true, some (.direct target)) := by
    simp [List.getElem?_zip_eq_some, live, inside, linked]
  have checked := all3_at checks rawFound paired found
  simp only [validateLinkedCallWith, Instruction.constructor?, validateManagedCallWith,
    managedCallTarget, operand, managed, Bool.not_true, Bool.false_eq_true, ite_false,
    Bool.and_eq_true] at checked
  obtain ⟨_, _, checked⟩ := checked
  by_cases opcode : instruction.opcode = 40
  · simp only [opcode, ite_true] at checked
    cases selected : methods[target]? with
    | none => simp [selected] at checked
    | some callee =>
      simp only [selected, calleeMatchesSite, Bool.and_eq_true, beq_iff_eq] at checked
      exact ⟨checked.2, callee, rfl, checked.1.1.1.1.1.1.1.1.1.2, checked.1.1.1.1.1.1.1.1.2⟩
  · simp [opcode] at checked

#print axioms ManagedCallsValid.direct_operand

instance (methods : List SpecializedMethod) (imports : List ImportSlot)
    (modelled : MethodRef → Bool) (raw : RawMethod) (reachable : List Bool) (emitted : Method) :
    Decidable (ManagedCallsValid methods imports modelled raw reachable emitted) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Every live pc passes the linked call rule with the link the table gives it. -/
theorem validated_managed_call {methods : List SpecializedMethod} {imports : List ImportSlot}
    {modelled : MethodRef → Bool} {raw : RawMethod} {reachable : List Bool} {emitted : Method}
    (valid : ManagedCallsValid methods imports modelled raw reachable emitted)
    (pc : Fin raw.code.length) :
    validateLinkedCall modelled methods imports raw.code[pc] reachable[pc.val]!
      (emitted.linkAt pc.val) (emitted.code[pc.val]?.getD (.unadmitted 0)) = true := by
  obtain ⟨_, _, statesLength, codeLength, checks⟩ :=
    (ManagedCallsValid_iff_original _ _ _ _ _ _).mp valid
  have live : pc.val < reachable.length := statesLength ▸ pc.isLt
  have present : pc.val < emitted.code.length := codeLength ▸ pc.isLt
  rw [getElem!_pos reachable pc.val live, List.getElem?_eq_getElem present, Option.getD_some]
  have paired : (reachable.zip ((List.range emitted.code.length).map emitted.linkAt))[pc.val]? =
      some (reachable[pc.val], emitted.linkAt pc) := by
    simp [List.getElem?_zip_eq_some, live, present]
  have pass := all3_at checks (List.getElem?_eq_getElem pc.isLt) paired
    (List.getElem?_eq_getElem present)
  exact pass

/-- An accepted live `call` linked past every extracted method is an external site calling a
    slot with its identity and arity. -/
theorem validated_import_call {methods : List SpecializedMethod} {imports : List ImportSlot}
    {raw : RawInstruction} {method : MethodRef} {prefixes : CallPrefixes} {target : Nat}
    (valid : validateManagedCall methods imports raw true (some (.direct target))
      (.call method prefixes) = true)
    (outside : methods.length ≤ target) :
    ∃ site identity slot, raw.operand = .call site ∧ site.target = .external identity ∧
      raw.opcode = 40 ∧ importSignatureMatches slot site = true ∧
      imports[target - methods.length]? = some slot ∧ slot.identity = identity ∧
      slot.parameterCount = site.parameterCount ∧ slot.hasThis = site.hasThis ∧
      slot.returnsValue = site.returnsValue ∧
      method.argumentCount = site.parameterCount + (if site.hasThis then 1 else 0) := by
  obtain ⟨offset, opcode, operand⟩ := raw
  cases operand with
  | call site =>
    obtain ⟨methodRef, declared, name, called, typeArguments, parameterCount, returnsValue,
      ownerArgumentCount⟩ := site
    cases called with
    | managed token =>
      have missing : methods[target]? = none := List.getElem?_eq_none_iff.mpr outside
      simp only [validateManagedCall, validateManagedCallWith, managedCallTarget,
        Bool.not_true, Bool.false_eq_true,
        ite_false] at valid
      by_cases call : opcode = 40 <;> simp [call, missing] at valid
    | external identity =>
      simp only [validateManagedCall, validateManagedCallWith, validateImportCallWith,
        Bool.not_true, Bool.false_eq_true,
        ite_false] at valid
      cases found : imports[target - methods.length]? with
      | none => simp [found] at valid
      | some slot =>
        simp [found] at valid
        obtain ⟨_, ⟨opcode40, _⟩, ⟨⟨⟨⟨⟨same, arity⟩, receiver⟩, result⟩, argc⟩, typed⟩⟩ :=
          valid
        exact ⟨_, identity, slot, rfl, rfl, opcode40, typed, rfl, same, arity, receiver, result,
          argc⟩
  | _ => simp [validateManagedCall, validateManagedCallWith] at valid

/-- Every accepted live `call` is linked to an extracted method or an existing import slot. -/
theorem validated_call_bound {methods : List SpecializedMethod} {imports : List ImportSlot}
    {raw : RawInstruction} {method : MethodRef} {prefixes : CallPrefixes} {target : Nat}
    (valid : validateManagedCall methods imports raw true (some (.direct target))
      (.call method prefixes) = true) :
    target < methods.length + imports.length := by
  by_cases inside : target < methods.length
  · exact Nat.lt_add_right _ inside
  · obtain ⟨_, _, _, _, _, _, _, found, _⟩ := validated_import_call valid (Nat.le_of_not_lt inside)
    have := (List.getElem?_eq_some_iff.mp found).1
    omega

#print axioms validated_specialization
#print axioms validated_closed_arguments
#print axioms validated_managed_call
#print axioms validated_import_call
#print axioms validated_call_bound

end CIL.Extraction
