import CIL.Extraction.Parameters
import CIL.Extraction.FlowIndex
import CIL.Imports

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

/-- The exact `System.Runtime.Intrinsics` assembly identity; `runtimeScope` is in `TypeExpr`. -/
def intrinsicsScope : String :=
  "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

/-- Byte width of an admitted integer vector, bound to both exact runtime type identities. -/
def integerVectorWidth : TypeExpr → Option Nat
  | .apply (.constructor scope name) (.atom elementScope element) =>
    if scope != intrinsicsScope || elementScope != runtimeScope ||
        element ∉ ["System.Byte", "System.Int32", "System.UInt32", "System.Int64",
          "System.UInt64"] then none
    else if name == "System.Runtime.Intrinsics.Vector128`1" then some 16
    else if name == "System.Runtime.Intrinsics.Vector256`1" then some 32
    else if name == "System.Runtime.Intrinsics.Vector512`1" then some 64
    else none
  | _ => none

/-- The field type of a primitive runtime type, by full name. -/
private def primitiveField : String → Option FieldType
  | "System.SByte" => some .signed8 | "System.Byte" => some .unsigned8
  | "System.Boolean" => some .boolean | "System.Int16" => some .signed16
  | "System.UInt16" => some .unsigned16 | "System.Char" => some .character
  | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
  | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
  | "System.IntPtr" => some .nativeInt | "System.UIntPtr" => some .nativeUInt
  | _ => none

/-- The integer types an enum may have as its underlying type. -/
private def enumField : FieldType → Bool
  | .signed8 | .unsigned8 | .signed16 | .unsigned16 | .signed32 | .unsigned32
  | .signed64 | .unsigned64 => true
  | _ => false

/-- Primitive array element identity is derived from the exact runtime metadata scope. -/
def arrayElementType (type : TypeExpr) (aggregateWidth : Nat := 0) : Option ArrayElement :=
  match type with
  | .aggregate identity _ => some (.aggregate identity aggregateWidth)
  | type@(.apply (.constructor _ name) (.atom _ element)) => do
    let width ← integerVectorWidth type
    return .vector (name ++ "<" ++ element ++ ">") width
  | .enum identity (.atom scope name) => do
    if scope != runtimeScope then none else pure ()
    let storage ← match name with
      | "System.SByte" => some EnumStorage.signed8 | "System.Byte" => some .unsigned8
      | "System.Int16" => some .signed16 | "System.UInt16" => some .unsigned16
      | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
      | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
      | _ => none
    return .enumeration identity storage
  | .atom scope name =>
    if scope != runtimeScope then none else match name with
      | "System.SByte" => some .signed8 | "System.Byte" => some .unsigned8
      | "System.Int16" => some .signed16 | "System.UInt16" => some .unsigned16
      | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
      | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
      | "System.IntPtr" => some .nativeInt | "System.UIntPtr" => some .nativeUInt
      | "System.Boolean" => some .boolean | "System.Char" => some .character
      | _ => none
  | _ => none
/-- Primitive/vector widths are intrinsic; aggregate widths come from checked layout uses. -/
def spanElementWidth (type : TypeExpr) (aggregateWidth : Nat := 0) : Option Nat :=
  if let .aggregate .. := type then some aggregateWidth else
  ((arrayElementType type).map ArrayElement.width).orElse (fun _ => integerVectorWidth type)

/-- Exact span metadata, including element width and write capability. -/
def spanStorage (type : TypeExpr) (aggregateWidth : Nat := 0) : Option StorageType :=
  match type with
  | .apply (.constructor scope name) elementType => do
    if scope != runtimeScope ||
        name ∉ ["System.Span`1", "System.ReadOnlySpan`1"] then none else
    let width ← spanElementWidth elementType aggregateWidth
    return .span width (name == "System.Span`1")
  | _ => none

/-- Whether a local has a supported span metadata shape; layouts are validated separately. -/
def spanLocal (type : TypeExpr) : Bool := (spanStorage type).isSome

/-- Callable identities retain scoped aggregate names, independent of layout-table ordering.
    Argument storage still validates the original index against the checked layout metadata. -/
def callableType : TypeExpr → TypeExpr
  | .aggregate identity _ => .aggregate identity 0
  | .byref element => .byref (callableType element)
  | .apply constructor argument => .apply (callableType constructor) (callableType argument)
  | .functionPointer result parameters convention hasThis explicitThis =>
    .functionPointer (callableType result) (callableType parameters) convention hasThis explicitThis
  | .signatureParameter head tail => .signatureParameter (callableType head) (callableType tail)
  | type => type

/-- Function pointers admit checked aggregates, integer vectors and integer/reference types. -/
def managedParameter : TypeExpr → Bool
  | .atom scope name => scope == runtimeScope && (primitiveField name).isSome
  | .enum _ (.atom scope name) => scope == runtimeScope &&
      ((primitiveField name).map enumField).getD false
  | .byref element => match element with
      | .atom .. | .enum .. | .aggregate .. | .apply .. => managedParameter element
      | _ => false
  | .aggregate .. => true
  | type => (integerVectorWidth type).isSome

/-- Decode the ordered parameter chain without accepting another metadata constructor. -/
def managedParameters : TypeExpr → Option (List TypeExpr)
  | .void => some []
  | .signatureParameter head tail => do
    if !managedParameter head then none else pure ()
    return callableType head :: (← managedParameters tail)
  | _ => none

/-- Only the exact static managed convention gives callable provenance. -/
def managedSignature : TypeExpr → Option ManagedSignature
  | .functionPointer result parameters 0 false false => do
    if result != .void && !managedParameter result then none else pure ()
    return ⟨callableType result, ← managedParameters parameters⟩
  | _ => none

/-- Raw callable types must bind every aggregate index before their identity is canonicalized. -/
def callableLayoutsValid (layouts : List RawLayout) : TypeExpr → Bool
  | .aggregate identity index => (layouts[index]?).any (·.identity == identity)
  | .byref element => callableLayoutsValid layouts element
  | .functionPointer result parameters _ _ _ =>
    callableLayoutsValid layouts result && callableLayoutsValid layouts parameters
  | .signatureParameter head tail =>
    callableLayoutsValid layouts head && callableLayoutsValid layouts tail
  | _ => true

/-- Decode storage independently from the exact metadata type identity. -/
def typeStorage (layouts : List RawLayout) : TypeExpr → Option StorageType
  | .atom scope name => if scope = runtimeScope then .field <$> primitiveField name else none
  | .aggregate identity index => do
    let metadata ← layouts[index]?
    if metadata.identity = identity then return .field (.aggregate index) else none
  | .enum _ underlying => do
    let .field kind ← typeStorage layouts underlying | none
    if enumField kind then return .field kind else none
  | .byref _ => some .reference
  | .array (.aggregate identity index) => do
    let metadata ← layouts[index]?
    if metadata.identity == identity then some (.aggregateArray identity index) else none
  | .array element => match managedSignature element with
    | some signature => if callableLayoutsValid layouts element then some (.methodTable signature)
      else none
    | none => StorageType.array <$> arrayElementType element
  | type@(.functionPointer ..) => if callableLayoutsValid layouts type then
      StorageType.methodPointer <$> managedSignature type else none
  | .pointer (.atom scope name) =>
    if scope == runtimeScope && name ∈ ["System.SByte", "System.Byte", "System.Int16",
        "System.UInt16", "System.Int32", "System.UInt32", "System.Int64", "System.UInt64",
        "System.IntPtr", "System.UIntPtr"] then some .reference else none
  | .pointer (.aggregate identity index) => do
    let metadata ← layouts[index]?
    if metadata.identity == identity then some .reference else none
  | .pointer type => if (integerVectorWidth type).isSome then some .reference else none
  | type@(.apply (.constructor scope name) elementType) => do
    if let some storage := spanStorage type then
      if let .aggregate identity index := elementType then
        let metadata ← layouts[index]?
        if metadata.identity != identity then none else
          return .aggregateSpan index (name == "System.Span`1")
      else return storage
    let .atom elementScope element := elementType | none
    if scope != intrinsicsScope || elementScope != runtimeScope ||
        element ∉ ["System.UInt64", "System.Int64", "System.UInt32", "System.Int32",
          "System.Byte", "System.Double", "System.Single"] then none
    else if name = "System.Runtime.Intrinsics.Vector128`1" then some .vector128
    else if name = "System.Runtime.Intrinsics.Vector256`1" then some .vector256
    else if name = "System.Runtime.Intrinsics.Vector512`1" then some .vector512 else none
  | _ => none

/-- A call target: a method of this module by metadata token, or another assembly's
    method by its `scope::signature` identity. -/
inductive MethodId where
  | managed (token : Nat)
  | external (identity : String)
  deriving DecidableEq, Repr

/-- The metadata of a `call` or `newobj` operand, as declared at the call site. -/
structure CallSite where
  declaringType : TypeExpr := .void
  name : String := ""
  target : MethodId
  typeArguments : List TypeExpr
  parameterCount : Nat
  hasThis : Bool
  returnsValue : Bool
  returnType : TypeExpr := .void
  parameterTypes : List TypeExpr := []
  /-- The suffix of `typeArguments` belonging to the declaring type, not the method. -/
  ownerArgumentCount : Nat := 0
  deriving DecidableEq, Repr

/-- A decoded instruction operand. A field operand names its owner type and the field's
    index in the owner's raw layout. -/
inductive RawOperand where
  | none
  | integer (value : Int)
  | text (value : String)
  | argument (index : Nat)
  | local (index : Nat)
  | target (pc : Nat)
  | targets (pcs : List Nat)
  | type (value : TypeExpr)
  | field (owner : TypeExpr) (index : Nat) (type : TypeExpr) (isStatic : Bool)
  | call (site : CallSite)
  | indirectCall (returnType : TypeExpr) (parameters : List TypeExpr)
      (hasThis explicitThis : Bool) (callingConvention : Nat)
  deriving DecidableEq, Repr

/-- One CIL instruction: its byte offset, opcode and operand. Branch operands are
    already instruction indices. -/
structure RawInstruction where
  offset : Nat
  opcode : Nat
  operand : RawOperand
  deriving DecidableEq, Repr

/-- A generic parameter's attribute flags and constraint types. -/
structure GenericConstraint where
  flags : Nat
  types : List String
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
  deriving DecidableEq, Repr

/-- Close metadata storage after substitution without changing callable owner expressions. -/
def substituteStorageType (layouts : List RawLayout) (arguments : List TypeExpr)
    (type : TypeExpr) : Option TypeExpr :=
  closeLayoutType layouts <$> substituteType arguments type

/-- Substitutes type arguments through every type an operand mentions. -/
def substituteOperand (arguments : List TypeExpr) (layouts : List RawLayout := []) :
    RawOperand → Option RawOperand
  | .type type => RawOperand.type <$> substituteStorageType layouts arguments type
  | .field owner index type isStatic => do
    return .field (← substituteStorageType layouts arguments owner) index (← substituteStorageType layouts arguments type)
      isStatic
  | .call site => do
    return .call { site with
      declaringType := ← substituteType arguments site.declaringType,
      typeArguments := ← site.typeArguments.mapM (substituteStorageType layouts arguments),
      returnType := ← substituteStorageType layouts arguments site.returnType,
      parameterTypes := ← site.parameterTypes.mapM (substituteStorageType layouts arguments) }
  | .indirectCall returnType parameters hasThis explicitThis convention => do
    return .indirectCall (← substituteStorageType layouts arguments returnType)
      (← parameters.mapM (substituteStorageType layouts arguments)) hasThis explicitThis convention
  | operand => some operand

/-- A closed, non-reference type argument with a known storage. -/
private def admittedTypeArgument (layouts : List RawLayout) (type : TypeExpr) : Bool :=
  substituteType [] type == some type && match typeStorage layouts type with
    | some .reference | some (.span ..) | some (.aggregateSpan ..) | some (.array _) | none => false
    | some _ => true

/-- Instantiation preserves instruction encodings, offsets and branch targets exactly. -/
def instantiateMethod (layouts : List RawLayout) (original : RawMethod)
    (arguments : List TypeExpr) : Option RawMethod := do
  if original.ownerArgumentCount != 0 ||
      arguments.length != original.genericParameters.length + original.ownerParameters.length ||
      !arguments.all (admittedTypeArgument layouts) ||
      !((original.genericParameters ++ original.ownerParameters).zip arguments).all
        (fun (constraint, argument) =>
          genericConstraintValid layouts argument constraint.flags constraint.types) then none
  else
    let returnType ← substituteStorageType layouts arguments original.returnType
    let parameters ← original.parameters.mapM (substituteStorageType layouts arguments)
    let locals ← original.locals.mapM (substituteStorageType layouts arguments)
    let code ← original.code.mapM fun instruction => do
      return { instruction with operand := ← substituteOperand arguments layouts instruction.operand }
    -- Masking with 239 clears the generic calling-convention bit (0x10).
    return { original with
      returnType, parameters, locals, code, genericParameters := [], ownerParameters := [],
      ownerArgumentCount := original.ownerParameters.length,
      callingConvention := original.callingConvention &&& 239 }

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

/-- A native pointer is an input table view; only raw target-feeding integer locals are callable. -/
def nativeDispatchStorage (context : NativeDispatchContext) (type : TypeExpr)
    (localIndex : Option Nat := none) : Option StorageType := do
  let signature ← context.signature
  if let .pointer element := type then
    if nativeDispatchInteger element then return .methodTable signature
  if nativeDispatchInteger type && localIndex.any context.pointerLocals.contains then
    return .methodPointer signature
  none

/-- Closed argument and local storage, including typed span views, and argument accesses. -/
def closedArguments (layouts : List RawLayout) (closed : RawMethod) : Option RawArguments := do
  let context := nativeDispatchContext closed
  let parameters ← closed.parameters.mapM fun type =>
    nativeDispatchStorage context type <|> typeStorage layouts type
  let locals ← closed.locals.zipIdx.mapM fun (type, index) =>
    nativeDispatchStorage context type (some index) <|> typeStorage layouts type
  let code ← closed.code.mapM argumentOperation
  return ⟨(if closed.hasThis then [.reference] else []) ++ parameters, locals, code⟩

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
    opcode: `call` (40) for `.call`, `newobj` (115) for a construction. -/
private def managedCallTarget (opcode : Nat) : Op → Option (Nat × Nat)
  | .call target count | .tailCall target count =>
    if opcode = 40 then some (target, count) else none
  | .newAggregate target count _ | .newVector256 target count =>
    if opcode = 115 then some (target, count) else none
  | _ => none

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

/-- Split a scoped declaring type from its ordered generic arguments. -/
def managedOwner : TypeExpr → Option (String × List TypeExpr)
  | .atom scope name | .constructor scope name => some (scope ++ "::" ++ name, [])
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
with the exact substituted type arguments and signature; an external one, a matching import slot. -/
def validateManagedCallWith (methodCount : Nat)
    (methods : Nat → Option SpecializedMethod) (imports : Nat → Option ImportSlot)
    (raw : RawInstruction) (live : Bool) (emitted : Op) : Bool :=
  if !live then true else
  match emitted with
  | .managed (.address target signature) => managedAddressMatches methods raw target signature
  | .managed (.call signature catalog _) => managedIndirectMatches methods raw signature catalog
  | _ =>
  match raw.operand with
  | .call site => match site.target with
    | .managed token => match managedCallTarget raw.opcode emitted with
      | none => false
      | some (target, count) => match methods target with
        | none => false
        | some callee =>
          managedOwnerMatches site callee.closed.owner callee.closed.ownerArgumentCount &&
          callee.closed.token == token && callee.arguments == site.typeArguments &&
          callee.closed.parameters.length == site.parameterCount &&
          callee.closed.hasThis == site.hasThis &&
          (callee.closed.returnType != .void) == site.returnsValue &&
          callee.closed.returnType == site.returnType &&
          callee.closed.parameters == site.parameterTypes &&
          count == site.parameterCount + (if raw.opcode == 40 && site.hasThis then 1 else 0)
    | .external identity => match emitted with
      | .call target count =>
        validateImportCallWith methodCount imports raw.opcode site identity target count
      | .tailCall .. | .newAggregate .. | .newVector256 .. => false
      | _ => true
  | .indirectCall .. => false
  | _ => match emitted with
    | .call .. | .tailCall .. | .newAggregate .. | .newVector256 .. => false
    | _ => true

/-- The external-call rule stated against the original lists, including bounds and offset. -/
def validateImportCall (methods : List SpecializedMethod) (imports : List ImportSlot)
    (opcode : Nat) (site : CallSite) (identity : String) (target count : Nat) : Bool :=
  validateImportCallWith methods.length (imports[·]?) opcode site identity target count

/-- The call rule stated against the original lists for use in semantic consequences. -/
def validateManagedCall (methods : List SpecializedMethod) (imports : List ImportSlot)
    (raw : RawInstruction) (live : Bool) (emitted : Op) : Bool :=
  validateManagedCallWith methods.length (methods[·]?) (imports[·]?) raw live emitted

/-- Every call emitted at a live call site of `raw` binds to the method table or an import
    slot, and no other instruction emits a call. An external site may instead emit a
    non-call translation, which other validators check. -/
def ManagedCallsValid (methods : List SpecializedMethod) (imports : List ImportSlot)
    (raw : RawMethod) (reachable : List Bool) (emitted : Method) : Prop :=
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
  all3 (validateManagedCallWith methods.length (FlowIndex.ofList methods).get?
    (FlowIndex.ofList imports).get?) raw.code reachable emitted.code = true

/-- Indexed call lookup preserves every metadata check and rejects the same invalid targets. -/
theorem ManagedCallsValid_iff_original (methods : List SpecializedMethod)
    (imports : List ImportSlot) (raw : RawMethod) (reachable : List Bool) (emitted : Method) :
    ManagedCallsValid methods imports raw reachable emitted ↔
      raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
        all3 (validateManagedCall methods imports) raw.code reachable emitted.code = true := by
  have index {α : Type} (values : List α) :
      (FlowIndex.ofList values).get? = (values[·]?) := by
    funext target
    exact FlowIndex.get?_ofList values target
  unfold ManagedCallsValid
  rw [index, index]
  rfl

#print axioms ManagedCallsValid_iff_original

instance (methods : List SpecializedMethod) (imports : List ImportSlot) (raw : RawMethod)
    (reachable : List Bool) (emitted : Method) :
    Decidable (ManagedCallsValid methods imports raw reachable emitted) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Checks generated call bindings structurally, retaining kernel decision for residual checks.
    Reflexive metadata comparisons use equality proofs instead of re-evaluating strings. -/
macro "cil_managed_calls" "[" facts:term,* "]" : tactic =>
  `(tactic| first
    | (apply (ManagedCallsValid_iff_original _ _ _ _ _).mpr
       refine ⟨?_, ?_, ?_⟩
       · rfl
       · rfl
       · simp [all3, validateManagedCall, validateManagedCallWith, managedCallTarget,
           $[$facts:term],*] <;>
           decide +kernel)
    | decide +kernel)

theorem validated_managed_call {methods : List SpecializedMethod} {imports : List ImportSlot}
    {raw : RawMethod} {reachable : List Bool} {emitted : Method}
    (valid : ManagedCallsValid methods imports raw reachable emitted) (pc : Fin raw.code.length) :
    validateManagedCall methods imports raw.code[pc] reachable[pc.val]!
      (emitted.code[pc.val]?.getD (.unsupported "Missing instruction")) = true := by
  have valid := (ManagedCallsValid_iff_original _ _ _ _ _).mp valid
  have live : pc.val < reachable.length := valid.1 ▸ pc.isLt
  have present : pc.val < emitted.code.length := valid.2.1 ▸ pc.isLt
  rw [getElem!_pos reachable pc.val live, List.getElem?_eq_getElem present, Option.getD_some]
  exact all3_at valid.2.2 (List.getElem?_eq_getElem pc.isLt) (List.getElem?_eq_getElem live)
    (List.getElem?_eq_getElem present)

/-- An accepted live `call` past every extracted method is an external site calling a slot
    with its identity and arity. -/
theorem validated_import_call {methods : List SpecializedMethod} {imports : List ImportSlot}
    {raw : RawInstruction} {target count : Nat}
    (valid : validateManagedCall methods imports raw true (.call target count) = true)
    (outside : methods.length ≤ target) :
    ∃ site identity slot, raw.operand = .call site ∧ site.target = .external identity ∧
      raw.opcode = 40 ∧ importSignatureMatches slot site = true ∧
      imports[target - methods.length]? = some slot ∧ slot.identity = identity ∧
      slot.parameterCount = site.parameterCount ∧ slot.hasThis = site.hasThis ∧
      slot.returnsValue = site.returnsValue ∧
      count = site.parameterCount + (if site.hasThis then 1 else 0) := by
  obtain ⟨offset, opcode, operand⟩ := raw
  cases operand with
  | call site =>
    obtain ⟨declaringType, name, method, typeArguments, parameterCount, hasThis, returnsValue,
      returnType, parameterTypes, ownerArgumentCount⟩ := site
    cases method with
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
        obtain ⟨⟨opcode40, _⟩, ⟨⟨⟨⟨⟨same, arity⟩, receiver⟩, result⟩, argc⟩, typed⟩⟩ := valid
        exact ⟨_, identity, slot, rfl, rfl, opcode40, typed, rfl, same, arity, receiver, result,
          argc⟩
  | _ => simp [validateManagedCall, validateManagedCallWith] at valid

/-- Every accepted live `call` targets an extracted method or an existing import slot. -/
theorem validated_call_bound {methods : List SpecializedMethod} {imports : List ImportSlot}
    {raw : RawInstruction} {target count : Nat}
    (valid : validateManagedCall methods imports raw true (.call target count) = true) :
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
