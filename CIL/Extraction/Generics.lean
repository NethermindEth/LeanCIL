import CIL.Extraction.Parameters
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

/-- Exact primitive span metadata, including element width and write capability. -/
def spanStorage : TypeExpr → Option StorageType
  | .apply (.constructor scope name) (.atom elementScope element) => do
    if scope != runtimeScope || elementScope != runtimeScope ||
        name ∉ ["System.Span`1", "System.ReadOnlySpan`1"] then none else
    let width ← match element with
      | "System.Byte" | "System.SByte" => some 1
      | "System.Int16" | "System.UInt16" => some 2
      | "System.Int32" | "System.UInt32" => some 4
      | "System.Int64" | "System.UInt64" => some 8
      | _ => none
    return .span width (name == "System.Span`1")
  | _ => none

/-- Whether a local is a supported primitive span. -/
def spanLocal (type : TypeExpr) : Bool := (spanStorage type).isSome

/-- Primitive array element identity is derived from the exact runtime metadata scope. -/
def arrayElementType : TypeExpr → Option ArrayElement
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
  | .array element => StorageType.array <$> arrayElementType element
  | .pointer (.atom scope name) =>
    if scope == runtimeScope && name ∈ ["System.SByte", "System.Byte", "System.Int16",
        "System.UInt16", "System.Int32", "System.UInt32", "System.Int64", "System.UInt64",
        "System.IntPtr", "System.UIntPtr"] then some .reference else none
  | type@(.apply (.constructor scope name) (.atom elementScope element)) =>
    if let some storage := spanStorage type then some storage else
    if scope != intrinsicsScope || elementScope != runtimeScope ||
        element ∉ ["System.UInt64", "System.Int64", "System.UInt32", "System.Int32",
          "System.Byte", "System.Double", "System.Single"] then none
    else if name = "System.Runtime.Intrinsics.Vector128`1" then some .vector128
    else if name = "System.Runtime.Intrinsics.Vector256`1" then some .vector256
    else if name = "System.Runtime.Intrinsics.Vector512`1" then some .vector512 else none
  | _ => none

/-- Structural substitution includes nested type constructors, not just signature strings. -/
def substituteType (arguments : List TypeExpr) : TypeExpr → Option TypeExpr
  | .parameter index => arguments[index]?
  | .byref element => TypeExpr.byref <$> substituteType arguments element
  | .pointer element => TypeExpr.pointer <$> substituteType arguments element
  | .array element => TypeExpr.array <$> substituteType arguments element
  | .enum identity underlying => TypeExpr.enum identity <$> substituteType arguments underlying
  | .apply constructor argument => do
    return .apply (← substituteType arguments constructor) (← substituteType arguments argument)
  | type => some type

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
  deriving DecidableEq, Repr

/-- Substitutes type arguments through every type an operand mentions. -/
def substituteOperand (arguments : List TypeExpr) : RawOperand → Option RawOperand
  | .type type => RawOperand.type <$> substituteType arguments type
  | .field owner index type isStatic => do
    return .field (← substituteType arguments owner) index (← substituteType arguments type)
      isStatic
  | .call site => do
    return .call { site with
      declaringType := ← substituteType arguments site.declaringType,
      typeArguments := ← site.typeArguments.mapM (substituteType arguments),
      returnType := ← substituteType arguments site.returnType,
      parameterTypes := ← site.parameterTypes.mapM (substituteType arguments) }
  | operand => some operand

/-- Admit value-type constraints and interfaces declared directly by the concrete aggregate.
    Only the `struct`, `new()` and `allows ref struct` flags are supported. -/
private def allowedConstraint (layouts : List RawLayout) (argument : TypeExpr)
    (constraint : GenericConstraint) : Bool :=
  constraint.flags &&& 56 == constraint.flags && constraint.types.all fun type =>
    type == runtimeScope ++ "::System.ValueType" ||
    type == runtimeScope ++ "::System.Runtime.InteropServices.UnmanagedType!" ++ runtimeScope ++
      "::System.ValueType" || match argument with
    | .aggregate identity index => match layouts[index]? with
      | some layout => layout.identity == identity && layout.interfaces.contains type
      | none => false
    | _ => false

/-- A closed, non-reference type argument with a known storage. -/
private def admittedTypeArgument (layouts : List RawLayout) (type : TypeExpr) : Bool :=
  substituteType [] type == some type && match typeStorage layouts type with
    | some .reference | some (.span ..) | some (.array _) | none => false
    | some _ => true

/-- Instantiation preserves instruction encodings, offsets and branch targets exactly. -/
def instantiateMethod (layouts : List RawLayout) (original : RawMethod)
    (arguments : List TypeExpr) : Option RawMethod := do
  if arguments.length != original.genericParameters.length ||
      !arguments.all (admittedTypeArgument layouts) ||
      !(original.genericParameters.zip arguments).all
        (fun (constraint, argument) => allowedConstraint layouts argument constraint) then none
  else
    let returnType ← substituteType arguments original.returnType
    let parameters ← original.parameters.mapM (substituteType arguments)
    let locals ← original.locals.mapM (substituteType arguments)
    let code ← original.code.mapM fun instruction => do
      return { instruction with operand := ← substituteOperand arguments instruction.operand }
    -- Masking with 239 clears the generic calling-convention bit (0x10).
    return { original with
      returnType, parameters, locals, code, genericParameters := [],
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

/-- Closed argument and local storage, including typed span views, and argument accesses. -/
def closedArguments (layouts : List RawLayout) (closed : RawMethod) : Option RawArguments := do
  let parameters ← closed.parameters.mapM (typeStorage layouts)
  let locals ← closed.locals.mapM (typeStorage layouts)
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
  | .call target count => if opcode = 40 then some (target, count) else none
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
def validateImportCall (methods : List SpecializedMethod) (imports : List ImportSlot)
    (opcode : Nat) (site : CallSite) (identity : String) (target count : Nat) : Bool :=
  opcode == 40 && methods.length ≤ target && match imports[target - methods.length]? with
  | none => false
  | some slot =>
    slot.identity == identity && slot.parameterCount == site.parameterCount &&
    slot.hasThis == site.hasThis && slot.returnsValue == site.returnsValue &&
    count == site.parameterCount + (if site.hasThis then 1 else 0) &&
      importSignatureMatches slot site

/-- Every live managed call must select the independently instantiated definition
with the exact substituted type arguments and signature; an external one, a matching import slot. -/
def validateManagedCall (methods : List SpecializedMethod) (imports : List ImportSlot)
    (raw : RawInstruction) (live : Bool) (emitted : Op) : Bool :=
  if !live then true else
  match raw.operand with
  | .call site => match site.target with
    | .managed token => match managedCallTarget raw.opcode emitted with
      | none => false
      | some (target, count) => match methods[target]? with
        | none => false
        | some callee =>
          callee.closed.token == token && callee.arguments == site.typeArguments &&
          callee.closed.parameters.length == site.parameterCount &&
          callee.closed.hasThis == site.hasThis &&
          (callee.closed.returnType != .void) == site.returnsValue &&
          callee.closed.returnType == site.returnType &&
          callee.closed.parameters == site.parameterTypes &&
          count == site.parameterCount + (if raw.opcode == 40 && site.hasThis then 1 else 0)
    | .external identity => match emitted with
      | .call target count =>
        validateImportCall methods imports raw.opcode site identity target count
      | .newAggregate .. | .newVector256 .. => false
      | _ => true
  | _ => match emitted with
    | .call .. | .newAggregate .. | .newVector256 .. => false
    | _ => true

/-- Every call emitted at a live call site of `raw` binds to the method table or an import
    slot, and no other instruction emits a call. An external site may instead emit a
    non-call translation, which other validators check. -/
def ManagedCallsValid (methods : List SpecializedMethod) (imports : List ImportSlot)
    (raw : RawMethod) (reachable : List Bool) (emitted : Method) : Prop :=
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
  all3 (validateManagedCall methods imports) raw.code reachable emitted.code = true

instance (methods : List SpecializedMethod) (imports : List ImportSlot) (raw : RawMethod)
    (reachable : List Bool) (emitted : Method) :
    Decidable (ManagedCallsValid methods imports raw reachable emitted) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem validated_managed_call {methods : List SpecializedMethod} {imports : List ImportSlot}
    {raw : RawMethod} {reachable : List Bool} {emitted : Method}
    (valid : ManagedCallsValid methods imports raw reachable emitted) (pc : Fin raw.code.length) :
    validateManagedCall methods imports raw.code[pc] reachable[pc.val]!
      (emitted.code[pc.val]?.getD (.unsupported "Missing instruction")) = true := by
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
      returnType, parameterTypes⟩ := site
    cases method with
    | managed token =>
      have missing : methods[target]? = none := List.getElem?_eq_none_iff.mpr outside
      simp only [validateManagedCall, managedCallTarget, Bool.not_true, Bool.false_eq_true,
        ite_false] at valid
      by_cases call : opcode = 40 <;> simp [call, missing] at valid
    | external identity =>
      simp only [validateManagedCall, validateImportCall, Bool.not_true, Bool.false_eq_true,
        ite_false] at valid
      cases found : imports[target - methods.length]? with
      | none => simp [found] at valid
      | some slot =>
        simp [found] at valid
        obtain ⟨⟨opcode40, _⟩, ⟨⟨⟨⟨⟨same, arity⟩, receiver⟩, result⟩, argc⟩, typed⟩⟩ := valid
        exact ⟨_, identity, slot, rfl, rfl, opcode40, typed, rfl, same, arity, receiver, result,
          argc⟩
  | _ => simp [validateManagedCall] at valid

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
