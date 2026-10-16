import CIL.Extraction.Parameters

namespace CIL.Extraction

inductive TypeExpr where
  | void
  | atom (scope name : String)
  | aggregate (identity : String) (index : Nat)
  | enum (identity : String) (underlying : TypeExpr)
  | parameter (index : Nat)
  | byref (element : TypeExpr)
  | pointer (element : TypeExpr)
  | constructor (scope name : String)
  | apply (constructor argument : TypeExpr)
  deriving DecidableEq, Repr

private def runtimeScope : String :=
  "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def intrinsicsScope : String :=
  "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

private def primitiveField : String → Option FieldType
  | "System.SByte" => some .signed8 | "System.Byte" => some .unsigned8
  | "System.Boolean" => some .boolean | "System.Int16" => some .signed16
  | "System.UInt16" => some .unsigned16 | "System.Char" => some .character
  | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
  | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
  | "System.IntPtr" => some .nativeInt | "System.UIntPtr" => some .nativeUInt
  | _ => none

private def enumField : FieldType → Bool
  | .signed8 | .unsigned8 | .signed16 | .unsigned16 | .signed32 | .unsigned32
  | .signed64 | .unsigned64 => true
  | _ => false

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
  | .apply (.constructor scope name) (.atom elementScope element) =>
    if scope != intrinsicsScope || elementScope != runtimeScope ||
        element ∉ ["System.UInt64", "System.Int64", "System.UInt32", "System.Int32", "System.Byte", "System.Double", "System.Single"] then none
    else if name = "System.Runtime.Intrinsics.Vector128`1" then some .vector128
    else if name = "System.Runtime.Intrinsics.Vector256`1" then some .vector256 else none
  | _ => none

/-- Structural substitution includes nested type constructors, not just signature strings. -/
def substituteType (arguments : List TypeExpr) : TypeExpr → Option TypeExpr
  | .parameter index => arguments[index]?
  | .byref element => TypeExpr.byref <$> substituteType arguments element
  | .pointer element => TypeExpr.pointer <$> substituteType arguments element
  | .enum identity underlying => TypeExpr.enum identity <$> substituteType arguments underlying
  | .apply constructor argument => do
    return .apply (← substituteType arguments constructor) (← substituteType arguments argument)
  | type => some type

inductive MethodId where
  | managed (token : Nat)
  | external (identity : String)
  deriving DecidableEq, Repr

structure CallSite where
  declaringType : TypeExpr := .void
  name : String := ""
  target : MethodId
  typeArguments : List TypeExpr
  parameterCount : Nat
  hasThis : Bool
  returnsValue : Bool
  deriving DecidableEq, Repr

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

structure RawInstruction where
  offset : Nat
  opcode : Nat
  operand : RawOperand
  deriving DecidableEq, Repr

structure GenericConstraint where
  flags : Nat
  types : List String
  deriving DecidableEq, Repr

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

def substituteOperand (arguments : List TypeExpr) : RawOperand → Option RawOperand
  | .type type => RawOperand.type <$> substituteType arguments type
  | .field owner index type isStatic => do
    return .field (← substituteType arguments owner) index (← substituteType arguments type) isStatic
  | .call site => do return .call { site with declaringType := ← substituteType arguments site.declaringType, typeArguments := ← site.typeArguments.mapM (substituteType arguments) }
  | operand => some operand

private def allowedConstraint (constraint : GenericConstraint) : Bool :=
  constraint.flags &&& 56 == constraint.flags && constraint.types.all fun type =>
    type == runtimeScope ++ "::System.ValueType" ||
    type == runtimeScope ++ "::System.Runtime.InteropServices.UnmanagedType!" ++ runtimeScope ++ "::System.ValueType"

private def admittedTypeArgument (layouts : List RawLayout) (type : TypeExpr) : Bool :=
  substituteType [] type == some type && match typeStorage layouts type with
    | some .reference | none => false
    | some _ => true

/-- Instantiation preserves instruction encodings, offsets and branch targets exactly. -/
def instantiateMethod (layouts : List RawLayout) (original : RawMethod)
    (arguments : List TypeExpr) : Option RawMethod := do
  if arguments.length != original.genericParameters.length ||
      !arguments.all (admittedTypeArgument layouts) || !original.genericParameters.all allowedConstraint then none
  else
    let returnType ← substituteType arguments original.returnType
    let parameters ← original.parameters.mapM (substituteType arguments)
    let locals ← original.locals.mapM (substituteType arguments)
    let code ← original.code.mapM fun instruction => do
      return { instruction with operand := ← substituteOperand arguments instruction.operand }
    return { original with returnType, parameters, locals, code, genericParameters := [], callingConvention := original.callingConvention &&& 239 }

/-- Closed argument metadata is derived from this checked body, including short opcodes. -/
def argumentOperation (instruction : RawInstruction) : Option ArgumentOp :=
  match instruction.opcode, instruction.operand with
  | 2, .none => some (.load 0) | 3, .none => some (.load 1)
  | 4, .none => some (.load 2) | 5, .none => some (.load 3)
  | 14, .argument index | 65033, .argument index => some (.load index)
  | 15, .argument index | 65034, .argument index => some (.address index)
  | 16, .argument index | 65035, .argument index => some (.store index)
  | opcode, _ => if opcode ∈ [2, 3, 4, 5, 14, 15, 16, 65033, 65034, 65035] then none else some .other

def closedArguments (layouts : List RawLayout) (closed : RawMethod) : Option RawArguments := do
  let parameters ← closed.parameters.mapM (typeStorage layouts)
  let locals ← closed.locals.mapM (typeStorage layouts)
  let code ← closed.code.mapM argumentOperation
  return ⟨(if closed.hasThis then [.reference] else []) ++ parameters, locals, code⟩

def SpecializationValid (layouts : List RawLayout) (original : RawMethod)
    (arguments : List TypeExpr) (closed : RawMethod) (parameterInput : RawArguments) : Prop :=
  instantiateMethod layouts original arguments = some closed ∧
  closedArguments layouts closed = some parameterInput

instance (layouts : List RawLayout) (original : RawMethod) (arguments : List TypeExpr)
    (closed : RawMethod) (parameterInput : RawArguments) : Decidable (SpecializationValid layouts original arguments closed parameterInput) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem validated_specialization {layouts : List RawLayout} {original closed : RawMethod}
    {arguments : List TypeExpr} {parameterInput : RawArguments}
    (valid : SpecializationValid layouts original arguments closed parameterInput) :
    instantiateMethod layouts original arguments = some closed := valid.1

theorem validated_closed_arguments {layouts : List RawLayout} {original closed : RawMethod}
    {arguments : List TypeExpr} {parameterInput : RawArguments}
    (valid : SpecializationValid layouts original arguments closed parameterInput) :
    closedArguments layouts closed = some parameterInput := valid.2


structure SpecializedMethod where
  arguments : List TypeExpr
  closed : RawMethod
  deriving DecidableEq, Repr

private def managedCallTarget (opcode : Nat) : Op → Option (Nat × Nat)
  | .call target count => if opcode = 40 then some (target, count) else none
  | .newAggregate target count _ | .newVector256 target count =>
    if opcode = 115 then some (target, count) else none
  | _ => none

/-- Every live managed call must select the independently instantiated definition
with the exact substituted type arguments and signature. -/
def validateManagedCall (methods : List SpecializedMethod) (raw : RawInstruction)
    (live : Bool) (emitted : Op) : Bool :=
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
          count == site.parameterCount + (if raw.opcode == 40 && site.hasThis then 1 else 0)
    | .external _ => match emitted with
      | .call .. | .newAggregate .. | .newVector256 .. => false
      | _ => true
  | _ => match emitted with
    | .call .. | .newAggregate .. | .newVector256 .. => false
    | _ => true

def ManagedCallsValid (methods : List SpecializedMethod) (raw : RawMethod)
    (reachable : List Bool) (emitted : Method) : Prop :=
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
  all3 (validateManagedCall methods) raw.code reachable emitted.code = true

instance (methods : List SpecializedMethod) (raw : RawMethod) (reachable : List Bool)
    (emitted : Method) : Decidable (ManagedCallsValid methods raw reachable emitted) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem validated_managed_call {methods : List SpecializedMethod} {raw : RawMethod}
    {reachable : List Bool} {emitted : Method}
    (valid : ManagedCallsValid methods raw reachable emitted) (pc : Fin raw.code.length) :
    validateManagedCall methods raw.code[pc] reachable[pc.val]! (emitted.code[pc.val]?.getD (.unsupported "Missing instruction")) = true := by
  have live : pc.val < reachable.length := valid.1 ▸ pc.isLt
  have present : pc.val < emitted.code.length := valid.2.1 ▸ pc.isLt
  rw [getElem!_pos reachable pc.val live, List.getElem?_eq_getElem present, Option.getD_some]
  exact all3_at valid.2.2 (List.getElem?_eq_getElem pc.isLt) (List.getElem?_eq_getElem live)
    (List.getElem?_eq_getElem present)

#print axioms validated_specialization
#print axioms validated_closed_arguments
#print axioms validated_managed_call

end CIL.Extraction
