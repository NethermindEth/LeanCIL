import CIL.Extraction.ValueDecoding
import CIL.Extraction.SpanCalls

/-!
# Folded instruction sequences

Some raw instruction sequences have no instruction-by-instruction translation and are
emitted as a unit: `typeof(A) == typeof(B)` becomes its decided Boolean, `throw new E(...)`
becomes one `throw`, and span constructors initialize typed local storage.
`foldRoles` finds these sequences from the raw body alone and gives each instruction its
role, which the feature and scalar checks then enforce.
-/

namespace CIL.Extraction

/-- Pointer, byref and generic instance types, which are never equal to a named type. -/
private def constructed : TypeExpr → Bool
  | .pointer _ | .byref _ | .array _ | .apply .. => true
  | _ => false

/-- Conjunction of two three-valued answers: false wins over unknown. -/
private def both : Option Bool → Option Bool → Option Bool
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- Runtime identity of two closed metadata types, or `none` when metadata cannot decide it.
    Full names are never forwarded, but one name in two scopes may denote one type. -/
def sameRuntimeType : TypeExpr → TypeExpr → Option Bool
  | .pointer x, .pointer y | .byref x, .byref y | .array x, .array y => sameRuntimeType x y
  | .apply f x, .apply g y => both (sameRuntimeType f g) (sameRuntimeType x y)
  | a, b =>
    -- `void` is serialized without its scope, so equal spellings do not establish identity.
    if a == b then (if a == .void then none else some true) else
    match namedType a, namedType b with
    | some (scope, name), some (scope', name') =>
      if name != name' then some false else if scope == scope' then some true else none
    | _, _ =>
      if (constructed a || (namedType a).isSome) && (constructed b || (namedType b).isSome) then
        some false
      else none

/-- The type operand of `ldtoken` (208). -/
private def typeHandle : RawInstruction → Option TypeExpr
  | ⟨_, 208, .type type⟩ => some type
  | _ => none

/-- The exact call site of a static `System.Type` method with `parameters` parameters;
    `methodName` is the metadata name spelling `name`. -/
private def typeMethod (name : String) (methodName : MetadataName) (signature : String)
    (parameters : Nat) : CallSite := {
  method := {
    owner := .atom runtimeScope "System.Type", name := methodName, hasThis := false,
    genericArity := 0,
    returnType := .atom runtimeScope
      (if name == "GetTypeFromHandle" then "System.Type" else "System.Boolean"),
    parameters := if name == "GetTypeFromHandle" then
        [.atom runtimeScope "System.RuntimeTypeHandle"]
      else [.atom runtimeScope "System.Type", .atom runtimeScope "System.Type"] },
  name, target := .external (runtimeScope ++ "::" ++ signature),
  typeArguments := [], parameterCount := parameters, returnsValue := true }

private def getTypeFromHandle : CallSite :=
  typeMethod "GetTypeFromHandle" name!"GetTypeFromHandle"
    "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)" 1

/-- Exactly `call Type.GetTypeFromHandle`. -/
private def typeFromHandle (instruction : RawInstruction) : Bool :=
  instruction.opcode == 40 && instruction.operand == .call getTypeFromHandle

/-- Equality polarity of the exact comparison call or reference-equality branch. -/
private def typeComparison (instruction : RawInstruction) : Option Bool :=
  if instruction.opcode == 65025 then
    if instruction.operand == .none then some true else none
  else if instruction.opcode ∈ [46, 51, 59, 64] then
    match instruction.operand with
    | .target _ => some (instruction.opcode == 46 || instruction.opcode == 59)
    | _ => none
  else if instruction.opcode != 40 then none
  else if instruction.operand == .call (typeMethod "op_Equality" name!"op_Equality"
      "System.Boolean System.Type::op_Equality(System.Type,System.Type)" 2) then some true
  else if instruction.operand == .call (typeMethod "op_Inequality" name!"op_Inequality"
      "System.Boolean System.Type::op_Inequality(System.Type,System.Type)" 2) then some false
  else none

/-- The exact `typeof(A) == typeof(B)` encoding and its decided result. -/
def typeTest (a b c d e : RawInstruction) : Option Bool := do
  let left ← typeHandle a
  let right ← typeHandle c
  if !typeFromHandle b || !typeFromHandle d then none
  let equality ← typeComparison e
  let same ← sameRuntimeType left right
  return same == equality

/-- Raw instructions that are admitted only as part of a decided type test. -/
def typeTestInstruction (instruction : RawInstruction) : Bool :=
  (instruction.opcode == 208 && instruction.operand matches .type _) ||
    match instruction.operand with
    | .call site => match site.declaringType with
      | .atom _ "System.Type" =>
        site.name == "GetTypeFromHandle" || site.name == "op_Equality" ||
          site.name == "op_Inequality"
      | _ => false
    | _ => false

/-- `ldstr` (114) or `ldnull` (20): a message argument of a folded `throw`. -/
private def messageLoad (instruction : RawInstruction) : Bool :=
  instruction.opcode == 114 || instruction.opcode == 20

/-- Admitted framework exceptions with parameterless/string constructors, plus the three
    argument exceptions' two-string overloads. Other constructors remain unsupported. -/
private def stringExceptionConstructor (name : String) (count : Nat) : Bool :=
  (count ≤ 1 && name ∈ ["System.Exception", "System.SystemException",
    "System.ApplicationException", "System.ArithmeticException",
    "System.DivideByZeroException", "System.OverflowException",
    "System.InvalidOperationException", "System.NotSupportedException",
    "System.NotImplementedException", "System.ArgumentException",
    "System.ArgumentNullException", "System.ArgumentOutOfRangeException",
    "System.IndexOutOfRangeException", "System.NullReferenceException",
    "System.FormatException"]) ||
  (count == 2 && name ∈ ["System.ArgumentException", "System.ArgumentNullException",
    "System.ArgumentOutOfRangeException"])

/-- Exact framework signatures whose literal/null arguments cannot change the raised type. -/
def exceptionConstructor (name : String) (parameters : List TypeExpr) : Bool :=
  let string := TypeExpr.object runtimeScope "System.String"
  let exception := TypeExpr.atom runtimeScope "System.Exception"
  (parameters.all (· == string) && stringExceptionConstructor name parameters.length) ||
    (parameters == [string, exception] && name ∈ ["System.Exception",
      "System.InvalidOperationException", "System.ArgumentException",
      "System.ArgumentOutOfRangeException"]) ||
    (name == "System.ArgumentException" && parameters == [string, string, exception]) ||
    (name == "System.ArgumentOutOfRangeException" &&
      parameters == [string, .atom runtimeScope "System.Object", string])

/-- An exact allowlisted `System.Runtime` constructor, including its complete signature. -/
private def raisedType (count : Nat) (arguments : List RawInstruction)
    (instruction : RawInstruction) : Option String :=
  if 3 < count then none else match instruction with
  | ⟨_, 115, .call site⟩ => match site.declaringType, site.target with
    | .atom scope name, .external signature =>
      if scope == runtimeScope && exceptionConstructor name site.parameterTypes &&
        site.parameterTypes.length == count && arguments.length == count &&
        (arguments.zip site.parameterTypes).all (fun (argument, parameter) =>
          parameter == .object runtimeScope "System.String" || argument.opcode == 20) &&
        signature == runtimeScope ++ "::System.Void " ++ name ++ "::.ctor(" ++
          ",".intercalate (site.parameterTypes.map fun type =>
            match type with | .atom _ name | .object _ name => name | _ => "") ++ ")" &&
        site.name == ".ctor" && site.hasThis && !site.returnsValue &&
        site.returnType == .void && site.typeArguments.isEmpty &&
        site.parameterCount == count then some name else none
    | _, _ => none
  | _ => none

/-- One beyond the largest admitted message arity; reaching it rules out a throw fold. -/
private def throwMessageLimit : Nat := 4

/-- `throw new E(...)` with only string or null arguments: the argument count and raised type. -/
def throwFold (code : List RawInstruction) : Option (Nat × String) :=
  let count := ((code.take throwMessageLimit).takeWhile messageLoad).length
  if count == throwMessageLimit then none else
  match code.drop count with
  | constructor :: ⟨_, 122, .none⟩ :: _ =>
    (count, ·) <$> raisedType count (code.take count) constructor
  | _ => none

/-- Admitted exception constructors never consume more than three literal/null arguments. -/
private theorem raisedType_large (count : Nat) (arguments : List RawInstruction)
    (instruction : RawInstruction) (large : 3 < count) :
    raisedType count arguments instruction = none := by
  simp [raisedType, large]

#print axioms raisedType_large

/-- Bounding message-prefix inspection preserves the original unrestricted fold test. -/
theorem throwFold_eq_takeWhile (code : List RawInstruction) :
    throwFold code =
      let count := (code.takeWhile messageLoad).length
      match code.drop count with
      | constructor :: ⟨_, 122, .none⟩ :: _ =>
        (count, ·) <$> raisedType count (code.take count) constructor
      | _ => none := by
  unfold throwFold throwMessageLimit
  rw [← List.take_takeWhile, List.length_take]
  by_cases short : (code.takeWhile messageLoad).length ≤ 3
  · have bound : min 4 (code.takeWhile messageLoad).length =
        (code.takeWhile messageLoad).length := by omega
    have notFour : (code.takeWhile messageLoad).length ≠ 4 := by omega
    simp only [bound, beq_iff_eq, notFour, ↓reduceIte]
  · have bound : min 4 (code.takeWhile messageLoad).length = 4 := by omega
    have large : 3 < (code.takeWhile messageLoad).length := by omega
    simp only [bound, beq_self_eq_true, ↓reduceIte]
    split <;> simp [raisedType_large _ _ _ large]

#print axioms throwFold_eq_takeWhile

/-- An instruction's part in a folded sequence. -/
inductive FoldRole where
  /-- The first instruction: emits nothing, and may be a branch target. -/
  | head
  /-- Later instructions: emit nothing, and are entered only from the preceding instruction. -/
  | interior
  /-- A type comparison: pushes the decided Boolean. -/
  | result (value : Bool)
  /-- A reference-equality branch over two closed typeof values takes this decided edge. -/
  | typeBranch (taken : Bool)
  /-- The raw `throw`: raises the type bound by the exact folded operands. -/
  | raise (exception : String)
  /-- An unchanged argument push protected from non-fallthrough entry. -/
  | argument
  /-- A checked constructor initializes the local whose address starts the fold. -/
  | spanConstructor (index : Nat) (constructor : SpanConstructor)
  /-- A direct managed call whose prefix requests frame retirement before transfer. -/
  | tailCall
  deriving DecidableEq, Repr

/-- Resetting a span local binds its exact type and never exposes its storage address. -/
private def spanDefaultFold (localAt : Nat → Option TypeExpr) (head : RawInstruction)
    (tail : List RawInstruction) : Option (List (Option FoldRole)) := do
  if !(head.opcode ∈ [18, 65037]) then none else pure ()
  let index ← localIndex head
  let localType ← localAt index
  let some ⟨_, 65045, .type initialized⟩ := tail.head? | none
  if initialized != localType then none else pure ()
  let .span width writable ← spanStorage localType | none
  return [some .head, some (.spanConstructor index (.empty width writable))]

/-- A constructor fold admits at most three pure single-value argument pushes. -/
private def spanConstructorFold (localAt : Nat → Option TypeExpr) (head : RawInstruction)
    (tail : List RawInstruction) : Option (List (Option FoldRole)) := do
  if !(head.opcode ∈ [18, 65037]) then none else pure ()
  let index ← localIndex head
  let localType ← localAt index
  let pushes := (tail.take 4).takeWhile fun instruction => instruction.opcode ∈
    [2, 3, 4, 5, 14, 65033, 6, 7, 8, 9, 17, 65036,
      20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
  if pushes.length > 3 then none else pure ()
  let call ← tail[pushes.length]?
  let .call site := call.operand | none
  if call.opcode != 40 || site.declaringType != localType then none else pure ()
  let constructor ← spanLocalConstructor site
  if pushes.length != site.parameterCount then none else
    some (some .head :: List.replicate pushes.length (some .argument) ++
      [some (.spanConstructor index constructor)])

/-- The roles of a fold starting at `a`, with local types supplied by `localAt`. -/
private def foldAt (localAt : Nat -> Option TypeExpr)
    (a : RawInstruction) (tail : List RawInstruction) :
    Option (List (Option FoldRole)) :=
  spanDefaultFold localAt a tail <|> spanConstructorFold localAt a tail <|>
  (match a, tail with
    | ⟨_, 20, .none⟩, ⟨_, 122, .none⟩ :: _ =>
      some [some .head, some (.raise "System.NullReferenceException")]
    | ⟨_, 65044, .none⟩, ⟨_, 41, .indirectCall _ _ false false 0⟩ ::
        ⟨_, 42, .none⟩ :: _ => some [some .head, some .tailCall, some .argument]
    | ⟨_, 65044, .none⟩, ⟨_, 40, .call site⟩ :: ⟨_, 42, .none⟩ :: _ =>
      match site.target with
      | .managed _ => some [some .head, some .tailCall, some .argument]
      | _ => none
    | _, _ => none) <|>
  (match tail with
    | b :: c :: d :: e :: _ => (typeTest a b c d e).map fun value =>
        [some .head, some .interior, some .interior, some .interior,
          some (if e.opcode == 40 || e.opcode == 65025 then .result value else .typeBranch value)]
    | _ => none) <|>
  (throwFold (a :: tail)).map fun (count, name) =>
    some .head :: List.replicate count (some .interior) ++ [some (.raise name)]

/-- Assign `pending` roles first; each step consumes one instruction, so the walk is structural.
    Local types come from `localAt`. -/
def foldRolesFrom (localAt : Nat -> Option TypeExpr) :
    List (Option FoldRole) → List RawInstruction → List (Option FoldRole)
  | _, [] => []
  | role :: pending, _ :: tail => role :: foldRolesFrom localAt pending tail
  | [], a :: tail => match foldAt localAt a tail with
    | some (role :: pending) => role :: foldRolesFrom localAt pending tail
    | _ => none :: foldRolesFrom localAt [] tail

/-- Roles derived from the raw body alone; extraction evidence cannot add or move a fold.
    Local types are read from a `FlowIndex` built once per body. -/
def foldRoles (locals : List TypeExpr) (code : List RawInstruction) : List (Option FoldRole) :=
  foldRolesFrom (FlowIndex.ofList locals).get? [] code

/-- A non-fallthrough edge may enter a fold only at its first instruction. -/
def foldEntry (role : Option (Option FoldRole)) : Bool :=
  match role with
  | some (some .interior) | some (some (.result _)) | some (some (.raise _))
  | some (some (.typeBranch _))
  | some (some .argument) | some (some (.spanConstructor ..)) => false
  | some (some .tailCall) => false
  | _ => true

end CIL.Extraction
