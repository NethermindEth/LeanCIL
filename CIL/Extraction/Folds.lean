import CIL.ExceptionType
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
    (parameters : Nat) : CallSite :=
  let type := TypeExpr.atom runtimeScope (metadata_text% "System.Type")
  let fromHandle := methodName == name!"GetTypeFromHandle"
  let method : MethodRef := {
    owner := type, name := methodName, hasThis := false,
    genericArity := 0,
    returnType := if fromHandle then type else
      .atom runtimeScope (metadata_text% "System.Boolean"),
    parameters := if fromHandle then
        [.atom runtimeScope (metadata_text% "System.RuntimeTypeHandle")]
      else [type, type] }
  { method, declared := method.signature 0, name,
    target := .external (runtimeScope ++ "::" ++ signature), typeArguments := [],
    parameterCount := parameters, returnsValue := true }

private def getTypeFromHandle : CallSite :=
  typeMethod (metadata_text% "GetTypeFromHandle") name!"GetTypeFromHandle"
    (metadata_text% "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)") 1

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
  else if instruction.operand == .call (typeMethod
      (metadata_text% "op_Equality") name!"op_Equality"
      (metadata_text% "System.Boolean System.Type::op_Equality(System.Type,System.Type)") 2) then
    some true
  else if instruction.operand == .call (typeMethod
      (metadata_text% "op_Inequality") name!"op_Inequality"
      (metadata_text% "System.Boolean System.Type::op_Inequality(System.Type,System.Type)") 2) then
    some false
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
private def messageLoad : RawInstruction → Bool
  | ⟨_, 114, .text _⟩ | ⟨_, 20, .none⟩ => true
  | _ => false

/-- The member a constructor's owner spells, the scope compared once; `none` for any other type. -/
def exceptionOwner? : TypeExpr → Option ExceptionType
  | .atom scope name =>
    if scope == runtimeScope then ExceptionType.all.find? (·.ownerName == name) else none
  | _ => none

/-- A constructor owner that names a member is that member's runtime type. -/
theorem exceptionOwner?_eq_some {type : TypeExpr} {raised : ExceptionType}
    (found : exceptionOwner? type = some raised) : type = .atom runtimeScope raised.ownerName := by
  cases type with
  | atom scope name =>
    simp only [exceptionOwner?] at found
    split at found
    next sameScope =>
      have named := List.find?_some found
      simp only [beq_iff_eq] at named sameScope
      rw [sameScope, named]
    next => simp at found
  | _ => simp [exceptionOwner?] at found

#print axioms exceptionOwner?_eq_some

/-- Each member's owner name identifies that member: no member shadows another. -/
theorem exceptionOwner?_ownerName (raised : ExceptionType) :
    exceptionOwner? (.atom runtimeScope raised.ownerName) = some raised := by
  have sameOwner : ∀ other : ExceptionType,
      (other.ownerName == raised.ownerName) = (other == raised) := by
    intro other
    by_cases equal : other = raised
    · subst equal
      simp
    · have names : other.ownerName ≠ raised.ownerName := ExceptionType.ownerName_injective.ne equal
      simp only [beq_eq_false_iff_ne.mpr names, beq_eq_false_iff_ne.mpr equal]
  simp only [exceptionOwner?, beq_self_eq_true, ↓reduceIte, sameOwner]
  cases raised <;> decide

#print axioms exceptionOwner?_ownerName

/-- The `System.String` parameter of an exception constructor: a message or a parameter name. -/
def messageParameter : TypeExpr := .object runtimeScope "System.String"

/-- The `System.Exception` parameter of an exception constructor: the inner exception. -/
def innerParameter : TypeExpr := .atom runtimeScope "System.Exception"

/-- The `System.Object` parameter of an exception constructor: the actual argument value. -/
def actualParameter : TypeExpr := .atom runtimeScope "System.Object"

/-- The parameter lists of the constructors a folded `throw` may call for each member; the
    members only instructions raise admit none. -/
def admittedParameters : ExceptionType → List (List TypeExpr)
  | .baseException | .invalidOperation =>
    [[], [messageParameter], [messageParameter, innerParameter]]
  | .systemException | .applicationException | .arithmetic | .divideByZero | .overflow
  | .notSupported | .notImplemented | .indexOutOfRange | .nullReference | .format =>
    [[], [messageParameter]]
  | .argument =>
    [[], [messageParameter], [messageParameter, messageParameter],
      [messageParameter, innerParameter], [messageParameter, messageParameter, innerParameter]]
  | .argumentNull => [[], [messageParameter], [messageParameter, messageParameter]]
  | .argumentOutOfRange =>
    [[], [messageParameter], [messageParameter, messageParameter],
      [messageParameter, innerParameter], [messageParameter, actualParameter, messageParameter]]
  | .invalidCast | .arrayTypeMismatch => []

/-- An exact allowlisted `System.Runtime` constructor, including its complete signature. -/
private def raisedType (count : Nat) (arguments : List RawInstruction)
    (instruction : RawInstruction) : Option ExceptionType :=
  if 3 < count then none else match instruction with
  | ⟨_, 115, .call site⟩ => match site.declaringType, site.target with
    | .atom _ name, .external signature => do
      let raised ← exceptionOwner? site.declaringType
      if site.parameterTypes ∈ admittedParameters raised &&
        site.parameterTypes.length == count && arguments.length == count &&
        (arguments.zip site.parameterTypes).all (fun (argument, parameter) =>
          parameter == .object runtimeScope "System.String" || argument.opcode == 20) &&
        signature == runtimeScope ++ "::System.Void " ++ name ++ "::.ctor(" ++
          ",".intercalate (site.parameterTypes.map fun type =>
            match type with | .atom _ name | .object _ name => name | _ => "") ++ ")" &&
        site.name == ".ctor" && site.hasThis && !site.returnsValue &&
        site.returnType == .void && site.typeArguments.isEmpty &&
        site.parameterCount == count then some raised else none
    | _, _ => none
  | _ => none

/-- One beyond the largest admitted message arity; reaching it rules out a throw fold. -/
private def throwMessageLimit : Nat := 4

/-- `throw new E(...)` with only string or null arguments: the argument count and raised type. -/
def throwFold (code : List RawInstruction) : Option (Nat × ExceptionType) :=
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
  | raise (exception : ExceptionType)
  /-- An unchanged argument push protected from non-fallthrough entry. -/
  | argument
  /-- A checked constructor initializes the local whose address starts the fold. -/
  | spanConstructor (index : Nat) (constructor : SpanConstructor)
  /-- A direct managed call whose prefix requests frame retirement before transfer. -/
  | tailCall
  /-- A branch enters this candidate after its head, so none of its roles may execute. -/
  | blocked
  deriving DecidableEq, Repr

/-- The instruction fixed by a fold role. Constructors also need their checked layout. -/
def Instruction.ofRole? (role : FoldRole) (previous : Option RawInstruction)
    (raw : RawInstruction) : Option Instruction :=
  match role with
  | .head | .interior => some .nop
  | .result value => some (.ldc_i4 (if value then 1 else 0))
  | .typeBranch taken => match raw.operand with
    | .target target => some (if taken then .br target else .nop)
    | _ => none
  | .raise exception => some (.throw exception)
  | .argument => Instruction.ofRaw? previous raw
  | .tailCall => if raw.opcode == 40 || raw.opcode == 41 then Instruction.ofRaw? previous raw
      else none
  | .spanConstructor .. | .blocked => none

/-- Calls use their site requirement. Other instructions in a fold emit their raw role. -/
def Instruction.withCallDecoder (roles : Array (Option FoldRole))
    (live : Nat → Bool) (localKind : TypeExpr → Option LocalKind) (decodeCall : CallDecoder) :
    CallDecoder := fun pc previous raw =>
  if !live pc then .unadmitted raw.opcode
  else if methodTokenCall raw.opcode then decodeCall pc previous raw
  else match (indexedRead? roles pc).join with
    | none | some .blocked => Instruction.ofClosedValue previous raw
    | some (.spanConstructor index (.empty ..)) =>
      match raw.operand with
      | .type initialized => match localKind initialized with
        | some (.span width writable) => .initializeSpanLocal index (.empty width writable)
        | _ => .unadmitted raw.opcode
      | _ => .unadmitted raw.opcode
    | some role => (Instruction.ofRole? role previous raw).getD (.unadmitted raw.opcode)

/-- Resetting a span local binds its exact type and never exposes its storage address. -/
private def spanDefaultFold (localAt : Nat → Option TypeExpr) (head : RawInstruction)
    (tail : List RawInstruction) : Option (List (Option FoldRole)) := do
  let index ← localIndex head
  let localType ← localAt index
  let some ⟨_, 65045, .type initialized⟩ := tail.head? | none
  if initialized != localType then none else pure ()
  let .span width writable ← spanStorage localType | none
  return [some .head, some (.spanConstructor index (.empty width writable))]

/-- A constructor fold admits at most three pure single-value argument pushes. -/
private def spanConstructorFold (localAt : Nat → Option TypeExpr) (head : RawInstruction)
    (tail : List RawInstruction) : Option (List (Option FoldRole)) := do
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

/-- The raw head determines which bounded instruction window can form a fold. -/
private inductive FoldHead where
  | spanAddress | exception | tailPrefix | typeHandle

/-- Only these instructions can start a folded sequence. -/
private def foldHead? : Nat → Option FoldHead
  | 18 | 65037 => some .spanAddress
  | 20 | 114 | 115 => some .exception
  | 65044 => some .tailPrefix
  | 208 => some .typeHandle
  | _ => none

/-- The roles of a fold starting at `a`, with local types supplied by `localAt`. -/
private def foldAt (localAt : Nat -> Option TypeExpr)
    (a : RawInstruction) (tail : List RawInstruction) :
    Option (List (Option FoldRole)) :=
  match foldHead? a.opcode with
  | some .spanAddress => spanDefaultFold localAt a tail <|> spanConstructorFold localAt a tail
  | some .exception =>
    if a.opcode == 20 && a.operand == .none && (tail.head? matches some ⟨_, 122, .none⟩) then
      some [some .head, some (.raise .nullReference)]
    else (throwFold (a :: tail)).map fun (count, raised) =>
      some .head :: List.replicate count (some .interior) ++ [some (.raise raised)]
  | some .tailPrefix => match a.operand, tail with
    | .none, ⟨_, 41, .indirectCall _ _ false false 0⟩ :: ⟨_, 42, .none⟩ :: _ =>
      some [some .head, some .tailCall, some .argument]
    | .none, ⟨_, 40, .call site⟩ :: ⟨_, 42, .none⟩ :: _ => match site.target with
      | .managed _ => some [some .head, some .tailCall, some .argument]
      | _ => none
    | _, _ => none
  | some .typeHandle => match tail with
    | b :: c :: d :: e :: _ => (typeTest a b c d e).map fun value =>
      [some .head, some .interior, some .interior, some .interior,
        some (if e.opcode == 40 || e.opcode == 65025 then .result value else .typeBranch value)]
    | _ => none
  | _ => none

/-- A non-fallthrough edge may enter ordinary code or the head of a fold. -/
def foldEntry : Option (Option FoldRole) → Bool
  | some none | some (some .head) => true
  | _ => false

/-- Assign all roles of a candidate together, using every encoded target in the body. -/
private def foldRolesFrom (localAt : Nat → Option TypeExpr) (targeted : Nat → Bool) :
    Nat → List (Option FoldRole) → List RawInstruction → List (Option FoldRole)
  | _, _, [] => []
  | pc, role :: pending, _ :: tail => role :: foldRolesFrom localAt targeted (pc + 1) pending tail
  | pc, [], first :: tail =>
    match foldAt localAt first tail with
    | some (head :: rest) =>
      if (rest.zipIdx (pc + 1)).all (fun (role, atPc) => !targeted atPc || foldEntry (some role))
      then head :: foldRolesFrom localAt targeted (pc + 1) rest tail
      else some .blocked :: foldRolesFrom localAt targeted (pc + 1)
        (List.replicate rest.length (some .blocked)) tail
    | _ => none :: foldRolesFrom localAt targeted (pc + 1) [] tail

/-- Roles derived from raw instructions, their branch targets and the declared local types. -/
def foldRoles (locals : List TypeExpr) (code : List RawInstruction) : List (Option FoldRole) :=
  let targets := Std.TreeSet.ofList (branchTargets code) compare
  foldRolesFrom (FlowIndex.ofList locals).get? targets.contains 0 [] code

/-- Every raw instruction is live and independent of call claims and folded sequences. -/
def plainBody : List RawInstruction → List Bool → Bool
  | [], _ => true
  | first :: rest, true :: live =>
    !methodTokenCall first.opcode && (foldHead? first.opcode).isNone && plainBody rest live
  | _, _ => false

/-- At each plain site the mask is live, the role is absent, and no call claim applies. -/
theorem plainBody_at {closed : RawMethod} {reachable : List Bool}
    (plain : plainBody closed.code reachable)
    {pc : Nat} {raw : RawInstruction} (found : closed.code[pc]? = some raw) :
    reachable[pc]? = some true ∧ methodTokenCall raw.opcode = false ∧
      (foldRoles closed.locals closed.code)[pc]? = some none := by
  let localAt := (FlowIndex.ofList closed.locals).get?
  let targeted := (Std.TreeSet.ofList (branchTargets closed.code) compare).contains
  suffices walk : ∀ (code : List RawInstruction) (mask : List Bool) (start index : Nat),
      plainBody code mask = true → code[index]? = some raw →
        mask[index]? = some true ∧ methodTokenCall raw.opcode = false ∧
          (foldRolesFrom localAt targeted start [] code)[index]? = some none by
    exact walk closed.code reachable 0 pc plain found
  intro code
  induction code with
  | nil => simp
  | cons first rest ih =>
    intro mask start index checked atIndex
    cases mask with
    | nil => cases checked
    | cons head tail =>
      cases head with
      | false => cases checked
      | true =>
        simp only [plainBody, Bool.and_eq_true, Bool.not_eq_true',
          Option.isNone_iff_eq_none] at checked
        simp only [foldRolesFrom, foldAt, checked.1.2]
        cases index with
        | zero =>
          obtain rfl := Option.some.inj atIndex
          exact ⟨rfl, checked.1.1, rfl⟩
        | succ index => exact ih tail (start + 1) index checked.2 atIndex

#print axioms plainBody_at

end CIL.Extraction
