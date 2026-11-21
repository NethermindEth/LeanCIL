import CIL.ExceptionType
import CIL.Extraction.ValueDecoding
import CIL.Extraction.SpanCalls

/-!
# Folded instruction sequences

A closed `typeof(A) == typeof(B)` comparison yields its decided Boolean. An allowlisted
exception construction binds the raised type to the `throw`. Its `ldnull` operands push the
same null object reference as in ordinary code.
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
        site.method.name == name!".ctor" && site.hasThis && !site.returnsValue &&
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
  /-- The first instruction of the sequence, which may be a branch target. -/
  | head
  /-- A later operand entered only from the preceding instruction. -/
  | interior
  /-- A type comparison: pushes the decided Boolean. -/
  | result (value : Bool)
  /-- A reference-equality branch over two closed typeof values takes this decided edge. -/
  | typeBranch (taken : Bool)
  /-- The raw `throw`: raises the type bound by the exact folded operands. -/
  | raise (exception : ExceptionType)
  /-- An unchanged argument push protected from non-fallthrough entry. -/
  | argument
  /-- A direct managed call whose prefix requests frame retirement before transfer. -/
  | tailCall
  /-- A branch enters this candidate after its head, so none of its roles may execute. -/
  | blocked
  deriving DecidableEq, Repr

/-- The instruction fixed by a fold role. -/
def Instruction.ofRole? (role : FoldRole) (previous : Option RawInstruction)
    (raw : RawInstruction) : Option Instruction :=
  match role with
  | .head | .interior =>
    if raw.opcode == 20 then
      if raw.operand == .none then some .ldnull else none
    else some .nop
  | .result value => some (.ldc_i4 (if value then 1 else 0))
  | .typeBranch taken => match raw.operand with
    | .target target => some (if taken then .br target else .nop)
    | _ => none
  | .raise exception => some (.throw exception)
  | .argument => Instruction.ofRaw? previous raw
  | .tailCall => if raw.opcode == 40 || raw.opcode == 41 then Instruction.ofRaw? previous raw
      else none
  | .blocked => none

/-- Calls and static field operands need the method's bindings or profile to decode. -/
def boundSite (raw : RawInstruction) : Bool :=
  methodTokenCall raw.opcode || raw.opcode == 126 || raw.opcode == 127 ||
    raw.opcode == 128 || raw.opcode == 208 && (raw.operand matches .field ..)

/-- These roles determine the entire instruction, including a call inside a fold. -/
def foldOwnsSite : Option FoldRole → Bool
  | some .head | some .interior | some (.result _) => true
  | _ => false

/-- Bound operands outside a recognized fold use their site decoder. -/
def Instruction.withSiteDecoder (roles : Array (Option FoldRole))
    (live : Nat → Bool) (decodeSite : SiteDecoder) :
    SiteDecoder := fun pc previous raw =>
  if !live pc then .unadmitted raw.opcode
  else
    let role := (indexedRead? roles pc).join
    if boundSite raw && !foldOwnsSite role then decodeSite pc previous raw
    else match role with
    | none | some .blocked => Instruction.ofClosedValue previous raw
    | some role => (Instruction.ofRole? role previous raw).getD (.unadmitted raw.opcode)

/-- The raw head determines which bounded instruction window can form a fold. -/
private inductive FoldHead where
  | exception | tailPrefix | typeHandle

/-- Only these instructions can start a folded sequence. -/
private def foldHead? : Nat → Option FoldHead
  | 20 | 114 | 115 => some .exception
  | 65044 => some .tailPrefix
  | 208 => some .typeHandle
  | _ => none

/-- The roles of a fold starting at `a`. -/
private def foldAt (a : RawInstruction) (tail : List RawInstruction) :
    Option (List (Option FoldRole)) :=
  match foldHead? a.opcode with
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
private def foldRolesFrom (targeted : Nat → Bool) :
    Nat → List (Option FoldRole) → List RawInstruction → List (Option FoldRole)
  | _, _, [] => []
  | pc, role :: pending, _ :: tail => role :: foldRolesFrom targeted (pc + 1) pending tail
  | pc, [], first :: tail =>
    match foldAt first tail with
    | some (head :: rest) =>
      if (rest.zipIdx (pc + 1)).all (fun (role, atPc) => !targeted atPc || foldEntry (some role))
      then head :: foldRolesFrom targeted (pc + 1) rest tail
      else some .blocked :: foldRolesFrom targeted (pc + 1)
        (List.replicate rest.length (some .blocked)) tail
    | _ => none :: foldRolesFrom targeted (pc + 1) [] tail

/-- Roles derived from raw instructions and their branch targets. -/
def foldRoles (code : List RawInstruction) : List (Option FoldRole) :=
  let targets := Std.TreeSet.ofList (branchTargets code) compare
  foldRolesFrom targets.contains 0 [] code

/-- Every raw instruction is live and independent of call claims and folded sequences. -/
def plainBody : List RawInstruction → List Bool → Bool
  | [], _ => true
  | first :: rest, true :: live =>
    !boundSite first && (foldHead? first.opcode).isNone && plainBody rest live
  | _, _ => false

/-- At each plain site the mask is live, the role is absent, and no call claim applies. -/
theorem plainBody_at {closed : RawMethod} {reachable : List Bool}
    (plain : plainBody closed.code reachable)
    {pc : Nat} {raw : RawInstruction} (found : closed.code[pc]? = some raw) :
    reachable[pc]? = some true ∧ boundSite raw = false ∧
      (foldRoles closed.code)[pc]? = some none := by
  let targeted := (Std.TreeSet.ofList (branchTargets closed.code) compare).contains
  suffices walk : ∀ (code : List RawInstruction) (mask : List Bool) (start index : Nat),
      plainBody code mask = true → code[index]? = some raw →
        mask[index]? = some true ∧ boundSite raw = false ∧
          (foldRolesFrom targeted start [] code)[index]? = some none by
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
