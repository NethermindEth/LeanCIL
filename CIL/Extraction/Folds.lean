import CIL.Extraction.Generics
import Std.Data.TreeMap.Lemmas

/-!
# Folded instruction sequences

Some raw instruction sequences have no instruction-by-instruction translation and are
emitted as a unit: `typeof(A) == typeof(B)` becomes its decided Boolean, `throw new E(...)`
becomes one `throw`, and `stloc s; ldloca s` over a span local keeps the span on the stack.
`foldRoles` finds these sequences from the raw body alone and gives each instruction its
role, which the feature and scalar checks then enforce.
-/

namespace CIL.Extraction

/-- Characters allowed in a plain metadata name. -/
private def plainChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '/' || c == '`'

/-- Identifier-only names exclude modifiers, arrays and other decorated metadata spellings. -/
private def plainName (name : List Char) : Bool := !name.isEmpty && name.all plainChar

/-- A nonempty scope with no colon. -/
private def plainScope (scope : List Char) : Bool := !scope.isEmpty && !scope.contains ':'

/-- Split `scope::name` at its first colon; any other colon makes the identity unusable. -/
private def splitIdentity : List Char → List Char → Option (List Char × List Char)
  | scope, ':' :: ':' :: name => some (scope.reverse, name)
  | scope, c :: rest => if c == ':' then none else splitIdentity (c :: scope) rest
  | _, [] => none

/-- `(scope, name)` when both are plain. -/
private def leaf (scope name : List Char) : Option (List Char × List Char) :=
  if plainScope scope && plainName name then some (scope, name) else none

/-- Decode ASCII without repeated indexed UTF-8 reads during kernel reduction. -/
private def asciiChars : List UInt8 → Option (List Char)
  | [] => some []
  | byte :: bytes =>
    if byte.toNat < 128 then (Char.ofNat byte.toNat :: ·) <$> asciiChars bytes else none

/-- An ASCII byte is the complete UTF-8 encoding of its character. -/
private theorem asciiByte (byte : UInt8) (small : byte.toNat < 128) :
    String.utf8EncodeChar (Char.ofNat byte.toNat) = [byte] := by
  have valid : byte.toNat.isValidChar := by simp [Nat.isValidChar]; omega
  have bound : byte.toNat ≤ 127 := by omega
  simp [String.utf8EncodeChar, Char.ofNat, valid, Char.ofNatAux, bound]

#print axioms asciiByte

/-- Successful ASCII decoding preserves every input byte. -/
private theorem asciiChars_encode (bytes : List UInt8) (chars : List Char)
    (decoded : asciiChars bytes = some chars) :
    chars.utf8Encode.data.toList = bytes := by
  induction bytes generalizing chars with
  | nil => simp [asciiChars] at decoded; subst chars; rfl
  | cons byte bytes ih =>
    simp only [asciiChars] at decoded
    split at decoded
    next small =>
      cases tail : asciiChars bytes with
      | none => simp [tail] at decoded
      | some rest =>
        simp [tail] at decoded
        subst chars
        simpa [List.utf8Encode, List.flatMap_cons, asciiByte byte small] using ih rest tail
    next large => simp at decoded

#print axioms asciiChars_encode

/-- ASCII metadata uses a byte-list traversal; Unicode retains the full decoder. -/
private def metadataChars (value : String) : List Char :=
  match asciiChars value.toByteArray.data.toList with
  | some chars => chars
  | none => value.toList

/-- Metadata decoding preserves the original character sequence for every string. -/
private theorem metadataChars_eq (value : String) : metadataChars value = value.toList := by
  unfold metadataChars
  cases decoded : asciiChars value.toByteArray.data.toList with
  | none => rfl
  | some chars =>
    have encoded := asciiChars_encode _ _ decoded
    have same : String.ofList chars = value := by
      apply String.toByteArray_inj.mp
      simpa [String.toByteArray_ofList, ByteArray.ext_iff, Array.ext_iff] using encoded
    simpa using congrArg String.toList same

#print axioms metadataChars_eq

/-- A named type as its referencing scope and full name. -/
def namedType : TypeExpr → Option (List Char × List Char)
  | .atom scope name | .constructor scope name => leaf (metadataChars scope) (metadataChars name)
  | .aggregate identity _ | .enum identity _ => do
    let (scope, name) ← splitIdentity [] (metadataChars identity)
    leaf scope name
  | _ => none

/-- The fast metadata decoder retains the original named-type rule, including Unicode. -/
theorem namedType_eq_original (type : TypeExpr) : namedType type =
    match type with
    | .atom scope name | .constructor scope name => leaf scope.toList name.toList
    | .aggregate identity _ | .enum identity _ => do
      let (scope, name) ← splitIdentity [] identity.toList
      leaf scope name
    | _ => none := by
  cases type <;> simp only [namedType, metadataChars_eq]

#print axioms namedType_eq_original

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

/-- The exact call site of a static `System.Type` method with `parameters` parameters. -/
private def typeMethod (name signature : String) (parameters : Nat) : CallSite := {
  declaringType := .atom runtimeScope "System.Type", name,
  target := .external (runtimeScope ++ "::" ++ signature),
  typeArguments := [], parameterCount := parameters, hasThis := false, returnsValue := true,
  returnType := .atom runtimeScope
    (if name == "GetTypeFromHandle" then "System.Type" else "System.Boolean"),
  parameterTypes := if name == "GetTypeFromHandle" then
      [.atom runtimeScope "System.RuntimeTypeHandle"]
    else [.atom runtimeScope "System.Type", .atom runtimeScope "System.Type"] }

private def getTypeFromHandle : CallSite :=
  typeMethod "GetTypeFromHandle"
    "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)" 1

/-- Exactly `call Type.GetTypeFromHandle`. -/
private def typeFromHandle (instruction : RawInstruction) : Bool :=
  instruction.opcode == 40 && instruction.operand == .call getTypeFromHandle

/-- `some true` for `op_Equality`, `some false` for `op_Inequality`. -/
private def typeComparison (instruction : RawInstruction) : Option Bool :=
  if instruction.opcode != 40 then none
  else if instruction.operand == .call (typeMethod "op_Equality"
      "System.Boolean System.Type::op_Equality(System.Type,System.Type)" 2) then some true
  else if instruction.operand == .call (typeMethod "op_Inequality"
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

/-- The local a `ldloc`, `stloc` or `ldloca` instruction names, in any of its forms. -/
def localIndex (instruction : RawInstruction) : Option Nat :=
  match instruction.opcode, instruction.operand with
  -- `ldloc.0` to `ldloc.3` and `stloc.0` to `stloc.3`.
  | 6, .none | 10, .none => some 0
  | 7, .none | 11, .none => some 1
  | 8, .none | 12, .none => some 2
  | 9, .none | 13, .none => some 3
  -- `ldloc`, `ldloca` and `stloc`, short and long forms.
  | 17, .local n | 18, .local n | 19, .local n
  | 65036, .local n | 65037, .local n | 65038, .local n => some n
  | _, _ => none

/-- Whether `instruction` names a typed span local. -/
def spanLocalOp (locals : List TypeExpr) (instruction : RawInstruction) : Bool :=
  match localIndex instruction with
  | some index => (locals[index]?.map spanLocal).getD false
  | none => false

/-- `stloc s; ldloca s` over a span local `s`: the span stays on the stack as the receiver. -/
def receiverFold (locals : List TypeExpr) (a b : RawInstruction) : Bool :=
  a.opcode ∈ [10, 11, 12, 13, 19, 65038] && (b.opcode == 18 || b.opcode == 65037) &&
    localIndex a == localIndex b && spanLocalOp locals a

/-- A receiver fold ends at a length call or an item call with a single index push. -/
private def spanReceiverUse (code : List RawInstruction) : Bool :=
  let member (instruction : RawInstruction) (name : String) :=
    match instruction with
    | ⟨_, 40, .call site⟩ => site.hasThis && site.name == name && spanLocal site.declaringType
    | _ => false
  match code with
  | call :: _ =>
    member call "get_Length" || match code with
    | index :: call :: _ =>
      index.opcode ∈ [2, 3, 4, 5, 14, 65033, 6, 7, 8, 9, 17, 65036,
        21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] && member call "get_Item"
    | _ => false
  | _ => false

/-- `ldstr` (114) or `ldnull` (20): a message argument of a folded `throw`. -/
private def messageLoad (instruction : RawInstruction) : Bool :=
  instruction.opcode == 114 || instruction.opcode == 20

/-- Admitted framework exceptions with parameterless/string constructors, plus the three
    argument exceptions' two-string overloads. Other constructors remain unsupported. -/
def exceptionConstructor (name : String) (count : Nat) : Bool :=
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

/-- An exact allowlisted `System.Runtime` constructor, including its complete signature. -/
private def raisedType (count : Nat) : RawInstruction → Option String
  | ⟨_, 115, .call site⟩ => match site.declaringType, site.target with
    | .atom scope name, .external signature =>
      if scope == runtimeScope && exceptionConstructor name count &&
        signature == runtimeScope ++ "::System.Void " ++ name ++ "::.ctor(" ++
          ",".intercalate (List.replicate count "System.String") ++ ")" &&
        site.name == ".ctor" && site.hasThis && !site.returnsValue &&
        site.typeArguments.isEmpty && site.parameterCount == count then some name else none
    | _, _ => none
  | _ => none

/-- One beyond the largest admitted message arity; reaching it rules out a throw fold. -/
private def throwMessageLimit : Nat := 3

/-- `throw new E(...)` with only string or null arguments: the argument count and raised type. -/
def throwFold (code : List RawInstruction) : Option (Nat × String) :=
  let count := ((code.take throwMessageLimit).takeWhile messageLoad).length
  if count == throwMessageLimit then none else
  match code.drop count with
  | constructor :: ⟨_, 122, .none⟩ :: _ => (count, ·) <$> raisedType count constructor
  | _ => none

/-- Admitted exception constructors never consume more than two message arguments. -/
private theorem raisedType_large (count : Nat) (instruction : RawInstruction)
    (large : 2 < count) : raisedType count instruction = none := by
  have notOne : ¬ count ≤ 1 := by omega
  have notTwo : count ≠ 2 := by omega
  unfold raisedType
  split <;> try rfl
  split <;> simp_all [exceptionConstructor] <;> omega

#print axioms raisedType_large

/-- Bounding message-prefix inspection preserves the original unrestricted fold test. -/
theorem throwFold_eq_takeWhile (code : List RawInstruction) :
    throwFold code =
      let count := (code.takeWhile messageLoad).length
      match code.drop count with
      | constructor :: ⟨_, 122, .none⟩ :: _ => (count, ·) <$> raisedType count constructor
      | _ => none := by
  unfold throwFold throwMessageLimit
  rw [← List.take_takeWhile, List.length_take]
  by_cases short : (code.takeWhile messageLoad).length ≤ 2
  · have bound : min 3 (code.takeWhile messageLoad).length =
        (code.takeWhile messageLoad).length := by omega
    have notThree : (code.takeWhile messageLoad).length ≠ 3 := by omega
    simp only [bound, beq_iff_eq, notThree, ↓reduceIte]
  · have bound : min 3 (code.takeWhile messageLoad).length = 3 := by omega
    have large : 2 < (code.takeWhile messageLoad).length := by omega
    simp only [bound, beq_self_eq_true, ↓reduceIte]
    split <;> simp [raisedType_large _ _ large]

#print axioms throwFold_eq_takeWhile

/-- An instruction's part in a folded sequence. -/
inductive FoldRole where
  /-- The first instruction: emits nothing, and may be a branch target. -/
  | head
  /-- Later instructions: emit nothing, and are entered only from the preceding instruction. -/
  | interior
  /-- A type comparison: pushes the decided Boolean. -/
  | result (value : Bool)
  /-- The raw `throw`: raises the constructed type. -/
  | raise (exception : String)
  deriving DecidableEq, Repr

/-- The roles of a fold starting at `a`, if any; type tests take precedence. -/
private def foldAt (locals : List TypeExpr) (a : RawInstruction) (tail : List RawInstruction) :
    Option (List (Option FoldRole)) :=
  (match tail with
    | b :: rest => if receiverFold locals a b && spanReceiverUse rest then
        some [some .head, some .interior] else none
    | _ => none) <|>
  (match tail with
    | b :: c :: d :: e :: _ => (typeTest a b c d e).map fun value =>
        [some .head, some .interior, some .interior, some .interior, some (.result value)]
    | _ => none) <|>
  (throwFold (a :: tail)).map fun (count, name) =>
    some .head :: List.replicate count (some .interior) ++ [some (.raise name)]

/-- Assign `pending` roles first; each step consumes one instruction, so the walk is structural. -/
def foldRolesFrom (locals : List TypeExpr) :
    List (Option FoldRole) → List RawInstruction → List (Option FoldRole)
  | _, [] => []
  | role :: pending, _ :: tail => role :: foldRolesFrom locals pending tail
  | [], a :: tail => match foldAt locals a tail with
    | some (role :: pending) => role :: foldRolesFrom locals pending tail
    | _ => none :: foldRolesFrom locals [] tail

/-- Exact counts of decoded local operands, including indexes outside the declared locals. -/
private def localUseCounts : List RawInstruction → Std.TreeMap Nat Nat
  | [] => ∅
  | instruction :: rest =>
    let counts := localUseCounts rest
    match localIndex instruction with
    | none => counts
    | some index => counts.insert index (counts.getD index 0 + 1)

/-- Each indexed count equals the original raw-instruction filter, even for malformed operands. -/
private theorem localUseCounts_get (code : List RawInstruction) (index : Nat) :
    (localUseCounts code).getD index 0 =
      (code.filter fun instruction => localIndex instruction == some index).length := by
  induction code with
  | nil => simp [localUseCounts]
  | cons instruction rest ih =>
    cases decoded : localIndex instruction with
    | none => simp [localUseCounts, decoded, ih]
    | some decodedIndex =>
      simp only [localUseCounts, decoded, Std.TreeMap.getD_insert, Nat.compare_eq_eq]
      by_cases same : decodedIndex = index
      · simp [same, decoded, ih]
      · simp [same, decoded, ih]

#print axioms localUseCounts_get

/-- Roles derived from the raw body alone; extraction evidence cannot add or move a fold. -/
def foldRoles (locals : List TypeExpr) (code : List RawInstruction) : List (Option FoldRole) :=
  if locals.isEmpty then foldRolesFrom [] [] code else
  let counts := localUseCounts code
  let singleUse := locals.zipIdx.map fun (type, index) =>
    if counts.getD index 0 == 2 then type else .void
  foldRolesFrom singleUse [] code

/-- Indexed role discovery agrees with filtering the whole body separately for each local. -/
theorem foldRoles_eq_filter (locals : List TypeExpr) (code : List RawInstruction) :
    foldRoles locals code = foldRolesFrom
      (locals.zipIdx.map fun (type, index) =>
        if (code.filter fun instruction => localIndex instruction == some index).length == 2
          then type else .void) [] code := by
  cases locals <;> simp only [foldRoles, List.isEmpty_nil, List.isEmpty_cons,
    Bool.false_eq_true, ↓reduceIte, List.zipIdx_nil, List.map_nil, localUseCounts_get]

#print axioms foldRoles_eq_filter

/-- A non-fallthrough edge may enter a fold only at its first instruction. -/
def foldEntry (role : Option (Option FoldRole)) : Bool :=
  match role with
  | some (some .interior) | some (some (.result _)) | some (some (.raise _)) => false
  | _ => true

end CIL.Extraction
