import CIL.TypeExpr
import CIL.Extraction.KernelEquation

/-!
# Exact named metadata identities

Span signatures, folded type tests and generic call targets share a kernel-reducible decoder
for scoped type names. The ASCII fast path is proved equivalent to Unicode character decoding.
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
def asciiChars (bytes : List UInt8) : Option (List Char) :=
  if bytes.all (fun byte => byte.toNat < 128) then
    some (bytes.map fun byte => Char.ofNat byte.toNat)
  else none

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
  unfold asciiChars at decoded
  split at decoded
  next small =>
    cases decoded
    simp only [List.all_eq_true, decide_eq_true_eq] at small
    induction bytes with
    | nil => rfl
    | cons byte bytes ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at small
      simpa [List.utf8Encode, List.flatMap_cons, asciiByte byte small.1] using ih small.2
  next => cases decoded

#print axioms asciiChars_encode

/-- ASCII metadata uses a byte-list traversal; Unicode retains the full decoder. -/
def metadataChars (value : String) : List Char :=
  match asciiChars value.toByteArray.data.toList with
  | some chars => chars
  | none =>
    let bytes := value.toByteArray.data.toList.map UInt8.toNat
    (utf8Characters bytes.length bytes).getD []

/-- Metadata decoding preserves the original character sequence for every string. -/
theorem metadataChars_eq (value : String) : metadataChars value = value.toList := by
  unfold metadataChars
  cases decoded : asciiChars value.toByteArray.data.toList with
  | none =>
    obtain ⟨chars, rfl⟩ : ∃ chars, value = String.ofList chars :=
      ⟨value.toList, String.ofList_toList.symm⟩
    have bytes : (String.ofList chars).toByteArray.data.toList.map UInt8.toNat =
        chars.flatMap fun char => (String.utf8EncodeChar char).map UInt8.toNat := by
      simp [String.toByteArray_ofList, List.utf8Encode, List.map_flatMap]
    rw [bytes]
    dsimp only
    rw [utf8Characters_decode chars _ (Nat.le_refl _), String.toList_ofList]
    rfl
  | some chars =>
    have encoded := asciiChars_encode _ _ decoded
    have same : String.ofList chars = value := by
      apply String.toByteArray_inj.mp
      simpa [String.toByteArray_ofList, ByteArray.ext_iff, Array.ext_iff] using encoded
    simpa using congrArg String.toList same

#print axioms metadataChars_eq

/-- Splitting a metadata identity consumes exactly the first double colon. -/
private theorem splitIdentity_parts {reversed input scope name : List Char}
    (split : splitIdentity reversed input = some (scope, name)) :
    reversed.reverse ++ input = scope ++ ':' :: ':' :: name := by
  fun_induction splitIdentity reversed input <;> simp_all [List.append_assoc]

#print axioms splitIdentity_parts

/-- The assembly prefix of a flat metadata identity. Generic arguments may carry further scopes. -/
def flatOwnerScope? (identity : String) : Option String := do
  let (scope, name) ← splitIdentity [] (metadataChars identity)
  if plainScope scope && !name.isEmpty then return String.ofList scope else none

/-- Every scope returned by the parser is followed by the metadata ownership separator. -/
theorem flatOwnerScope?_prefix {identity scope : String}
    (found : flatOwnerScope? identity = some scope) :
    (metadataChars scope ++ [':', ':']).isPrefixOf (metadataChars identity) = true := by
  unfold flatOwnerScope? at found
  cases split : splitIdentity [] (metadataChars identity) with
  | none => simp [split] at found
  | some pair =>
    obtain ⟨assembly, suffix⟩ := pair
    simp only [split] at found
    change (if plainScope assembly && !suffix.isEmpty then some (String.ofList assembly)
      else none) = some scope at found
    split at found
    · cases found
      have parts := splitIdentity_parts split
      simp only [List.reverse_nil, List.nil_append] at parts
      rw [parts, metadataChars_eq]
      simp [List.isPrefixOf_iff_prefix, List.IsPrefix, List.append_assoc]
    · contradiction
#print axioms flatOwnerScope?_prefix


/-- A class name usable by metadata operations that accept only a plain, unambiguous spelling. -/
private def plainSpelling? (name : ClassName) : Option String := do
  let text ← name.signatureName?
  guard (ClassName.ofText text == name)
  return text

/-- A named type as its referencing scope and full name. -/
def namedType : TypeExpr → Option (List Char × List Char)
  | .primitive type => leaf (metadataChars runtimeScope) (metadataChars type.display)
  | .atom scope name => leaf (metadataChars scope) (metadataChars name)
  | .constructor scope name | .objectConstructor scope name => do
    leaf (metadataChars scope) (metadataChars (← plainSpelling? name))
  | .enum identity _ => do
    leaf (metadataChars (← assemblyScope? identity.assembly))
      (metadataChars (← plainSpelling? ⟨identity.levels⟩))
  | .aggregate identity _ => do
    let (scope, name) ← splitIdentity [] (metadataChars identity)
    leaf scope name
  | _ => none

/-- The fast metadata decoder retains the original named-type rule, including Unicode. -/
theorem namedType_eq_original (type : TypeExpr) : namedType type =
    match type with
    | .primitive type => leaf runtimeScope.toList type.display.toList
    | .atom scope name => leaf scope.toList name.toList
    | .constructor scope name | .objectConstructor scope name => do
      leaf scope.toList (← plainSpelling? name).toList
    | .enum identity _ => do
      leaf (← assemblyScope? identity.assembly).toList (← plainSpelling? ⟨identity.levels⟩).toList
    | .aggregate identity _ => do
      let (scope, name) ← splitIdentity [] identity.toList
      leaf scope name
    | _ => none := by
  cases type <;> simp only [namedType, metadataChars_eq]

#print axioms namedType_eq_original

/-- A named type's plain full name; an atom's or generic definition's scope is left undecoded. -/
def plainTypeName : TypeExpr → Option (List Char)
  | .constructor _ name | .objectConstructor _ name => do
    let chars := metadataChars (← plainSpelling? name)
    if plainName chars then some chars else none
  | .atom _ name =>
    let name := metadataChars name
    if plainName name then some name else none
  | type => Prod.snd <$> namedType type

/-- Remove an exact byte prefix, rejecting mismatches and truncated identities. -/
def stripIdentityPrefix : List UInt8 → List UInt8 → Option (List UInt8)
  | [], bytes => some bytes
  | first :: expected, actual :: bytes =>
    if first == actual then stripIdentityPrefix expected bytes else none
  | _, _ => none

/-- Prefix removal succeeds exactly for the original prefix followed by the returned bytes. -/
theorem stripIdentityPrefix_eq (expected bytes suffix : List UInt8) :
    stripIdentityPrefix expected bytes = some suffix ↔ bytes = expected ++ suffix := by
  induction expected generalizing bytes with
  | nil => simp [stripIdentityPrefix]
  | cons first expected ih =>
    cases bytes with
    | nil => simp [stripIdentityPrefix]
    | cons actual bytes =>
      by_cases equal : first = actual
      · subst actual
        simp [stripIdentityPrefix, ih]
      · simp [stripIdentityPrefix, equal, beq_iff_eq, Ne.symm equal]
#print axioms stripIdentityPrefix_eq

/-- A scoped argument starts with an assembly identity; commas inside it have a following space. -/
private def afterArgumentScope : List Char → Option (List Char)
  | ':' :: ':' :: rest => some rest
  | '<' :: _ | '>' :: _ => none
  | ',' :: ' ' :: rest => afterArgumentScope rest
  | ',' :: _ => none
  | _ :: rest => afterArgumentScope rest
  | [] => none

/-- Runtime signatures omit nested argument scopes while metadata identities retain them. -/
private def unscopedArguments : Nat → List Char → List Char
  | 0, chars => chars
  | _ + 1, [] => []
  | fuel + 1, '<' :: rest =>
    '<' :: unscopedArguments fuel ((afterArgumentScope rest).getD rest)
  | fuel + 1, ',' :: rest =>
    ',' :: unscopedArguments fuel ((afterArgumentScope rest).getD rest)
  | fuel + 1, char :: rest => char :: unscopedArguments fuel rest

/-- The runtime signature spelling of a scoped aggregate identity, nested arguments included. -/
def aggregateName (identity : String) : Option (List Char) := do
  let name ← afterArgumentScope (metadataChars identity)
  let name := unscopedArguments name.length name
  if name.isEmpty then none else return name

/-- Pointer, byref, array and generic instance types, which are never equal to a named type. -/
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
  | .enum a x, .enum b y =>
    if a.levels != b.levels then some false else if a == b then some (x == y) else none
  | .constructor s a, .constructor t b | .objectConstructor s a, .objectConstructor t b =>
    if a != b then some false else if s == t then some true else none
  | .constructor .., .objectConstructor .. | .objectConstructor .., .constructor .. => some false
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

/-- A repeated aggregate operand with the same scoped name and layout has the same runtime type. -/
theorem sameRuntimeType_aggregate_self (identity : String) (layout : Nat) :
    sameRuntimeType (.aggregate identity layout) (.aggregate identity layout) = some true := by
  simp [sameRuntimeType]

#print axioms sameRuntimeType_aggregate_self

/-- The separate assembly name on a metadata type head. Flat owners carry it inside the name. -/
def TypeExpr.explicitHeadScope : TypeExpr → Option String
  | .primitive _ => some runtimeScope
  | .atom scope _ | .object scope _ | .constructor scope _ | .objectConstructor scope _ =>
    some scope
  | .apply head _ => head.explicitHeadScope
  | _ => none

/-- The assembly of the declaring type, including a scope embedded in an aggregate or enum name. -/
def TypeExpr.headScope : TypeExpr → Option String
  | .enum identity _ => assemblyScope? identity.assembly
  | .aggregate identity _ => flatOwnerScope? identity
  | .apply head _ => head.headScope
  | type => type.explicitHeadScope

end CIL.Extraction
