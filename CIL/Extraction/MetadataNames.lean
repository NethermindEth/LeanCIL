import CIL.TypeExpr

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
def asciiChars : List UInt8 → Option (List Char)
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
def metadataChars (value : String) : List Char :=
  match asciiChars value.toByteArray.data.toList with
  | some chars => chars
  | none => value.toList

/-- Metadata decoding preserves the original character sequence for every string. -/
theorem metadataChars_eq (value : String) : metadataChars value = value.toList := by
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

/-- A named type's plain full name; an atom's or constructor's scope is left undecoded. -/
def plainTypeName : TypeExpr → Option (List Char)
  | .atom _ name | .constructor _ name =>
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
  let name ← afterArgumentScope identity.toList
  let name := unscopedArguments name.length name
  if name.isEmpty then none else return name

end CIL.Extraction
