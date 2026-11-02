import CIL.Extraction.MetadataNames

/-!
# Assembly attribution

An extraction may read method bodies from the selected assembly and from referenced
assemblies the caller pinned by SHA-256. Each method's evidence names the pin of the assembly
its body came from. `AssemblyPinsValid` checks that the pins are well formed, that two pins
agree exactly when they share an identity or bytes, and that every body is owned by the
assembly its pin names. Byte hashing and metadata decoding stay in the trusted extractor; the
certificate states which pinned inputs it was built from, as `docs/SOUNDNESS.md` describes.
-/

namespace CIL.Extraction

/-- One input assembly: its full metadata identity, module version id and the lowercase
    hexadecimal SHA-256 of its bytes. -/
structure AssemblyPin where
  identity : String := ""
  mvid : String := ""
  sha256 : String := ""
  deriving DecidableEq, Repr

/-- The number of hexadecimal digits in a SHA-256 digest. -/
def sha256Digits : Nat := 64

/-- A lowercase hexadecimal digit. -/
private def lowerHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- A nonempty identity with no colon, so `identity::` prefixes exactly one scope. -/
def pinIdentityValid (identity : String) : Bool :=
  let chars := metadataChars identity
  !chars.isEmpty && !chars.contains ':'

/-- The pin is well formed: a plain identity, a module version id and a full digest. -/
def AssemblyPin.wellFormed (pin : AssemblyPin) : Bool :=
  let digest := metadataChars pin.sha256
  pinIdentityValid pin.identity && !pin.mvid.isEmpty &&
    digest.length == sha256Digits && digest.all lowerHex

/-- `owner` is a scoped identity of the assembly `identity`: it begins with `identity::`. -/
def ownedBy (identity owner : String) : Bool :=
  (metadataChars identity ++ [':', ':']).isPrefixOf (metadataChars owner)

/-- Two pins name the same assembly exactly when they are equal, by identity and by bytes. -/
def pinsAgree (left right : AssemblyPin) : Bool :=
  (left.identity == right.identity) == (left == right) &&
    (left.sha256 == right.sha256) == (left == right)

/-- Every pin is well formed and no identity or digest names two different pins. -/
def pinsConsistent (pins : List AssemblyPin) : Bool :=
  pins.all fun left => left.wellFormed && pins.all (pinsAgree left)

/-- The assemblies a certificate's method bodies came from: each body's owner is scoped by
    its pin, and the pins are consistent across bodies. -/
def AssemblyPinsValid (pins : List AssemblyPin) (owners : List (AssemblyPin × String)) : Prop :=
  pinsConsistent (pins ++ owners.map Prod.fst) = true ∧
    ∀ entry ∈ owners, entry.1 ∈ pins ∧ ownedBy entry.1.identity entry.2 = true

instance (pins : List AssemblyPin) (owners : List (AssemblyPin × String)) :
    Decidable (AssemblyPinsValid pins owners) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A colon-free scope is determined by any string it prefixes before `::`. -/
private theorem scope_prefix_unique : ∀ {left right leftRest rightRest : List Char},
    ':' ∉ left → ':' ∉ right →
    left ++ ':' :: ':' :: leftRest = right ++ ':' :: ':' :: rightRest → left = right
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, noColon, joined => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at joined
    exact absurd (joined.1 ▸ List.mem_cons_self) noColon
  | _ :: _, [], _, _, noColon, _, joined => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at joined
    exact absurd (joined.1.symm ▸ List.mem_cons_self) noColon
  | head :: tail, other :: rest, _, _, leftColon, rightColon, joined => by
    simp only [List.cons_append, List.cons.injEq] at joined
    obtain ⟨same, tails⟩ := joined
    subst same
    rw [scope_prefix_unique (fun member => leftColon (List.mem_cons_of_mem _ member))
      (fun member => rightColon (List.mem_cons_of_mem _ member)) tails]

#print axioms scope_prefix_unique

/-- A valid identity scopes at most one assembly: no owner is attributed to two pins. -/
theorem ownedBy_unique {left right owner : String}
    (leftValid : pinIdentityValid left = true) (rightValid : pinIdentityValid right = true)
    (byLeft : ownedBy left owner = true) (byRight : ownedBy right owner = true) :
    left = right := by
  simp only [pinIdentityValid, metadataChars_eq, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at leftValid rightValid
  simp only [ownedBy, metadataChars_eq, List.isPrefixOf_iff_prefix] at byLeft byRight
  obtain ⟨leftSuffix, leftEq⟩ := byLeft
  obtain ⟨rightSuffix, rightEq⟩ := byRight
  have noColon {chars : List Char} (valid : ∀ c ∈ chars, ¬':' = c) : ':' ∉ chars :=
    fun member => valid ':' member rfl
  apply String.toList_inj.mp
  apply scope_prefix_unique (noColon leftValid.2) (noColon rightValid.2)
    (leftRest := leftSuffix) (rightRest := rightSuffix)
  simpa [List.append_assoc] using leftEq.trans rightEq.symm

#print axioms ownedBy_unique

end CIL.Extraction
