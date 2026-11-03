import CIL.Extraction.MetadataNames

/-!
# Assembly attribution

An extraction may read method bodies from the selected assembly and from referenced
assemblies the caller pinned by SHA-256. Each method's evidence names the identity of the
assembly its body came from, and `AttributionValid` checks that every body is owned by that
assembly. A pin carries the identity only: hashes and module version ids live in the artifact
manifest, where `check` recomputes them, so the certificate depends on the program alone, as
`docs/SOUNDNESS.md` describes.
-/

namespace CIL.Extraction

/-- One input assembly, named by its full metadata identity. -/
structure AssemblyPin where
  identity : String := ""
  deriving DecidableEq, Repr

/-- A nonempty identity with no colon, so `identity::` prefixes exactly one scope. -/
def pinIdentityValid (identity : String) : Bool :=
  let chars := metadataChars identity
  !chars.isEmpty && !chars.contains ':'

/-- `owner` is a scoped identity of the assembly `identity`: it begins with `identity::`. -/
def ownedBy (identity owner : String) : Bool :=
  (metadataChars identity ++ [':', ':']).isPrefixOf (metadataChars owner)

/-- Every body's pin is a valid identity that scopes the body's owner. -/
def AttributionValid (owners : List (AssemblyPin × String)) : Bool :=
  owners.all fun entry => pinIdentityValid entry.1.identity && ownedBy entry.1.identity entry.2

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
