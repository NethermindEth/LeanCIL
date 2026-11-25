import CIL.Extraction.MetadataBytes
import CIL.Extraction.MetadataNames

/-!
# Assembly attribution

An extraction may read method bodies from the selected assembly and from referenced
assemblies the caller pinned by SHA-256. Each method's evidence names the identity of the
assembly its body came from, and `AttributionValid` checks that every body's owner is defined
in that assembly, comparing typed `AssemblyName` values. A pin carries the identity only:
hashes and module version ids live in the artifact manifest, where `check` recomputes them, so
the certificate depends on the program alone, as `docs/SOUNDNESS.md` describes.
-/

namespace CIL.Extraction

/-- One input assembly, named by its full metadata identity. -/
structure AssemblyPin where
  identity : AssemblyName
  deriving DecidableEq, Repr

/-- `owner` is a scoped identity of the assembly `identity`: it begins with `identity::`. -/
def ownedBy (identity owner : String) : Bool :=
  (metadataChars identity ++ [':', ':']).isPrefixOf (metadataChars owner)

/-- The type identity text `owner` begins with `assembly`'s colon-free spelling and `::`. Type
    identities are text, so a typed assembly meets a scoped type name here and in `spelledAs`. -/
def _root_.CIL.AssemblyName.scopes (assembly : AssemblyName) (owner : String) : Bool :=
  assembly.colonFree && (assembly.spelling ++ [58, 58]).isPrefixOf (bytesOf owner)

/-- A colon-free byte string is determined by any string it prefixes before `::`. -/
private theorem spelling_prefix_unique : ∀ {left right leftRest rightRest : List Nat},
    58 ∉ left → 58 ∉ right →
    left ++ 58 :: 58 :: leftRest = right ++ 58 :: 58 :: rightRest → left = right
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
    rw [spelling_prefix_unique (fun member => leftColon (List.mem_cons_of_mem _ member))
      (fun member => rightColon (List.mem_cons_of_mem _ member)) tails]

#print axioms spelling_prefix_unique

/-- Two assemblies that scope one owner spell alike, so an owner's text selects one spelling. -/
theorem _root_.CIL.AssemblyName.scopes_unique {left right : AssemblyName} {owner : String}
    (byLeft : left.scopes owner = true) (byRight : right.scopes owner = true) :
    left.spelling = right.spelling := by
  simp only [AssemblyName.scopes, AssemblyName.colonFree, Bool.and_eq_true, Bool.not_eq_true',
    List.isPrefixOf_iff_prefix] at byLeft byRight
  obtain ⟨leftFree, leftSuffix, leftEq⟩ := byLeft
  obtain ⟨rightFree, rightSuffix, rightEq⟩ := byRight
  have noColon {bytes : List Nat} (free : bytes.contains 58 = false) : 58 ∉ bytes :=
    fun member => by rw [List.contains_iff_mem.mpr member] at free; cases free
  apply spelling_prefix_unique (noColon leftFree) (noColon rightFree)
    (leftRest := leftSuffix) (rightRest := rightSuffix)
  simpa [List.append_assoc] using leftEq.trans rightEq.symm

#print axioms CIL.AssemblyName.scopes_unique

/-- Every body's owner is defined in the assembly its pin names. An owner whose assembly Lean
    did not read is refused. -/
def AttributionValid (owners : List (AssemblyPin × Option AssemblyName)) : Bool :=
  owners.all fun (pin, owner) => owner == some pin.identity

end CIL.Extraction
