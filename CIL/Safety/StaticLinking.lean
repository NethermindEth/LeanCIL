import CIL.Safety.Linking
import CIL.Safety.ExecutionStaticWorld

/-!
# Static-checked linking

`linkChecked` links an application with its libraries and accepts the result only if no two
distinct static descriptors share an identity, so the linked program has one static world.
On a collision it reports the two conflicting fields.
-/

namespace CIL.Safety

/-- Descriptors with the same identity are equal, so an identity names one static field. -/
def StaticDescriptorsCompatible (descriptors : List CIL.StaticDescriptor) : Prop :=
  descriptors.Pairwise (fun left right => left.identity = right.identity → left = right)

instance (descriptors : List CIL.StaticDescriptor) :
    Decidable (StaticDescriptorsCompatible descriptors) :=
  inferInstanceAs (Decidable (descriptors.Pairwise _))

/-- The error message for incompatible descriptors, naming the first colliding pair found. -/
def staticCollision (descriptors : List CIL.StaticDescriptor) : String :=
  let pairs := descriptors.flatMap fun left => descriptors.map fun right => (left, right)
  match
    pairs.find? (fun (left, right) => left.identity == right.identity && !(left == right))
  with
  | none => "Static identity collision"
  | some (left, right) =>
    s!"Static identity collision {left.identity}: {left.assemblyIdentity}::{left.fieldName} and {right.assemblyIdentity}::{right.fieldName}"

/-- Links `app` with `libraries`, failing when two static descriptors collide. -/
def linkChecked (app : CIL.Program) (libraries : List Library) : Except String CIL.Program :=
  let linked := link app libraries
  let descriptors := programStaticDescriptors linked
  if StaticDescriptorsCompatible descriptors then .ok linked
  else .error (staticCollision descriptors)

theorem linkChecked_sound {app : CIL.Program} {libraries : List Library} {linked : CIL.Program}
    (checked : linkChecked app libraries = .ok linked) :
    linked = link app libraries ∧
      StaticDescriptorsCompatible (programStaticDescriptors linked) := by
  dsimp only [linkChecked] at checked
  split at checked
  next compatible =>
    cases checked
    exact ⟨rfl, compatible⟩
  next incompatible => cases checked

theorem linkChecked_of_compatible {app : CIL.Program} {libraries : List Library}
    (compatible : StaticDescriptorsCompatible (programStaticDescriptors (link app libraries))) :
    linkChecked app libraries = .ok (link app libraries) := by
  dsimp only [linkChecked]
  split
  · rfl
  · contradiction

theorem linkChecked_links {app : CIL.Program} {libraries : List Library} {linked : CIL.Program}
    (checked : linkChecked app libraries = .ok linked) : Links app linked := by
  rw [(linkChecked_sound checked).1]
  exact link_links app libraries

/-- Compatibility in the form `StaticWorldValid` asks for: any two members with the same
    identity are equal. -/
theorem StaticDescriptorsCompatible.identities {descriptors : List CIL.StaticDescriptor}
    (compatible : StaticDescriptorsCompatible descriptors) :
    ∀ left ∈ descriptors, ∀ right ∈ descriptors,
      left.identity = right.identity → left = right := by
  induction descriptors with
  | nil => simp
  | cons descriptor rest ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp compatible
    intro left leftMember right rightMember same
    rcases List.mem_cons.mp leftMember with equalLeft | leftMember
    · subst left
      rcases List.mem_cons.mp rightMember with equalRight | rightMember
      · subst right
        rfl
      · exact head right rightMember same
    · rcases List.mem_cons.mp rightMember with equalRight | rightMember
      · subst right
        exact (head left leftMember same.symm).symm
      · exact ih tail left leftMember right rightMember same

#print axioms linkChecked_sound
#print axioms linkChecked_of_compatible
#print axioms linkChecked_links
#print axioms StaticDescriptorsCompatible.identities

end CIL.Safety
