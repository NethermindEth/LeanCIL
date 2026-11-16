import CIL.Safety.Linking
import CIL.Safety.ExecutionStaticWorld

/-!
# Static-checked linking

`linkChecked` links an application with its libraries and accepts the result only if no two
distinct static descriptors share an identity, so the linked program has one static world.
On a collision it reports the first two conflicting descriptors as a `StaticCollision`.
-/

namespace CIL.Safety

/-- Descriptors with the same identity are equal, so an identity names one static field. -/
def StaticDescriptorsCompatible (descriptors : List CIL.StaticDescriptor) : Prop :=
  descriptors.Pairwise (fun left right => left.identity = right.identity → left = right)

instance (descriptors : List CIL.StaticDescriptor) :
    Decidable (StaticDescriptorsCompatible descriptors) :=
  inferInstanceAs (Decidable (descriptors.Pairwise _))

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

/-- Two descriptors that share an identity and differ, as `linkChecked` reports them. -/
structure StaticCollision where
  left : CIL.StaticDescriptor
  right : CIL.StaticDescriptor
  deriving DecidableEq, Repr

/-- The report of a collision, naming its identity and both fields. -/
def StaticCollision.message (collision : StaticCollision) : String :=
  s!"Static identity collision {collision.left.identity}: {reprStr collision.left.field}" ++
    s!" and {reprStr collision.right.field}"

/-- The first pair of descriptors, in list order, that share an identity and differ. -/
def firstCollision (descriptors : List CIL.StaticDescriptor) : Option StaticCollision :=
  let pairs := descriptors.flatMap fun left => descriptors.map fun right => (left, right)
  (pairs.find? fun (left, right) => left.identity == right.identity && !(left == right)).map
    fun (left, right) => { left, right }

/-- Descriptors with no collision are compatible, and compatible ones have none. -/
theorem firstCollision_eq_none {descriptors : List CIL.StaticDescriptor} :
    firstCollision descriptors = none ↔ StaticDescriptorsCompatible descriptors := by
  simp only [firstCollision, Option.map_eq_none_iff, List.find?_eq_none, List.mem_flatMap,
    List.mem_map, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
  constructor
  · intro none
    refine List.pairwise_of_forall_mem_list fun left leftMember right rightMember same => ?_
    exact Classical.byContradiction fun different =>
      none (left, right) ⟨left, leftMember, right, rightMember, rfl⟩ ⟨same, different⟩
  · intro compatible pair member found
    obtain ⟨left, leftMember, right, rightMember, rfl⟩ := member
    exact found.2 (compatible.identities left leftMember right rightMember found.1)

/-- Links `app` with `libraries`, failing with the first collision of two static
    descriptors. -/
def linkChecked (app : CIL.Program) (libraries : List Library) :
    Except StaticCollision CIL.Program :=
  let linked := link app libraries
  match firstCollision (programStaticDescriptors linked) with
  | none => .ok linked
  | some collision => .error collision

theorem linkChecked_sound {app : CIL.Program} {libraries : List Library} {linked : CIL.Program}
    (checked : linkChecked app libraries = .ok linked) :
    linked = link app libraries ∧
      StaticDescriptorsCompatible (programStaticDescriptors linked) := by
  dsimp only [linkChecked] at checked
  split at checked
  next none =>
    cases checked
    exact ⟨rfl, firstCollision_eq_none.mp none⟩
  next => cases checked

theorem linkChecked_of_compatible {app : CIL.Program} {libraries : List Library}
    (compatible : StaticDescriptorsCompatible (programStaticDescriptors (link app libraries))) :
    linkChecked app libraries = .ok (link app libraries) := by
  dsimp only [linkChecked]
  rw [firstCollision_eq_none.mpr compatible]

/-- `linkChecked` fails with the first collision of the linked program's descriptors. -/
theorem linkChecked_of_collision {app : CIL.Program} {libraries : List Library}
    {collision : StaticCollision}
    (found : firstCollision (programStaticDescriptors (link app libraries)) = some collision) :
    linkChecked app libraries = .error collision := by
  dsimp only [linkChecked]
  rw [found]

theorem linkChecked_links {app : CIL.Program} {libraries : List Library} {linked : CIL.Program}
    (checked : linkChecked app libraries = .ok linked) : Links app linked := by
  rw [(linkChecked_sound checked).1]
  exact link_links app libraries

#print axioms firstCollision_eq_none
#print axioms linkChecked_sound
#print axioms linkChecked_of_compatible
#print axioms linkChecked_links
#print axioms linkChecked_of_collision
#print axioms StaticDescriptorsCompatible.identities

end CIL.Safety
