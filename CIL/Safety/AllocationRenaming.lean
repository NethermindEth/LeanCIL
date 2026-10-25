import CIL.Safety.Memory

/-!
# Extensible allocation identity maps

A mapping injects the allocated source prefix into the allocated target prefix.
Paired allocations extend both prefixes; target-only private homes extend only the
target prefix. Extensions keep every previously allocated identity unchanged.
-/

namespace CIL.Safety

/-- An injective map of allocated identities; the target may contain additional private homes. -/
structure AllocationRenaming where
  sourceLimit : Nat
  targetLimit : Nat
  image : AllocationId → AllocationId
  bounded : ∀ identity, identity < sourceLimit → image identity < targetLimit
  injective : ∀ left right, left < sourceLimit → right < sourceLimit →
    image left = image right → left = right

namespace AllocationRenaming

/-- Caller allocations initially have exactly the same identities in both executions. -/
def identity (limit : Nat) : AllocationRenaming :=
  ⟨limit, limit, id, fun _ bound => bound, fun _ _ _ _ equal => equal⟩

/-- An extension retains the images of every identity already allocated in the source. -/
structure Extends (earlier later : AllocationRenaming) : Prop where
  source : earlier.sourceLimit ≤ later.sourceLimit
  target : earlier.targetLimit ≤ later.targetLimit
  image : ∀ identity, identity < earlier.sourceLimit → later.image identity = earlier.image identity
  fresh : ∀ identity, earlier.sourceLimit ≤ identity → identity < later.sourceLimit →
    earlier.targetLimit ≤ later.image identity

/-- A mapping always extends itself. -/
theorem Extends.refl (mapping : AllocationRenaming) : mapping.Extends mapping :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl,
    fun _ lower upper => False.elim (Nat.not_lt_of_ge lower upper)⟩
#print axioms Extends.refl

/-- Extensions through nested calls retain all mappings from the caller. -/
theorem Extends.trans {first middle last : AllocationRenaming}
    (left : first.Extends middle) (right : middle.Extends last) : first.Extends last :=
  ⟨Nat.le_trans left.source right.source, Nat.le_trans left.target right.target,
    fun identity bound => (right.image identity (Nat.lt_of_lt_of_le bound left.source)).trans
      (left.image identity bound), by
      intro identity lower upper
      by_cases old : identity < middle.sourceLimit
      · rw [right.image identity old]
        exact left.fresh identity lower old
      · exact Nat.le_trans left.target (right.fresh identity (Nat.le_of_not_gt old) upper)⟩
#print axioms Extends.trans

/-- Allocating a target-only dead home does not change any source identity's image. -/
def skipTarget (mapping : AllocationRenaming) : AllocationRenaming := {
  mapping with
  targetLimit := mapping.targetLimit + 1
  bounded := fun identity bound => Nat.lt_succ_of_lt (mapping.bounded identity bound) }

/-- Adding a target-only private home retains all earlier mappings. -/
theorem skipTarget_extends (mapping : AllocationRenaming) :
    mapping.Extends mapping.skipTarget :=
  ⟨Nat.le_refl _, Nat.le_add_right _ _, fun _ _ => rfl,
    fun _ lower upper => False.elim (Nat.not_lt_of_ge lower upper)⟩
#print axioms skipTarget_extends

/-- Paired allocations map the fresh source identity to the fresh target identity. -/
def allocate (mapping : AllocationRenaming) : AllocationRenaming where
  sourceLimit := mapping.sourceLimit + 1
  targetLimit := mapping.targetLimit + 1
  image identity := if identity < mapping.sourceLimit then mapping.image identity
    else mapping.targetLimit
  bounded identity bound := by
    split
    · exact Nat.lt_succ_of_lt (mapping.bounded identity ‹_›)
    · exact Nat.lt_succ_self _
  injective left right leftBound rightBound equal := by
    by_cases leftOld : left < mapping.sourceLimit
    · by_cases rightOld : right < mapping.sourceLimit
      · simp only [leftOld, rightOld, ite_true] at equal
        exact mapping.injective left right leftOld rightOld equal
      · simp only [leftOld, rightOld, ite_true, ite_false] at equal
        have bounded := mapping.bounded left leftOld
        exact False.elim ((Nat.ne_of_lt bounded) equal)
    · by_cases rightOld : right < mapping.sourceLimit
      · simp only [leftOld, rightOld, ite_true, ite_false] at equal
        have bounded := mapping.bounded right rightOld
        exact False.elim ((Nat.ne_of_lt bounded) equal.symm)
      · omega

/-- Paired allocation preserves the mapping of every previously allocated identity. -/
theorem allocate_extends (mapping : AllocationRenaming) : mapping.Extends mapping.allocate :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, fun identity bound => by
    simp only [allocate, bound, ite_true], by
    intro identity lower _
    simp only [allocate, Nat.not_lt_of_ge lower, ite_false, Nat.le_refl]⟩
#print axioms allocate_extends

/-- The newly allocated identity maps to the target's previous allocation watermark. -/
theorem allocate_fresh (mapping : AllocationRenaming) :
    mapping.allocate.image mapping.sourceLimit = mapping.targetLimit := by
  simp [allocate]
#print axioms allocate_fresh

/-- Previously allocated private target identities stay outside every extended source image. -/
theorem Extends.private {earlier later : AllocationRenaming} (extension : earlier.Extends later)
    (privateIdentity : AllocationId) (allocated : privateIdentity < earlier.targetLimit)
    (privateHome : ∀ identity, identity < earlier.sourceLimit →
      earlier.image identity ≠ privateIdentity) :
    ∀ identity, identity < later.sourceLimit → later.image identity ≠ privateIdentity := by
  intro identity bound
  by_cases old : identity < earlier.sourceLimit
  · rw [extension.image identity old]
    exact privateHome identity old
  · have fresh := extension.fresh identity (Nat.le_of_not_gt old) bound
    exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated fresh)).symm
#print axioms Extends.private
/-- Rename an allocation-backed reference without changing its byte offset. -/
def reference (mapping : AllocationRenaming) (reference : Reference) : Reference :=
  { reference with allocation := mapping.image reference.allocation }

/-- Later allocations cannot change a reference to already allocated storage. -/
theorem Extends.reference {earlier later : AllocationRenaming} (extension : earlier.Extends later)
    (reference : Reference) (bound : reference.allocation < earlier.sourceLimit) :
    later.reference reference = earlier.reference reference := by
  simp only [AllocationRenaming.reference, extension.image reference.allocation bound]
#print axioms Extends.reference

/-- Reference equality is preserved on the allocated source prefix. -/
theorem reference_injective (mapping : AllocationRenaming) (left right : Reference)
    (leftBound : left.allocation < mapping.sourceLimit)
    (rightBound : right.allocation < mapping.sourceLimit)
    (equal : mapping.reference left = mapping.reference right) : left = right := by
  have allocations := congrArg Reference.allocation equal
  have offsets := congrArg Reference.offset equal
  have same := mapping.injective _ _ leftBound rightBound allocations
  cases left
  cases right
  simp_all [reference]
#print axioms reference_injective

/-- Rename a permission view without changing its range or read/write authority. -/
def view (mapping : AllocationRenaming) (view : View) : View :=
  { view with allocation := mapping.image view.allocation }

/-- Corresponding views cover exactly the same byte offsets of allocated references. -/
theorem viewContains (mapping : AllocationRenaming) (permission : View) (reference : Reference)
    (viewBound : permission.allocation < mapping.sourceLimit)
    (referenceBound : reference.allocation < mapping.sourceLimit) :
    CIL.Safety.viewContains (mapping.view permission) (mapping.reference reference) =
      CIL.Safety.viewContains permission reference := by
  have identities : mapping.image permission.allocation = mapping.image reference.allocation ↔
      permission.allocation = reference.allocation :=
    ⟨mapping.injective _ _ viewBound referenceBound, congrArg mapping.image⟩
  simp only [CIL.Safety.viewContains, view, AllocationRenaming.reference, identities]
#print axioms viewContains
end AllocationRenaming
end CIL.Safety
