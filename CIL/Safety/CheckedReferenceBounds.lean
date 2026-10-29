import CIL.Safety.CheckedMemoryRenaming
import CIL.Safety.InstructionMemoryLemmas

/-!
# Bounds of checked references

Successful reference validation in well-formed memory places every address in the allocated
identity prefix. These bounds keep mappings stable when subsequent calls allocate more storage.
-/

namespace CIL.Safety

/-- Successful formation names an existing allocation, below the next fresh identity. -/
theorem Memory.WellFormed.form_below {memory : Memory} (formed : memory.WellFormed)
    {reference result : Reference} (success : form memory reference = .ok result) :
    reference.allocation < memory.nextIdentity := by
  unfold form at success
  cases found : liveAllocation memory reference.allocation with
  | error fault => simp only [found, Bind.bind, Except.bind] at success; cases success
  | ok allocation =>
    exact (formed.1 _ _ (liveAllocation_ok _ _ _ found).1).1
#print axioms Memory.WellFormed.form_below

/-- Extracting a non-null address preserves its prefix bound. -/
theorem referenceAt_below {limit : Nat} {reference : ManagedReference} {address : Reference}
    (bound : reference.Below limit) (success : referenceAt reference = .ok address) :
    address.allocation < limit := by
  cases reference with
  | null => cases success
  | address source => cases success; exact bound
#print axioms referenceAt_below

/-- Valid spans carry null or an address in the allocated prefix. -/
theorem Memory.WellFormed.span_below {memory : Memory} (formed : memory.WellFormed)
    (view : SpanView) (valid : view.validate memory = .ok ()) :
    view.reference.Below memory.nextIdentity := by
  cases reference : view.reference with
  | null => trivial
  | address address =>
    change address.allocation < memory.nextIdentity
    unfold SpanView.validate at valid
    simp only [reference] at valid
    repeat' first
      | contradiction
      | solve |
          have found : liveAllocation memory address.allocation = .ok _ := by assumption
          exact (formed.1 _ _ (liveAllocation_ok _ _ _ found).1).1
      | cases valid
      | split at valid
      | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at valid
    all_goals try simp_all only [ManagedReference.address.injEq]
    all_goals subst_vars
    all_goals exact (formed.1 _ _ (liveAllocation_ok _ _ _ (by assumption)).1).1
#print axioms Memory.WellFormed.span_below

/-- Every valid checked value has bounded allocation identities in well-formed memory. -/
theorem Value.Valid.below {memory : Memory} (formed : memory.WellFormed)
    {value : Value} (valid : value.Valid memory) : value.Below memory.nextIdentity := by
  cases value with
  | scalar value | methodPointer _ | methodTable _ => trivial
  | bufferSpan view => exact formed.span_below view valid
  | array view => exact formed.span_below view.storage valid
  | reference reference | readOnlyReference reference | span reference length =>
    cases reference with
    | null => trivial
    | address address => exact formed.form_below valid
#print axioms Value.Valid.below

/-- A valid evaluation stack supplies all bounds required by allocation renaming. -/
theorem ValuesValid.below {memory : Memory} (formed : memory.WellFormed)
    {values : List Value} (valid : ValuesValid memory values) :
    ∀ value ∈ values, value.Below memory.nextIdentity :=
  fun value member => (valid value member).below formed
#print axioms ValuesValid.below

end CIL.Safety
