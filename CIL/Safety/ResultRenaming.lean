import CIL.Safety.ValueRenaming
import CIL.Safety.MemoryEquivalence

/-!
# Execution results under allocation renaming

Success values are related explicitly. A memory fault retains its rule and width but
reports the mapped reference; named exceptions and all other fault kinds stay exact.
-/

namespace CIL.Safety

/-- Rename only the allocation identity reported by a memory fault. -/
def AllocationRenaming.fault (mapping : AllocationRenaming) : ExecutionFault → ExecutionFault
  | .memory rule reference width => .memory rule (mapping.managedReference reference) width
  | fault => fault

/-- A checked computation agrees with an explicitly mapped copy of its success value. -/
theorem ResultEquivalent.of_map (result : Except ε α) (transform : α → β) :
    ResultEquivalent (fun left right => right = transform left) result (result.map transform) := by
  cases result <;> first | exact .error _ | exact .ok rfl
#print axioms ResultEquivalent.of_map

/-- A checked computation is related to itself by equality, including its exact fault. -/
theorem ResultEquivalent.eq_refl (result : Except ε α) : ResultEquivalent Eq result result := by
  cases result <;> first | exact .error _ | exact .ok rfl
#print axioms ResultEquivalent.eq_refl

/-- Related execution results preserve all non-memory faults exactly. -/
inductive ResultRenamed (mapping : AllocationRenaming) (relation : α → β → Prop) :
    ExecutionResult α → ExecutionResult β → Prop
  | error (fault : ExecutionFault) :
      ResultRenamed mapping relation (.error fault) (.error (mapping.fault fault))
  | ok {source : α} {target : β} (related : relation source target) :
      ResultRenamed mapping relation (.ok source) (.ok target)

/-- Sequential checked computations compose when their successful intermediate values relate. -/
theorem ResultRenamed.bind {mapping : AllocationRenaming} {relation : α → β → Prop}
    {following : γ → δ → Prop} {source : ExecutionResult α} {target : ExecutionResult β}
    (related : ResultRenamed mapping relation source target)
    (sourceNext : α → ExecutionResult γ) (targetNext : β → ExecutionResult δ)
    (next : ∀ left right, relation left right →
      ResultRenamed mapping following (sourceNext left) (targetNext right)) :
    ResultRenamed mapping following (source >>= sourceNext) (target >>= targetNext) := by
  cases related with
  | error fault => exact .error fault
  | ok relation => exact next _ _ relation
#print axioms ResultRenamed.bind

/-- Sequential transport may use the source computation's successful equation. -/
theorem ResultRenamed.bindWithSuccess {mapping : AllocationRenaming}
    {relation : α → β → Prop} {following : γ → δ → Prop}
    {source : ExecutionResult α} {target : ExecutionResult β}
    (related : ResultRenamed mapping relation source target)
    (sourceNext : α → ExecutionResult γ) (targetNext : β → ExecutionResult δ)
    (next : ∀ left right, source = .ok left → relation left right →
      ResultRenamed mapping following (sourceNext left) (targetNext right)) :
    ResultRenamed mapping following (source >>= sourceNext) (target >>= targetNext) := by
  cases related with
  | error fault => exact .error fault
  | ok relation => exact next _ _ rfl relation
#print axioms ResultRenamed.bindWithSuccess

/-- Pure result projections preserve the mapped fault and the stated success relation. -/
theorem ResultRenamed.map {mapping : AllocationRenaming} {relation : α → β → Prop}
    {following : γ → δ → Prop} {source : ExecutionResult α} {target : ExecutionResult β}
    (related : ResultRenamed mapping relation source target) (left : α → γ) (right : β → δ)
    (preserved : ∀ source target, relation source target → following (left source) (right target)) :
    ResultRenamed mapping following (source.map left) (target.map right) := by
  cases related with
  | error fault => exact .error fault
  | ok relation => exact .ok (preserved _ _ relation)
#print axioms ResultRenamed.map

/-- Equal checked-memory faults become execution faults with corresponding references. -/
theorem ResultEquivalent.checkedAt {mapping : AllocationRenaming} {relation : α → β → Prop}
    {source : Checked α} {target : Checked β}
    (related : ResultEquivalent relation source target) (reference : ManagedReference)
    (width : Nat) :
    ResultRenamed mapping relation (checkedAt reference width source)
      (checkedAt (mapping.managedReference reference) width target) := by
  cases related with
  | error fault => exact .error (.memory fault reference width)
  | ok related => exact .ok related
#print axioms ResultEquivalent.checkedAt

/-- A raised CLR exception is unchanged by reference renaming. -/
theorem ResultRenamed.thrown {mapping : AllocationRenaming} {relation : α → β → Prop}
    {target : ExecutionResult β} {exception : String}
    (related : ResultRenamed mapping relation (.error (.thrown exception)) target) :
    target = .error (.thrown exception) := by cases related; rfl
#print axioms ResultRenamed.thrown

/-- A successful source run gives a successful target run satisfying the result relation. -/
theorem ResultRenamed.success {mapping : AllocationRenaming} {relation : α → β → Prop}
    {source : α} {target : ExecutionResult β}
    (related : ResultRenamed mapping relation (.ok source) target) :
    ∃ result, target = .ok result ∧ relation source result := by
  cases related with
  | ok related => exact ⟨_, rfl, related⟩
#print axioms ResultRenamed.success

/-- A paired memory computation succeeds on the target whenever it succeeds on the source. -/
theorem ResultEquivalent.success {relation : α → β → Prop} {source : α}
    {target : Except ε β} (related : ResultEquivalent relation (.ok source) target) :
    ∃ result, target = .ok result ∧ relation source result := by
  cases related with
  | ok related => exact ⟨_, rfl, related⟩
#print axioms ResultEquivalent.success

end CIL.Safety
