import CIL.Safety.ValueMemoryRenaming
import CIL.Safety.ReferenceObservations

/-!
# Reference observations under allocation renaming

Nullness, allocation equality and offsets retain their meaning. Comparisons across
allocation boundaries keep the existing unsupported cases and gain no access authority.
-/

namespace CIL.Safety

/-- Live allocation lookup preserves layout, lifetime, sentinels and related storage kind. -/
theorem Memory.Renamed.liveAllocation {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (identity : AllocationId)
    (bound : identity < mapping.sourceLimit) :
    ResultEquivalent (Allocation.Related scopes) (liveAllocation source identity)
      (liveAllocation target (mapping.image identity)) := by
  have allocations := related.allocations identity bound
  unfold CIL.Safety.liveAllocation
  generalize sourceFound : source.allocations identity = sourceAllocation at allocations ⊢
  generalize targetFound : target.allocations (mapping.image identity) = targetAllocation
    at allocations ⊢
  cases allocations with
  | none => exact .error Fault.missingAllocation
  | @some sourceDescriptor targetDescriptor descriptors =>
    dsimp only
    rw [← descriptors.live]
    cases sourceDescriptor.live with
    | false => exact .error Fault.expiredLifetime
    | true => exact .ok descriptors
#print axioms Memory.Renamed.liveAllocation

/-- Null tests preserve their Boolean result and reference formation checks. -/
theorem Memory.Renamed.referenceNonNull {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) :
    ResultRenamed mapping Eq (referenceNonNull source reference)
      (referenceNonNull target (mapping.managedReference reference)) := by
  unfold CIL.Safety.referenceNonNull
  apply (related.formValue reference bound).bind
  intro left right values
  cases reference <;> exact .ok rfl
#print axioms Memory.Renamed.referenceNonNull

/-- Pointer subtraction and ordering inspect corresponding offsets in the same allocation. -/
theorem Memory.Renamed.referencePositions {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (left right : ManagedReference)
    (leftBound : left.Below mapping.sourceLimit) (rightBound : right.Below mapping.sourceLimit) :
    ResultRenamed mapping Eq (referencePositions source left right)
      (referencePositions target
        (mapping.managedReference left) (mapping.managedReference right)) := by
  cases left with
  | null => exact .error (.memory .nullDereference .null 0)
  | address left =>
    cases right with
    | null => exact .error (.memory .nullDereference .null 0)
    | address right =>
      have identities : mapping.image left.allocation = mapping.image right.allocation ↔
          left.allocation = right.allocation :=
        ⟨mapping.injective _ _ leftBound rightBound, congrArg mapping.image⟩
      dsimp only [CIL.Safety.referencePositions, AllocationRenaming.managedReference,
        referenceAt, Bind.bind, Except.bind]
      rw [related.form left leftBound, related.form right rightBound]
      cases CIL.Safety.form source left with
      | error fault => exact .error (.memory fault (.address left) 0)
      | ok first =>
        cases CIL.Safety.form source right with
        | error fault => exact .error (.memory fault (.address right) 0)
        | ok second =>
          simp only [checkedAt, Except.map, Except.mapError, Bind.bind, Except.bind,
            AllocationRenaming.reference, bne_iff_ne, ne_eq, identities]
          split <;> first | exact .error _ | exact .ok rfl
#print axioms Memory.Renamed.referencePositions

/-- Native-width pointer differences preserve the same modular signed displacement. -/
theorem Memory.Renamed.referenceDifference {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (left right : ManagedReference)
    (leftBound : left.Below mapping.sourceLimit) (rightBound : right.Below mapping.sourceLimit) :
    ResultRenamed mapping Eq (referenceDifference source left right)
      (referenceDifference target
        (mapping.managedReference left) (mapping.managedReference right)) :=
  (related.referencePositions left right leftBound rightBound).bind _ _
    (fun _ _ equal => by cases equal; exact .ok rfl)
#print axioms Memory.Renamed.referenceDifference

/-- Pointer order within one allocation is independent of its renamed identity. -/
theorem Memory.Renamed.referenceLess {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (left right : ManagedReference)
    (leftBound : left.Below mapping.sourceLimit) (rightBound : right.Below mapping.sourceLimit) :
    ResultRenamed mapping Eq (referenceLess source left right)
      (referenceLess target (mapping.managedReference left) (mapping.managedReference right)) :=
  (related.referencePositions left right leftBound rightBound).bind _ _
    (fun _ _ equal => by cases equal; exact .ok rfl)
#print axioms Memory.Renamed.referenceLess

/-- Reference equality retains the same cross-allocation end-pointer rejection. -/
theorem Memory.Renamed.referenceEqual {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (left right : ManagedReference)
    (leftBound : left.Below mapping.sourceLimit) (rightBound : right.Below mapping.sourceLimit) :
    ResultRenamed mapping Eq (referenceEqual source left right)
      (referenceEqual target (mapping.managedReference left) (mapping.managedReference right)) := by
  unfold CIL.Safety.referenceEqual
  apply (related.formValue left leftBound).bind
  intro first otherFirst firstRelated
  apply (related.formValue right rightBound).bind
  intro second otherSecond secondRelated
  cases left with
  | null => cases right <;> exact .ok rfl
  | address left =>
    cases right with
    | null => exact .ok rfl
    | address right =>
      have identities : mapping.image left.allocation = mapping.image right.allocation ↔
          left.allocation = right.allocation :=
        ⟨mapping.injective _ _ leftBound rightBound, congrArg mapping.image⟩
      simp only [AllocationRenaming.managedReference, AllocationRenaming.reference,
        beq_iff_eq, identities]
      split
      · exact .ok rfl
      · apply ((related.liveAllocation left.allocation leftBound).checkedAt (.address left) 0).bind
        intro first otherFirst firstAllocation
        apply ((related.liveAllocation right.allocation rightBound).checkedAt
          (.address right) 0).bind
        intro second otherSecond secondAllocation
        rw [← firstAllocation.layout, ← secondAllocation.layout]
        split <;> first | exact .error _ | exact .ok rfl
#print axioms Memory.Renamed.referenceEqual

/-- Native-width pointer arithmetic retains provenance and checks the same resulting offset. -/
theorem Memory.Renamed.add {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (bound : reference.allocation < mapping.sourceLimit) (size : Nat) (offset : BitVec 64) :
    add target (mapping.reference reference) size offset =
      (add source reference size offset).map mapping.reference := by
  unfold CIL.Safety.add
  rw [related.form reference bound]
  cases CIL.Safety.form source reference with
  | error fault => rfl
  | ok formed =>
    simp only [Except.map, Bind.bind, Except.bind]
    exact related.form { reference with offset :=
      (BitVec.ofNat 64 reference.offset + BitVec.ofNat 64 size * offset).toNat } bound
#print axioms Memory.Renamed.add

/-- Displacing a reference preserves the mapped reference and the original validity check. -/
theorem Memory.Renamed.displaceReference {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (size : Nat) (displacement : Int) :
    ResultRenamed mapping (fun source target => target = mapping.managedReference source)
      (displaceReference source reference size displacement)
      (displaceReference target (mapping.managedReference reference) size displacement) := by
  unfold CIL.Safety.displaceReference
  cases reference with
  | null => exact .error (.memory .nullDereference .null 0)
  | address reference =>
    dsimp only [AllocationRenaming.managedReference, referenceAt, Bind.bind, Except.bind]
    rw [related.add reference bound]
    cases CIL.Safety.add source reference size (BitVec.ofInt 64 displacement) with
    | error fault => exact .error (.memory fault (.address reference) 0)
    | ok result => exact .ok rfl
#print axioms Memory.Renamed.displaceReference

/-- Subtracting an integer offset preserves the mapped reference and the original validity check. -/
theorem Memory.Renamed.referenceSubtract {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (offset : CIL.Value) :
    ResultRenamed mapping (fun source target => target = mapping.managedReference source)
      (referenceSubtract source reference offset)
      (referenceSubtract target (mapping.managedReference reference) offset) := by
  unfold CIL.Safety.referenceSubtract
  cases CIL.offsetValue true offset with
  | none => exact .error .invalidState
  | some displacement => exact related.displaceReference reference bound 1 (-displacement)
#print axioms Memory.Renamed.referenceSubtract

end CIL.Safety
