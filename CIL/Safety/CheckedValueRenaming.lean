import CIL.Safety.LocalLoadRenaming
import CIL.Safety.Execution

/-!
# Value checks under allocation renaming

Stack observers preserve scalar bits and nullness. Checked value formation transports the
same reference validation to the corresponding allocation in the target memory.
-/

namespace CIL.Safety

/-- Reference renaming preserves whether a value exposes unspecified scalar bits. -/
theorem AllocationRenaming.hasUnspecified (mapping : AllocationRenaming) (value : Value) :
    (mapping.value value).hasUnspecified = value.hasUnspecified := by cases value <;> rfl
#print axioms AllocationRenaming.hasUnspecified

/-- Null tests are unchanged by allocation renaming, including expired non-null addresses. -/
theorem AllocationRenaming.isNull (mapping : AllocationRenaming) (reference : ManagedReference) :
    (mapping.managedReference reference == .null) = (reference == .null) := by
  cases reference <;> rfl
#print axioms AllocationRenaming.isNull

/-- Scalar bit casts preserve their exact result and do not report memory-dependent faults. -/
theorem AllocationRenaming.bitcastValue (mapping : AllocationRenaming)
    (source target : CIL.SnapshotShape) (value : CIL.Value) :
    ResultRenamed mapping Eq
      (bitcastValue source target value) (bitcastValue source target value) := by
  unfold CIL.Safety.bitcastValue
  repeat first | exact .ok rfl | exact .error _ | split
#print axioms AllocationRenaming.bitcastValue

/-- The unspecified-operand guard sees the same scalar operands after reference renaming. -/
theorem AllocationRenaming.unspecifiedOperands (mapping : AllocationRenaming)
    (count : Nat) (values : List Value) :
    unspecifiedOperands count (values.map mapping.value) = unspecifiedOperands count values := by
  simp only [CIL.Safety.unspecifiedOperands, ← List.map_take, List.any_map,
    Function.comp_def, mapping.hasUnspecified]
#print axioms AllocationRenaming.unspecifiedOperands

/-- Scalar-only decoding rejects the same non-scalar shapes after allocation renaming. -/
theorem AllocationRenaming.scalars (mapping : AllocationRenaming) (values : List Value) :
    scalars (values.map mapping.value) = scalars values := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
    cases value <;> simp only [List.map_cons, AllocationRenaming.value, CIL.Safety.scalars,
      induction]
#print axioms AllocationRenaming.scalars

/-- Managed reference extraction maps the successful address and preserves null faults. -/
theorem AllocationRenaming.referenceAt (mapping : AllocationRenaming)
    (reference : ManagedReference) :
    ResultRenamed mapping (fun left right => right = mapping.reference left)
      (referenceAt reference) (referenceAt (mapping.managedReference reference)) := by
  cases reference with
  | null => exact .error (.memory .nullDereference .null 0)
  | address address => exact .ok rfl
#print axioms AllocationRenaming.referenceAt

/-- Value formation checks the corresponding backing allocation for every value shape. -/
theorem Memory.Renamed.checkedValue {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (value : Value)
    (bound : value.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun left right => right = mapping.value left)
      (checkedValue source value) (checkedValue target (mapping.value value)) := by
  cases value with
  | scalar value =>
    dsimp only [AllocationRenaming.value, CIL.Safety.checkedValue]
    split <;> first | exact .ok rfl | exact .error .invalidState
  | reference reference => exact related.formValue reference bound
  | readOnlyReference reference =>
    dsimp only [CIL.Safety.checkedValue, AllocationRenaming.value]
    apply (related.formValue reference bound).bind
    intro left right same
    exact .ok rfl
  | span reference length =>
    dsimp only [CIL.Safety.checkedValue, AllocationRenaming.value]
    apply (related.formValue reference bound).bind
    intro left right same
    exact .ok rfl
  | bufferSpan view =>
    dsimp only [CIL.Safety.checkedValue, AllocationRenaming.value]
    have validation : ResultEquivalent Eq (view.validate source)
        ((mapping.spanView view).validate target) := by
      rw [related.spanValidate view bound]
      cases view.validate source <;> first | exact .error _ | exact .ok rfl
    apply (validation.checkedAt view.reference 0).bind
    intro left right same
    exact .ok rfl
  | array view =>
    dsimp only [CIL.Safety.checkedValue, AllocationRenaming.value]
    have validation : ResultEquivalent Eq (view.validate source)
        ((mapping.arrayView view).validate target) := by
      rw [related.arrayValidate view bound]
      cases view.validate source <;> first | exact .error _ | exact .ok rfl
    apply (validation.checkedAt view.reference 0).bind
    intro left right same
    exact .ok rfl
#print axioms Memory.Renamed.checkedValue

/-- Checking a complete stack preserves its mapped values and the first reported fault. -/
theorem Memory.Renamed.checkedValues {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (values : List Value)
    (bounds : ∀ value ∈ values, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun left right => right = left.map mapping.value)
      (values.mapM (CIL.Safety.checkedValue source))
      ((values.map mapping.value).mapM (CIL.Safety.checkedValue target)) := by
  induction values with
  | nil => exact .ok rfl
  | cons value rest induction =>
    simp only [List.map_cons, List.mapM_cons]
    apply (related.checkedValue value (bounds value (List.mem_cons_self ..))).bind
    intro first otherFirst firstRelated
    apply (induction (fun value member => bounds value (List.mem_cons_of_mem _ member))).bind
    intro remaining otherRemaining remainingRelated
    exact .ok (by simp only [List.map_cons, firstRelated, remainingRelated])
#print axioms Memory.Renamed.checkedValues

end CIL.Safety
