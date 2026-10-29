import CIL.Safety.LocalLoadRenaming
import CIL.Safety.SnapshotRenaming

/-!
# Local stores under allocation renaming

Retained slots keep their exact kind and initialization behavior. Scalar and snapshot
stores update corresponding bytes; root assignments preserve mapped reference checks.
-/

namespace CIL.Safety

/-- Scalar encoding has no allocation-sensitive result or fault. -/
theorem AllocationRenaming.localNumber (mapping : AllocationRenaming)
    (kind : CIL.LocalKind) (value : CIL.Value) :
    ResultRenamed mapping Eq (localNumber kind value) (localNumber kind value) := by
  unfold CIL.Safety.localNumber
  split
  · exact .error (.unsupported "Unspecified vector bytes")
  · cases kind <;> cases value
    all_goals repeat' first
      | exact .error _
      | exact .ok rfl
      | split
#print axioms AllocationRenaming.localNumber

/-- A slot store preserves corresponding metadata, contents and memory authority. -/
theorem Memory.Renamed.storeLocal {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (slot : LocalSlot) (value : Value)
    (slotBound : slot.Below mapping.sourceLimit) (valueBound : value.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun source target =>
      target.1 = mapping.localSlot source.1 ∧
      Memory.Renamed mapping scopes source.2 target.2)
      (storeLocal source slot value)
      (storeLocal target (mapping.localSlot slot) (mapping.value value)) := by
  cases slot with
  | methodPointer signature stored | methodTable signature stored =>
    cases value
    case scalar scalar => cases scalar <;> exact .error _
    case reference reference => cases reference <;> first
      | exact .error _
      | exact .ok ⟨rfl, related⟩
    all_goals simp only [CIL.Safety.storeLocal, AllocationRenaming.localSlot,
      AllocationRenaming.value, Value.hasUnspecified, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte]
    all_goals repeat' first
      | contradiction
      | exact .error _
      | exact .ok ⟨rfl, related⟩
      | split
  | opaque128 stored =>
    cases value with
    | scalar scalar =>
      cases scalar <;> first | exact .error _ | exact .ok ⟨rfl, related⟩
    | reference _ | span _ _ | bufferSpan _ | readOnlyReference _ | array _
    | methodPointer _ | methodTable _ => exact .error _
  | root stored | readOnlyRoot stored =>
    cases value with
    | reference reference | readOnlyReference reference =>
      dsimp only [CIL.Safety.storeLocal, AllocationRenaming.localSlot,
        AllocationRenaming.value, Value.hasUnspecified, Bool.and]
      apply (related.formValue reference valueBound).bind
      intro left right values
      exact .ok ⟨rfl, related⟩
    | scalar scalar => cases scalar <;> exact .error _
    | span _ _ | bufferSpan _ | array _ | methodPointer _ | methodTable _ => exact .error _
  | bytes kind reference =>
    cases value with
    | scalar scalar =>
      cases scalar <;> simp only [CIL.Safety.storeLocal, AllocationRenaming.localSlot,
        AllocationRenaming.value, Value.hasUnspecified, CIL.Value.hasUnspecified,
        Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
      all_goals first
        | exact .error _
        | (split
           · exact .error _
           · apply ((related.writeSnapshot reference slotBound _ _).checkedAt
               (.address reference) (localWidth kind)).bind
             intro left right stored
             exact .ok ⟨rfl, stored⟩)
        | (apply (mapping.localNumber kind _).bind
           intro left right equal
           cases equal
           apply ((related.write reference slotBound _ _).checkedAt
             (.address reference) (localWidth kind)).bind
           intro left right stored
           exact .ok ⟨rfl, stored⟩)
    | reference _ | span _ _ | bufferSpan _ | readOnlyReference _ | array _
    | methodPointer _ | methodTable _ => exact .error _
  | span width writable stored =>
    cases value with
    | scalar scalar => cases scalar <;> exact .error _
    | reference _ | readOnlyReference _ | array _
    | methodPointer _ | methodTable _ => exact .error _
    | span reference length =>
      cases writable with
      | true => exact .error .invalidState
      | false =>
        dsimp only [CIL.Safety.storeLocal, AllocationRenaming.localSlot,
          AllocationRenaming.value, Value.hasUnspecified, Bool.and]
        have checked := related.spanValidate ⟨reference, length, width, false⟩ valueBound
        dsimp only [AllocationRenaming.spanView] at checked
        rw [checked]
        cases SpanView.validate ⟨reference, length, width, false⟩ source with
        | error fault => exact .error (.memory fault reference 0)
        | ok _ => exact .ok ⟨rfl, related⟩
    | bufferSpan view =>
      dsimp only [CIL.Safety.storeLocal, AllocationRenaming.localSlot,
        AllocationRenaming.value, AllocationRenaming.spanView, Value.hasUnspecified, Bool.and]
      have checked := related.spanValidate view valueBound
      dsimp only [AllocationRenaming.spanView] at checked
      rw [checked]
      simp only [Bool.false_eq_true, ite_false]
      by_cases mismatch : (view.width != width || view.writable != writable) = true
      all_goals simp only [mismatch, ite_true, ite_false]
      · exact .error .invalidState
      · cases view.validate source with
        | error fault => exact .error (.memory fault view.reference 0)
        | ok _ => exact .ok ⟨rfl, related⟩
  | array element stored =>
    cases value with
    | scalar scalar => cases scalar <;> exact .error _
    | reference reference =>
      cases reference with
      | address _ => exact .error .invalidState
      | null =>
        simp only [CIL.Safety.storeLocal, AllocationRenaming.localSlot, AllocationRenaming.value,
          Value.hasUnspecified, Bool.and, Bool.false_eq_true, ite_false,
          AllocationRenaming.managedReference, ArrayView.validate, ArrayView.storage, SpanView.validate]
        by_cases width : 0 < element.width ∧ element.width < 2^64
        all_goals simp [width, checkedAt, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
        · exact .ok ⟨rfl, related⟩
        · exact .error _
    | span _ _ | readOnlyReference _ | bufferSpan _
    | methodPointer _ | methodTable _ => exact .error _
    | array view =>
      dsimp only [CIL.Safety.storeLocal, AllocationRenaming.localSlot,
        AllocationRenaming.value, AllocationRenaming.arrayView, Value.hasUnspecified, Bool.and]
      have checked := related.arrayValidate view valueBound
      dsimp only [AllocationRenaming.arrayView] at checked
      rw [checked]
      simp only [Bool.false_eq_true, ite_false]
      by_cases mismatch : (view.elementType != element) = true
      all_goals simp only [mismatch, ite_true, ite_false]
      · exact .error .invalidState
      · cases view.validate source with
        | error fault => exact .error (.memory fault view.reference 0)
        | ok _ => exact .ok ⟨rfl, related⟩
#print axioms Memory.Renamed.storeLocal

/-- Storing a bounded value cannot introduce a reference beyond the allocated identity prefix. -/
theorem storeLocal_below {limit : Nat} {memory after : Memory} {slot final : LocalSlot}
    {value : Value} (slotBound : slot.Below limit) (valueBound : value.Below limit)
    (stored : storeLocal memory slot value = .ok (final, after)) : final.Below limit := by
  unfold CIL.Safety.storeLocal at stored
  repeat' first
    | solve | exact slotBound
    | solve | exact valueBound
    | solve | trivial
    | cases stored
    | split at stored
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at stored
  all_goals simpa [LocalSlot.Below, Value.Below, ManagedReference.Below] using valueBound
#print axioms storeLocal_below

end CIL.Safety
