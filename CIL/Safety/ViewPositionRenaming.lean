import CIL.Safety.ViewRenaming
import CIL.Safety.ResultRenaming

/-!
# Span and array positions under allocation renaming

Slicing and indexing preserve bounds checks and offsets while mapping backing allocations.
-/

namespace CIL.Safety

/-- Span indexing preserves the exact fault or returns the corresponding element address. -/
theorem Memory.Renamed.spanElement {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : SpanView)
    (bound : view.reference.Below mapping.sourceLimit) (index : Nat) :
    ResultEquivalent (fun left right => right = mapping.reference left)
      (view.element source index) ((mapping.spanView view).element target index) := by
  unfold SpanView.element
  rw [related.spanValidate view bound]
  apply ResultEquivalent.bind_same
  intro checked
  dsimp +instances only [AllocationRenaming.spanView]
  by_cases inside : index < view.length
  · simp only [inside, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases reference : view.reference with
    | null => simp only [AllocationRenaming.managedReference]; exact .error _
    | address address =>
      have addressBound : address.allocation < mapping.sourceLimit := by
        simpa only [reference, ManagedReference.Below] using bound
      simp only [AllocationRenaming.managedReference, AllocationRenaming.reference]
      have formed := related.form { address with offset := address.offset + index * view.width }
        addressBound
      simp only [AllocationRenaming.reference] at formed
      rw [formed]
      cases CIL.Safety.form source { address with offset := address.offset + index * view.width }
      · exact .error _
      · exact .ok rfl
  · simp only [inside, Bool.false_eq_true, ite_false, Bind.bind, Except.bind]
    exact .error _
#print axioms Memory.Renamed.spanElement

/-- Slices preserve length, mutability and bounds checks on the mapped backing allocation. -/
theorem Memory.Renamed.spanSlice {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : SpanView)
    (bound : view.reference.Below mapping.sourceLimit) (start length : Nat) :
    ResultEquivalent (fun left right => right = mapping.spanView left)
      (view.slice source start length) ((mapping.spanView view).slice target start length) := by
  unfold SpanView.slice
  rw [related.spanValidate view bound]
  apply ResultEquivalent.bind_same
  intro checked
  dsimp +instances only [AllocationRenaming.spanView]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  by_cases inside : start ≤ view.length ∧ length ≤ view.length - start
  · simp only [inside, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases reference : view.reference with
    | null =>
      simp only [AllocationRenaming.managedReference]
      change ResultEquivalent _
        (({ view with reference := .null, length := length }.validate source).bind _)
        (({ view with reference := .null, length := length }.validate source).bind _)
      apply ResultEquivalent.bind_same
      intro checked
      exact .ok rfl
    | address address =>
      have addressBound : address.allocation < mapping.sourceLimit := by
        simpa only [reference, ManagedReference.Below] using bound
      have validated := related.spanValidate
        { view with reference := .address { address with
            offset := address.offset + start * view.width }, length := length } addressBound
      simp only [AllocationRenaming.managedReference, AllocationRenaming.reference]
      simp only [AllocationRenaming.spanView, AllocationRenaming.managedReference,
        AllocationRenaming.reference] at validated
      rw [validated]
      cases checked : ({ view with reference := .address { address with
          offset := address.offset + start * view.width }, length := length }.validate source)
      · exact .error _
      · exact .ok rfl
  · simp only [inside, Bool.false_eq_true, ite_false, Bind.bind, Except.bind]
    exact .error _
#print axioms Memory.Renamed.spanSlice

/-- Array indexing preserves null rejection and the corresponding element address. -/
theorem Memory.Renamed.arrayViewElement {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : ArrayView)
    (bound : view.reference.Below mapping.sourceLimit) (index : Nat) :
    ResultEquivalent (fun left right => right = mapping.reference left)
      (view.element source index) ((mapping.arrayView view).element target index) := by
  unfold ArrayView.element
  rw [related.arrayValidate view bound]
  apply ResultEquivalent.bind_same
  intro checked
  have elements := related.spanElement view.storage bound index
  cases reference : view.reference with
  | null =>
    simp only [AllocationRenaming.arrayView, AllocationRenaming.managedReference,
      reference, BEq.beq, decide_true, ite_true]
    exact .error _
  | address address =>
    simpa only [AllocationRenaming.arrayView, AllocationRenaming.spanView,
      ArrayView.storage, AllocationRenaming.managedReference, reference, BEq.beq,
      reduceCtorEq, decide_false, Bool.false_eq_true, ite_false] using elements
#print axioms Memory.Renamed.arrayViewElement

/-- Checked array positions preserve the named null/bounds exceptions and mapped address. -/
theorem Memory.Renamed.arrayElement {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : ArrayView)
    (bound : view.reference.Below mapping.sourceLimit) (index width : Nat) :
    ResultRenamed mapping (fun left right => right = mapping.reference left)
      (arrayElement source view index width)
      (arrayElement target (mapping.arrayView view) index width) := by
  unfold CIL.Safety.arrayElement
  dsimp +instances only [AllocationRenaming.arrayView]
  by_cases correct : width != view.elementType.width
  · simp only [correct, ite_true, Bind.bind, Except.bind]
    exact .error .invalidState
  · simp only [correct, Bool.false_eq_true, ite_false, Bind.bind, Except.bind]
    have validation : ResultEquivalent Eq (view.validate source)
        ((mapping.arrayView view).validate target) := by
      rw [related.arrayValidate view bound]
      cases view.validate source <;> first | exact .error _ | exact .ok rfl
    apply (validation.checkedAt view.reference 0).bind
    intro left right same
    have positions := (related.arrayViewElement view bound index).checkedAt (mapping := mapping)
      view.reference width
    cases reference : view.reference with
    | null =>
      simp only [AllocationRenaming.managedReference, reference, BEq.beq,
        decide_true, ite_true]
      exact .error (.thrown "System.NullReferenceException")
    | address address =>
      simp only [AllocationRenaming.managedReference, reference, BEq.beq,
        reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
      by_cases inside : index < view.length
      · simpa only [inside, ite_true, Bind.bind, Except.bind, reference,
          AllocationRenaming.arrayView, AllocationRenaming.managedReference] using positions
      · simp only [inside, ite_false, Bind.bind, Except.bind]
        exact .error (.thrown "System.IndexOutOfRangeException")
#print axioms Memory.Renamed.arrayElement

end CIL.Safety
