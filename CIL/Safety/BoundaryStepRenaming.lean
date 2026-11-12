import CIL.Safety.FixedStepHelpers
import CIL.Safety.NativeMethodTableRenaming

/-! Argument loads, calls and returns preserve checked values and control flow. -/

namespace CIL.Safety

/-- Allocation renaming preserves exactly the null managed reference. -/
private theorem managedReference_null_iff (mapping : AllocationRenaming)
    (reference : ManagedReference) :
    mapping.managedReference reference = .null ↔ reference = .null := by
  cases reference <;> simp [AllocationRenaming.managedReference]
#print axioms managedReference_null_iff

/-- Observable execution through a native table requires a successful checked memory step. -/
private theorem checkedNative_bind {mapping : AllocationRenaming} {relation : β → γ → Prop}
    (source target : Checked α) (sourceNext : α → ExecutionResult β)
    (targetNext : α → ExecutionResult γ)
    (preserved : ∀ value, source = .ok value → target = .ok value)
    (observable : SuccessOrThrow (checkedAt .null nativeMethodWidth source >>= sourceNext))
    (next : ∀ value, source = .ok value → SuccessOrThrow (sourceNext value) →
      ResultRenamed mapping relation (sourceNext value) (targetNext value)) :
    ResultRenamed mapping relation (checkedAt .null nativeMethodWidth source >>= sourceNext)
      (checkedAt .null nativeMethodWidth target >>= targetNext) := by
  cases checked : source with
  | error fault =>
    simp [checked, checkedAt, Except.mapError, Bind.bind, Except.bind, SuccessOrThrow] at observable
  | ok value =>
    simp only [checked, checkedAt, Except.mapError, Bind.bind, Except.bind] at observable ⊢
    rw [preserved value checked]
    exact next value checked observable
#print axioms checkedNative_bind

/-- Managed metadata identities are stable while checked argument references are renamed. -/
theorem Memory.Renamed.managedStep {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed)
    (operation : CIL.ManagedOp) (pc : Nat) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (managedStep operation pc sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (managedStep operation pc sourceFrame stack source)
      (managedStep operation pc targetFrame (stack.map mapping.value) target) := by
  unfold CIL.Safety.managedStep at observable ⊢
  split
  all_goals try simp only [*, List.map_cons, AllocationRenaming.value] at observable ⊢
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals try simp only [List.length_map, ← List.map_take, ← List.map_reverse, ← List.map_drop]
  all_goals repeat' first
    | exact .error _
    | exact .ok (.next related frames)
    | exact .ok (.call related)
    | exact .ok (.tailCall related)
    | (simp only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at observable ⊢)
    | contradiction
    | (apply checkedNative_bind _ _ _ _
        (fun value proof => related.addNativeTable_success formed _ value _ proof) observable
       intro value found observable)
    | (apply checkedNative_bind _ _ _ _
        (fun value proof => related.loadNativeTable_success formed _ value proof) observable
       intro value found observable)
    | (apply (related.checkedValues _ (by
        intro value member
        exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))).bind
       intro first second same
       subst second)
    | (split <;> try simp only [*, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
        List.map_cons, AllocationRenaming.value, Bind.bind, Except.bind, Pure.pure,
        Except.pure] at observable ⊢)
  all_goals try simp_all only [reduceCtorEq, forall_const, forall_eq', false_implies, true_implies]
  all_goals cases stack with
  | nil => simp_all [AllocationRenaming.value, managedReference_null_iff]
  | cons head rest =>
    cases head <;> simp_all [AllocationRenaming.value, managedReference_null_iff]
    all_goals cases rest with
    | nil => simp_all [AllocationRenaming.value, managedReference_null_iff]
    | cons head rest =>
      cases head <;> simp_all [AllocationRenaming.value, managedReference_null_iff] <;>
        (exfalso; solve_by_elim)
#print axioms Memory.Renamed.managedStep

/-- A receiver-checked call transports as a call: renaming keeps a receiver null exactly when it
    was, so both runs throw at the `callvirt` or both enter the callee. -/
private theorem Memory.Renamed.stepCallInstance {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    {sourceFrame targetFrame : Frame} (related : Memory.Renamed mapping scopes source target)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method) (callee argc pc : Nat)
    (arguments stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.callInstance callee argc) pc arguments sourceFrame stack source)
      (step targetBody (.callInstance callee argc) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  simp only [step, mapping.unspecifiedOperands, Bool.or_false, List.length_map,
    ← List.map_take, ← List.map_drop, ← List.map_reverse]
  by_cases guard : unspecifiedOperands (observerCount (.callInstance callee argc)) stack = true
  · simp only [guard, ite_true]
    exact .error _
  · simp only [guard, Bool.false_eq_true, ite_false]
    by_cases short : stack.length < argc
    · simp only [short, ite_true]
      exact .error _
    · simp only [short, ite_false]
      have checks := related.checkedValues (stack.take argc).reverse (by
        intro value member
        exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))
      cases checked : (stack.take argc).reverse.mapM (CIL.Safety.checkedValue source) with
      | error fault =>
        rw [checked] at checks
        generalize ((stack.take argc).reverse.map mapping.value).mapM
          (CIL.Safety.checkedValue target) = targetChecked at checks ⊢
        cases checks
        exact .error fault
      | ok operands =>
        rw [checked] at checks
        obtain ⟨targetOperands, targetChecked, rfl⟩ := checks.success
        simp only [targetChecked, Bind.bind, Except.bind]
        have called : ∀ receiver tail, ResultRenamed mapping
            (FrameAction.Renamed indices mapping scopes)
            (.ok (.call callee (.object (.address receiver) :: tail) (stack.drop argc) source))
            (.ok (.call callee ((Value.object (.address receiver) :: tail).map mapping.value)
              ((stack.drop argc).map mapping.value) target)) := fun receiver tail =>
          .ok (FrameAction.Renamed.call related)
        match operands with
        | [] => exact .error _
        | .object (.address receiver) :: tail => exact called receiver tail
        | .object .null :: _ => exact .error _
        | .scalar _ :: _ | .methodPointer _ :: _ | .methodTable _ :: _ | .reference _ :: _
        | .readOnlyReference _ :: _ | .span .. :: _ | .bufferSpan _ :: _ | .array _ :: _ =>
          exact .error _
#print axioms Memory.Renamed.stepCallInstance

/-- Renaming keeps a live object's runtime type, and maps the fault of any other reference. -/
private theorem Memory.Renamed.runtimeTypeOf {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (receiver : Reference)
    (bound : receiver.allocation < mapping.sourceLimit) :
    ResultRenamed mapping Eq (CIL.Safety.runtimeTypeOf source receiver)
      (CIL.Safety.runtimeTypeOf target (mapping.reference receiver)) := by
  have allocations := related.allocations receiver.allocation bound
  simp only [CIL.Safety.runtimeTypeOf, AllocationRenaming.reference,
    CIL.Safety.liveAllocation, checkedAt, Except.mapError, Bind.bind, Except.bind]
  generalize source.allocations receiver.allocation = sourceAllocation at allocations ⊢
  generalize target.allocations (mapping.image receiver.allocation) = targetAllocation
    at allocations ⊢
  cases allocations with
  | none => exact .error (.memory .missingAllocation (.address receiver) 0)
  | @some sourceDescriptor targetDescriptor descriptors =>
    obtain ⟨kinds, -, live, -⟩ := descriptors
    dsimp only
    rw [← live]
    cases sourceDescriptor.live with
    | false => exact .error (.memory .expiredLifetime (.address receiver) 0)
    | true =>
      simp only [ite_true, Pure.pure, Except.pure]
      revert kinds
      generalize sourceDescriptor.kind = sourceKind
      generalize targetDescriptor.kind = targetKind
      intro kinds
      cases kinds with
      | frame => exact .error .invalidState
      | same =>
        cases sourceKind
        all_goals first
          | exact .error .invalidState
          | exact .ok rfl
#print axioms Memory.Renamed.runtimeTypeOf

/-- Renaming keeps a live object's runtime class, so a virtual call selects the same body and
    fails with the same, renamed, fault. -/
private theorem Memory.Renamed.virtualTarget {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (receiver : Reference)
    (bound : receiver.allocation < mapping.sourceLimit)
    (targets : List (CIL.Extraction.TypeExpr × Nat)) :
    ResultRenamed mapping (fun left right => right = left)
      (CIL.Safety.virtualTarget source targets receiver)
      (CIL.Safety.virtualTarget target targets (mapping.reference receiver)) := by
  unfold CIL.Safety.virtualTarget
  apply (related.runtimeTypeOf receiver bound).bind
  intro runtime other same
  subst same
  split
  · exact .ok rfl
  · exact .error outsideDispatchTable
#print axioms Memory.Renamed.virtualTarget

/-- Renaming keeps a type test's outcome: the same runtime lineage decides it, and a passing
    reference stays the renamed reference. -/
private theorem Memory.Renamed.objectTest {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (type : CIL.Extraction.TypeExpr)
    (throwing : Bool) :
    ResultRenamed mapping (fun left right => right = mapping.managedReference left)
      (CIL.Safety.objectTest source type throwing reference)
      (CIL.Safety.objectTest target type throwing (mapping.managedReference reference)) := by
  unfold CIL.Safety.objectTest
  apply (related.formObject reference bound).bind
  intro formed otherFormed _
  cases reference with
  | null => exact .ok rfl
  | address object =>
    simp only [AllocationRenaming.managedReference]
    apply (related.runtimeTypeOf object bound).bind
    intro runtime other same
    subst same
    split
    · exact .ok rfl
    · split
      · exact .error _
      · exact .ok rfl
#print axioms Memory.Renamed.objectTest

/-- A type test transports as a step to the next pc: renaming keeps null, the tested runtime
    class and the cast's exception. -/
private theorem Memory.Renamed.stepObjectTest {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    {sourceFrame targetFrame : Frame} (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (type : CIL.Extraction.TypeExpr) (throwing : Bool)
    (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.objectTest type throwing) pc arguments sourceFrame stack source)
      (step targetBody (.objectTest type throwing) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  simp only [step, mapping.unspecifiedOperands, Bool.or_false]
  by_cases guard : unspecifiedOperands (observerCount (.objectTest type throwing)) stack = true
  · simp only [guard, ite_true]
    exact .error _
  · simp only [guard, Bool.false_eq_true, ite_false]
    match stack, bounds with
    | .object reference :: rest, bounds =>
      have below : reference.Below mapping.sourceLimit := bounds _ List.mem_cons_self
      simp only [List.map_cons, AllocationRenaming.value]
      refine (related.objectTest reference below type throwing).bind _ _ ?_
      intro left right same
      subst same
      exact .ok (.next related frames)
    | [], _ => exact .error _
    | .scalar _ :: _, _ | .methodPointer _ :: _, _ | .methodTable _ :: _, _
    | .reference _ :: _, _ | .readOnlyReference _ :: _, _ | .span .. :: _, _
    | .bufferSpan _ :: _, _ | .array _ :: _, _ =>
      dsimp only [pureArity, CIL.Safety.instruction]
      simp only [mapping.unspecifiedOperands]
      split <;> exact .error _
#print axioms Memory.Renamed.stepObjectTest

/-- A virtual call transports as a call: renaming keeps a receiver null exactly when it was and
    keeps a live receiver's class, so both runs throw, fault alike or enter the same body. -/
private theorem Memory.Renamed.stepCallVirtual {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    {sourceFrame targetFrame : Frame} (related : Memory.Renamed mapping scopes source target)
    (sourceBody targetBody : CIL.Method) (targets : List (CIL.Extraction.TypeExpr × Nat))
    (argc pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.callVirtual targets argc) pc arguments sourceFrame stack source)
      (step targetBody (.callVirtual targets argc) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  simp only [step, mapping.unspecifiedOperands, Bool.or_false, List.length_map,
    ← List.map_take, ← List.map_drop, ← List.map_reverse]
  by_cases guard : unspecifiedOperands (observerCount (.callVirtual targets argc)) stack = true
  · simp only [guard, ite_true]
    exact .error _
  · simp only [guard, Bool.false_eq_true, ite_false]
    by_cases short : stack.length < argc
    · simp only [short, ite_true]
      exact .error _
    · simp only [short, ite_false]
      have checks := related.checkedValues (stack.take argc).reverse (by
        intro value member
        exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))
      cases checked : (stack.take argc).reverse.mapM (CIL.Safety.checkedValue source) with
      | error fault =>
        rw [checked] at checks
        generalize ((stack.take argc).reverse.map mapping.value).mapM
          (CIL.Safety.checkedValue target) = targetChecked at checks ⊢
        cases checks
        exact .error fault
      | ok operands =>
        rw [checked] at checks
        obtain ⟨targetOperands, targetChecked, rfl⟩ := checks.success
        have unchanged := (checkedValues_valid _ _ _ checked).1
        simp only [targetChecked, Bind.bind, Except.bind]
        match operands, unchanged with
        | [], _ => exact .error _
        | .object (.address receiver) :: tail, unchanged =>
          have below := bounds _ (List.mem_of_mem_take (List.mem_reverse.mp
            (unchanged ▸ List.mem_cons_self ..)))
          simp only [Value.Below, ManagedReference.Below] at below
          simp only [List.map_cons, AllocationRenaming.value, AllocationRenaming.managedReference]
          refine (related.virtualTarget receiver below targets).bind _ _ ?_
          intro left right same
          subst same
          exact .ok (FrameAction.Renamed.call related)
        | .object .null :: _, _ => exact .error _
        | .scalar _ :: _, _ | .methodPointer _ :: _, _ | .methodTable _ :: _, _
        | .reference _ :: _, _ | .readOnlyReference _ :: _, _ | .span .. :: _, _
        | .bufferSpan _ :: _, _ | .array _ :: _, _ =>
          exact .error _
#print axioms Memory.Renamed.stepCallVirtual

/-- Argument loads, calls and returns preserve their checked values and control flow. -/
theorem Memory.Renamed.stepBoundary {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (operation : CIL.Instruction)
    (family : fixedStepFamily operation = .boundary) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (argumentBounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  by_cases isManaged : ∃ native, operation = .managed native
  · rcases isManaged with ⟨native, rfl⟩
    unfold CIL.Safety.step at observable ⊢
    simp only [Bool.or_false] at observable ⊢
    rw [mapping.unspecifiedOperands]
    by_cases guarded : unspecifiedOperands (observerCount (.managed native)) stack = true
    · simp only [guarded, ite_true]
      exact .error (.unsupported "Instruction observes unspecified vector bits")
    · simp only [guarded, Bool.false_eq_true, ite_false] at observable ⊢
      exact related.managedStep frames formed native pc stack bounds observable
  by_cases receiverChecked : ∃ callee argc, operation = .callInstance callee argc
  · rcases receiverChecked with ⟨callee, argc, rfl⟩
    exact related.stepCallInstance formed sourceBody targetBody callee argc pc arguments stack
      bounds
  by_cases dispatched : ∃ targets argc, operation = .callVirtual targets argc
  · rcases dispatched with ⟨targets, argc, rfl⟩
    exact related.stepCallVirtual sourceBody targetBody targets argc pc arguments stack bounds
  by_cases tested : ∃ type throwing, operation = .objectTest type throwing
  · rcases tested with ⟨type, throwing, rfl⟩
    exact related.stepObjectTest frames sourceBody targetBody type throwing pc arguments stack
      bounds
  ·
    allocation_fixed_step (
      first
      | exact False.elim (isManaged ⟨_, rfl⟩)
      | exact False.elim (receiverChecked ⟨_, _, rfl⟩)
      | exact False.elim (dispatched ⟨_, _, rfl⟩)
      | exact False.elim (tested ⟨_, _, rfl⟩)
      | (rename_i position
         rw [List.getElem?_map]
         cases found : arguments[position]? with
         | none => exact .error .invalidState
         | some value =>
           apply (related.checkedValue value
             (argumentBounds value (List.mem_of_getElem? found))).bind
           intro first second same
           subst second
           exact .ok (.next related frames))
      | (rename_i position kind
         rw [List.getElem?_map]
         cases found : arguments[position]? with
         | none => exact .error .invalidState
         | some value =>
           cases value <;> try exact .error .invalidState
           rename_i scalar
           cases scalar <;> try exact .error .invalidState
           apply (related.checkedValue _ (by trivial)).bind
           intro first second same
           subst second
           exact .ok (.next related frames))
      | (apply (frames.argumentHome _).bind
         intro slot otherSlot slots
         rcases slots with ⟨bounded, rfl⟩
         first
         | (apply (related.loadLocal slot bounded).bind
            intro first second same
            subst second
            exact .ok (.next related frames))
         | (apply (related.localAddress slot bounded).bind
            intro first second same
            subst second
            exact .ok (.next related frames)))
      | (try simp only [List.map_nil, List.length_map, ← List.map_take, ← List.map_drop,
           ← List.map_reverse, metadata.returnsValue]
         repeat first
         | exact .error _
         | exact .ok (.returned related)
         | exact .ok (.call related)
         | exact .ok (.tailCall related)
         | (apply (related.checkedValues _ (by assumption)).bind
            intro first second same
            subst second)
         | (apply (related.checkedValues _ (by
              intro value member
              exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))).bind
            intro first second same
            subst second)
         | (apply (related.checkedValues _ (by
              intro value member
              exact bounds value (List.mem_reverse.mp member))).bind
            intro first second same
            subst second)
         | (apply (related.scalarChecks _).bind
            intro first second same
            subst second)
         | (split <;> try simp only [*, Bool.false_eq_true, ite_false])
         skip))
#print axioms Memory.Renamed.stepBoundary

end CIL.Safety
