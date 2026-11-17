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

/-- Managed metadata identities are stable while checked argument references are renamed. -/
theorem Memory.Renamed.managedStep {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (operation : CIL.ManagedOp) (link : Option CIL.Link) (pc : Nat) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (managedStep operation link pc sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (managedStep operation link pc sourceFrame stack source)
      (managedStep operation link pc targetFrame (stack.map mapping.value) target) := by
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
    | (apply (related.checkedValues _ (by
        intro value member
        exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))).bind
       intro first second same
       subst second)
    | (split <;> try simp only [*, Bool.false_eq_true, ite_false, ite_true, Bind.bind,
        Except.bind, Pure.pure, Except.pure] at observable ⊢)
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
    (linked : targetBody.linkAt pc = sourceBody.linkAt pc)
    (arguments stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.callInstance callee argc) pc arguments sourceFrame stack source)
      (step targetBody (.callInstance callee argc) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  simp only [step, mapping.unspecifiedOperands, List.length_map, linked,
    ← List.map_take, ← List.map_drop, ← List.map_reverse]
  by_cases guard : unspecifiedOperands (observerCount (.callInstance callee argc)) stack = true
  · simp only [guard, ite_true]
    exact .error _
  · simp only [guard, Bool.false_eq_true, ite_false]
    generalize sourceBody.linkAt pc = link
    rcases link with _ | link
    · exact .error _
    cases link <;> try exact .error _
    rename_i callee
    try dsimp only
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

/-- A `castclass` (`throwing`) or `isinst` transports as a step to the next pc: renaming keeps
    null, the tested runtime class and the cast's exception. -/
private theorem Memory.Renamed.stepTypeTest {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    {sourceFrame targetFrame : Frame} (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceBody targetBody : CIL.Method) (operation : CIL.Instruction)
    (type : CIL.Extraction.TypeExpr) (throwing : Bool)
    (tests : operation = .castclass type ∧ throwing = true ∨
      operation = .isinst type ∧ throwing = false)
    (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody operation pc arguments sourceFrame stack source)
      (step targetBody operation pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  rcases tests with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (
    simp only [step, observerCount, mapping.unspecifiedOperands]
    by_cases guard : unspecifiedOperands 1 stack = true
    · simp only [guard, ite_true]
      exact .error _
    · simp only [guard, Bool.false_eq_true, ite_false]
      match stack, bounds with
      | .object reference :: rest, bounds =>
        have below : reference.Below mapping.sourceLimit := bounds _ List.mem_cons_self
        simp only [List.map_cons, AllocationRenaming.value]
        refine (related.objectTest reference below type _).bind _ _ ?_
        intro left right same
        subst same
        exact .ok (.next related frames)
      | [], _ => exact .error _
      | .scalar _ :: _, _ | .methodPointer _ :: _, _ | .methodTable _ :: _, _
      | .reference _ :: _, _ | .readOnlyReference _ :: _, _ | .span .. :: _, _
      | .bufferSpan _ :: _, _ | .array _ :: _, _ =>
        dsimp only [pureArity, CIL.Safety.instruction]
        simp only [mapping.unspecifiedOperands]
        split <;> exact .error _)
#print axioms Memory.Renamed.stepTypeTest

/-- A virtual call transports as a call: renaming keeps a receiver null exactly when it was and
    keeps a live receiver's class, so both runs throw, fault alike or enter the same body. -/
private theorem Memory.Renamed.stepCallVirtual {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    {sourceFrame targetFrame : Frame} (related : Memory.Renamed mapping scopes source target)
    (sourceBody targetBody : CIL.Method) (targets : List (CIL.Extraction.TypeExpr × Nat))
    (argc pc : Nat) (linked : targetBody.linkAt pc = sourceBody.linkAt pc)
    (arguments stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.callVirtual targets argc) pc arguments sourceFrame stack source)
      (step targetBody (.callVirtual targets argc) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  simp only [step, mapping.unspecifiedOperands, List.length_map, linked,
    ← List.map_take, ← List.map_drop, ← List.map_reverse]
  by_cases guard : unspecifiedOperands (observerCount (.callVirtual targets argc)) stack = true
  · simp only [guard, ite_true]
    exact .error _
  · simp only [guard, Bool.false_eq_true, ite_false]
    -- The dispatch table is the link's; both bodies read the same one.
    generalize sourceBody.linkAt pc = link
    rcases link with _ | link
    · exact .error _
    cases link <;> try exact .error _
    rename_i targets
    try dsimp only
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

/-- Running `model` for a call without a link transports under every allocation renaming:
    related bodies, well-formed source memories, frames and stacks whose source run succeeds or
    throws step to related results. -/
def _root_.CIL.RuntimeModel.StepRenamed (model : CIL.RuntimeModel) : Prop :=
  ∀ {indices : LocalIndexMap} {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} {sourceFrame targetFrame : Frame},
    Memory.Renamed mapping scopes source target →
    Frame.Renamed indices mapping scopes sourceFrame targetFrame → source.WellFormed →
    ∀ (sourceBody targetBody : CIL.Method), StepMetadata sourceBody targetBody →
    ∀ (pc : Nat) (stack : List Value), (∀ value ∈ stack, value.Below mapping.sourceLimit) →
    SuccessOrThrow (modelStep (some model) sourceBody pc sourceFrame stack source) →
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (modelStep (some model) sourceBody pc sourceFrame stack source)
      (modelStep (some model) targetBody pc targetFrame (stack.map mapping.value) target)

/-- The `System.Object` constructor's model drops the receiver alike on both sides. -/
theorem objectConstructor_stepRenamed : CIL.RuntimeModel.objectConstructor.StepRenamed := by
  intro indices mapping scopes source target sourceFrame targetFrame related frames _ _ _ _ pc
    stack _ _
  simp only [modelStep, observedCall, mapping.unspecifiedOperands, runModel]
  split
  · exact .error _
  cases stack with
  | nil => exact .error _
  | cons value rest => exact .ok (.next related frames)

#print axioms objectConstructor_stepRenamed

/-- An intrinsic's model reads only scalar operands and the profile, which related bodies share,
    so both sides fault alike or push the same value. -/
theorem intrinsic_stepRenamed (operation : CIL.Intrinsic) (argc : Nat) :
    (CIL.RuntimeModel.intrinsic operation argc).StepRenamed := by
  intro indices mapping scopes source target sourceFrame targetFrame related frames _ sourceBody
    targetBody metadata pc stack _ _
  simp only [modelStep, observedCall, mapping.unspecifiedOperands, runModel, intrinsicCall,
    metadata.profile, List.length_map, ← List.map_take, ← List.map_drop, ← List.map_reverse]
  split
  · exact .error _
  split
  · exact .error _
  split
  · exact .error _
  apply (mapping.scalarOperands _).bind
  intro values otherValues same
  subst otherValues
  apply (mapping.checkedIntrinsic _ _).bind
  intro value otherValue same
  subst otherValue
  apply (related.checkedValue _ (by trivial)).bind
  intro checked otherChecked same
  subst otherChecked
  exact .ok (.next related frames)

#print axioms intrinsic_stepRenamed

/-- A memory operation's model runs as that operation, which transports its successful effect or
    named throw on the corresponding allocations. -/
theorem memory_stepRenamed (operation : CIL.MemoryOp) :
    (CIL.RuntimeModel.memory operation).StepRenamed := by
  intro indices mapping scopes source target sourceFrame targetFrame related frames formed _ _ _
    pc stack bounds observable
  simp only [modelStep, observedCall, mapping.unspecifiedOperands, runModel,
    CIL.RuntimeModel.observerCount] at observable ⊢
  by_cases observed : unspecifiedOperands operation.argumentCount stack = true
  · simp only [observed, ite_true]
    exact .error _
  simp only [observed, Bool.false_eq_true, ite_false] at observable ⊢
  apply (related.memoryInstructionResult operation formed stack bounds
    (SuccessOrThrow.bind_left observable)).bind
  intro left right ⟨memories, values⟩
  rw [values]
  exact .ok (.next memories frames)

#print axioms memory_stepRenamed

/-- Every model of the runtime table transports under a renaming; an entry adds its model's
    case here. -/
theorem runtimeModel_stepRenamed {environment : CIL.LayoutEnvironment}
    {opcode : CIL.CallOpcode} {method : CIL.Extraction.MethodRef} {model : CIL.RuntimeModel}
    (found : CIL.Extraction.runtimeModel environment opcode method = some model) :
    model.StepRenamed :=
  CIL.Extraction.runtimeModel_yields (property := CIL.RuntimeModel.StepRenamed)
    (by
      intro entry member
      simp only [CIL.Extraction.modelEntries, List.mem_append, List.mem_cons] at member
      rcases member with ((rfl | member) | member) | member
      · exact CIL.Extraction.ModelEntry.exact_yields.mpr objectConstructor_stepRenamed
      · exact CIL.Extraction.vectorEntries_yields intrinsic_stepRenamed entry member
      · exact CIL.Extraction.integerMathEntries_yields intrinsic_stepRenamed entry member
      · exact CIL.Extraction.bitEntries_yields intrinsic_stepRenamed entry member) found

#print axioms runtimeModel_stepRenamed

/-- A direct call transports as a call or, under `tail.`, as a tail call: both bodies link its
    pc to the same callee, so both runs enter it with related arguments or fault alike. Without a
    link both run the model one environment gives its method, which continues at the next pc. -/
private theorem Memory.Renamed.stepCall {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    {sourceFrame targetFrame : Frame} (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (method : CIL.Extraction.MethodRef) (prefixes : CIL.CallPrefixes) (pc : Nat)
    (metadata : StepMetadata sourceBody targetBody)
    (arguments stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.call method prefixes) pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.call method prefixes) pc arguments sourceFrame stack source)
      (step targetBody (.call method prefixes) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target) := by
  have unobserved : unspecifiedOperands 0 stack = false := rfl
  simp only [step, observerCount, unobserved, Bool.false_eq_true, ite_false,
    observedCall, mapping.unspecifiedOperands, List.length_map, metadata.linkAt pc,
    metadata.environment, ← List.map_take, ← List.map_drop, ← List.map_reverse] at observable ⊢
  generalize sourceBody.linkAt pc = link at observable ⊢
  rcases link with _ | link
  · dsimp only at observable ⊢
    by_cases tail : prefixes.tail = true
    · simp only [tail, ite_true]
      exact .error _
    simp only [tail, Bool.false_eq_true, ite_false] at observable ⊢
    cases found : CIL.Extraction.runtimeModel sourceBody.environment .call method with
    | none => exact .error _
    | some model =>
      rw [found] at observable
      exact runtimeModel_stepRenamed found related frames formed sourceBody targetBody metadata
        pc stack bounds observable
  · by_cases guard : unspecifiedOperands method.argumentCount stack = true
    · simp only [guard, ite_true]
      exact .error _
    simp only [guard, Bool.false_eq_true, ite_false]
    cases link <;> try exact .error _
    rename_i callee
    try dsimp only
    by_cases tail : prefixes.tail = true
    · simp only [tail, ite_true]
      split
      · exact .error _
      · apply (related.checkedValues _ (by
          intro value member
          exact bounds value (List.mem_reverse.mp member))).bind
        intro first second same
        subst second
        exact .ok (.tailCall related)
    · simp only [tail, Bool.false_eq_true, ite_false]
      by_cases short : stack.length < method.argumentCount
      · simp only [short, ite_true]
        exact .error _
      · simp only [short, ite_false]
        apply (related.checkedValues _ (by
          intro value member
          exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))).bind
        intro first second same
        subst second
        exact .ok (.call related)
#print axioms Memory.Renamed.stepCall

/-- Bodies that read an argument from the incoming list, narrowed alike, load related values. -/
theorem Memory.Renamed.loadArgument {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target) {sourceBody targetBody : CIL.Method}
    {index : Nat} {narrow : Option NarrowKind}
    (sourceAccess : sourceBody.argumentAccess index = .value narrow)
    (targetAccess : targetBody.argumentAccess index = .value narrow) (arguments : List Value)
    (argumentBounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun left right => right = mapping.value left)
      (loadArgument sourceBody index arguments sourceFrame source)
      (loadArgument targetBody index (arguments.map mapping.value) targetFrame target) := by
  unfold CIL.Safety.loadArgument
  rw [sourceAccess, targetAccess, List.getElem?_map]
  cases found : arguments[index]? with
  | none => cases narrow <;> exact .error .invalidState
  | some value =>
    have bound := argumentBounds value (List.mem_of_getElem? found)
    cases narrow with
    | none => exact related.checkedValue value bound
    | some kind =>
      dsimp only [Option.map]
      rw [mapping.hasUnspecified]
      by_cases unspecified : value.hasUnspecified = true
      · simp only [unspecified, ↓reduceIte]
        exact .error _
      · simp only [unspecified, Bool.false_eq_true, ↓reduceIte]
        cases value <;> try exact .error .invalidState
        rename_i scalar
        cases scalar <;> try exact .error .invalidState
        exact related.checkedValue _ trivial
#print axioms Memory.Renamed.loadArgument

/-- The source body reads every argument as it arrives, so `starg` has no home to write. -/
theorem StepMetadata.storeArgument_source {sourceBody targetBody : CIL.Method}
    (metadata : StepMetadata sourceBody targetBody) (index : Nat) (value : Value) (frame : Frame)
    (memory : Memory) :
    storeArgument sourceBody index value frame memory =
      .error (.unsupported "Store to an argument without a home") := by
  obtain ⟨_, sourceAccess, -⟩ := metadata.arguments index
  simp only [storeArgument, sourceAccess]
#print axioms StepMetadata.storeArgument_source

/-- The source body reads every argument as it arrives, so `ldarga` has no home to address. -/
theorem StepMetadata.addressArgument_source {sourceBody targetBody : CIL.Method}
    (metadata : StepMetadata sourceBody targetBody) (index : Nat) (frame : Frame)
    (memory : Memory) :
    addressArgument sourceBody index frame memory =
      .error (.unsupported "Address of an argument without a home") := by
  obtain ⟨_, sourceAccess, -⟩ := metadata.arguments index
  simp only [addressArgument, sourceAccess]
#print axioms StepMetadata.addressArgument_source

/-- The target body reads every argument as it arrives, so `starg` has no home to write. -/
theorem StepMetadata.storeArgument_target {sourceBody targetBody : CIL.Method}
    (metadata : StepMetadata sourceBody targetBody) (index : Nat) (value : Value) (frame : Frame)
    (memory : Memory) :
    storeArgument targetBody index value frame memory =
      .error (.unsupported "Store to an argument without a home") := by
  obtain ⟨_, -, targetAccess⟩ := metadata.arguments index
  simp only [storeArgument, targetAccess]
#print axioms StepMetadata.storeArgument_target

/-- The target body reads every argument as it arrives, so `ldarga` has no home to address. -/
theorem StepMetadata.addressArgument_target {sourceBody targetBody : CIL.Method}
    (metadata : StepMetadata sourceBody targetBody) (index : Nat) (frame : Frame)
    (memory : Memory) :
    addressArgument targetBody index frame memory =
      .error (.unsupported "Address of an argument without a home") := by
  obtain ⟨_, -, targetAccess⟩ := metadata.arguments index
  simp only [addressArgument, targetAccess]
#print axioms StepMetadata.addressArgument_target

/-- Argument loads, calls and returns preserve their checked values and control flow; argument
    stores and addresses cannot succeed or throw without a home. -/
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
    rw [mapping.unspecifiedOperands]
    by_cases guarded : unspecifiedOperands (observerCount (.managed native)) stack = true
    · simp only [guarded, ite_true]
      exact .error (.unsupported "Instruction observes unspecified vector bits")
    · simp only [guarded, Bool.false_eq_true, ite_false] at observable ⊢
      rw [metadata.linkAt pc]
      exact related.managedStep frames native _ pc stack bounds observable
  by_cases direct : ∃ method prefixes, operation = .call method prefixes
  · rcases direct with ⟨method, prefixes, rfl⟩
    exact related.stepCall frames formed sourceBody targetBody method prefixes pc metadata
      arguments stack bounds observable
  by_cases receiverChecked : ∃ callee argc, operation = .callInstance callee argc
  · rcases receiverChecked with ⟨callee, argc, rfl⟩
    exact related.stepCallInstance formed sourceBody targetBody callee argc pc
      (metadata.linkAt pc) arguments stack bounds
  by_cases dispatched : ∃ targets argc, operation = .callVirtual targets argc
  · rcases dispatched with ⟨targets, argc, rfl⟩
    exact related.stepCallVirtual sourceBody targetBody targets argc pc (metadata.linkAt pc)
      arguments stack bounds
  by_cases casting : ∃ type, operation = .castclass type
  · rcases casting with ⟨type, rfl⟩
    exact related.stepTypeTest frames sourceBody targetBody _ type true (.inl ⟨rfl, rfl⟩) pc
      arguments stack bounds
  by_cases testing : ∃ type, operation = .isinst type
  · rcases testing with ⟨type, rfl⟩
    exact related.stepTypeTest frames sourceBody targetBody _ type false (.inr ⟨rfl, rfl⟩) pc
      arguments stack bounds
  ·
    allocation_fixed_step (
      first
      | exact False.elim (isManaged ⟨_, rfl⟩)
      | exact False.elim (direct ⟨_, _, rfl⟩)
      | exact False.elim (receiverChecked ⟨_, _, rfl⟩)
      | exact False.elim (dispatched ⟨_, _, rfl⟩)
      | exact False.elim (casting ⟨_, rfl⟩)
      | exact False.elim (testing ⟨_, rfl⟩)
      -- Both bodies read every argument without a home, so a store or an address faults alike.
      | (simp only [metadata.storeArgument_source, metadata.storeArgument_target,
           metadata.addressArgument_source, metadata.addressArgument_target, Bind.bind,
           Except.bind]
         exact .error _)
      | (rename_i position
         obtain ⟨_, sourceAccess, targetAccess⟩ := metadata.arguments position
         apply (related.loadArgument sourceAccess targetAccess arguments argumentBounds).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
      | (try simp only [List.length_map, ← List.map_take, ← List.map_drop, ← List.map_reverse]
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
         skip)
      all_goals
        cases narrowing : sourceBody.returnNarrow with
        | none =>
          simp only [narrowing, returnFrom, List.length_map]
          by_cases sized : stack.length = (if sourceBody.returnsValue then 1 else 0)
          · simp only [sized, ↓reduceIte]
            apply (related.checkedValues stack bounds).bind
            intro first second same
            subst second
            exact .ok (.returned related)
          · simp only [sized, ↓reduceIte]
            exact .error .invalidState
        | some kind =>
          cases stack with
          | nil => exact .error .invalidState
          | cons value rest =>
            cases value <;> try exact .error .invalidState
            rename_i scalar
            cases scalar <;> cases rest <;> try exact .error .invalidState
            simp only [returnFrom, List.map_cons, List.map_nil, AllocationRenaming.value]
            split <;> first | exact .ok (.returned related) | exact .error .invalidState)
#print axioms Memory.Renamed.stepBoundary

end CIL.Safety
