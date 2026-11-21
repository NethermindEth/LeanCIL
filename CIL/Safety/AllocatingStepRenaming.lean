import CIL.Safety.StepTransport
import CIL.Safety.StepComposition
import CIL.Safety.StaticInstructionRenaming
import CIL.Safety.StackAllocationRenaming
import CIL.Safety.ArrayAllocationRenaming
import CIL.Safety.InstructionRenaming
import CIL.Safety.SpanHomeRenaming

/-!
# Checked allocating instruction steps

Static storage and dynamic stack storage extend allocation maps while keeping retained frames,
operand checks and named exceptions consistent with the actual checked dispatcher.
The memory case reuses the checked step equation instead of simplifying the full dispatcher.
-/

namespace CIL.Safety

-- Stack lists are renamed by the local map of the frame that holds them.
variable {indices : LocalIndexMap}

/-- Memory dispatch reads neither the method nor the pc, so two bodies agree on it. -/
theorem staticInstruction_body (sourceBody targetBody : CIL.Method) (pc : Nat)
    (operation : CIL.MemoryOp) (stack : List Value) (memory : Memory) :
    staticInstruction targetBody pc operation stack memory =
      staticInstruction sourceBody pc operation stack memory := rfl
#print axioms staticInstruction_body

/-- Checked memory steps, span constructors over static storage included, extend the map only
    when their actual operation allocates. -/
theorem Memory.Renamed.memoryModelStep {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (operation : CIL.MemoryOp) (pc : Nat) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (modelStep (some (.memory operation)) sourceBody pc sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (modelStep (some (.memory operation)) sourceBody pc sourceFrame stack source)
        (modelStep (some (.memory operation)) targetBody pc targetFrame (stack.map (indices.value mapping)) target) := by
  simp only [modelStep_memory, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false,
      staticInstruction_body sourceBody targetBody] at observable ⊢
    apply (frames.viewOperands related (viewOperandCount operation) stack bounds).bindExtending
    intro viewed otherViewed sourceViewed operandsRelated
    obtain ⟨rfl, viewedBounds⟩ := operandsRelated
    obtain ⟨later, extension, operations⟩ := related.staticInstructionResult sourceFormed
      sourceBody pc operation viewed viewedBounds (observable.bind_right sourceViewed).bind_left
    refine ⟨later, extension, ?_⟩
    apply operations.bind
    intro first second result
    rcases first with ⟨sourceAfter, values⟩
    rcases second with ⟨targetAfter, targetValues⟩
    rcases result with ⟨memories, rfl⟩
    exact .ok (.next memories (frames.extend extension (fun _ _ scope => scope)))
#print axioms Memory.Renamed.memoryModelStep

/-- A typed element access after its operand check touches the mapped element and keeps the
    allocation map: both bodies give the element the same shape. -/
private theorem Memory.Renamed.typedElementStep {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    {sourceFrame targetFrame : Frame} (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (element : CIL.Extraction.TypeExpr)
    (store : Bool) (pc : Nat) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (do
      let (memory, values) ←
        typedElementInstruction (sourceBody.elementShape element) store stack source
      return FrameAction.next (pc + 1) values sourceFrame memory)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (do
        let (memory, values) ←
          typedElementInstruction (sourceBody.elementShape element) store stack source
        return FrameAction.next (pc + 1) values sourceFrame memory)
      (do
        let (memory, values) ← typedElementInstruction (targetBody.elementShape element) store
          (stack.map (indices.value mapping)) target
        return FrameAction.next (pc + 1) values targetFrame memory) := by
  have shaped : targetBody.elementShape element = sourceBody.elementShape element := by
    simp only [CIL.Method.elementShape, metadata.environment]
  rw [shaped]
  apply (related.typedElementInstructionResult _ store sourceFormed stack bounds
    observable.bind_left).bind
  intro first second result
  rcases first with ⟨sourceAfter, values⟩
  rcases second with ⟨targetAfter, targetValues⟩
  rcases result with ⟨memories, rfl⟩
  exact .ok (.next memories frames)
#print axioms Memory.Renamed.typedElementStep

/-- A checked typed `ldelem` step keeps the allocation map. -/
theorem Memory.Renamed.stepLdelemAny {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (element : CIL.Extraction.TypeExpr)
    (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.ldelem_any element) pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.ldelem_any element) pc arguments sourceFrame stack source)
      (step targetBody (.ldelem_any element) pc (arguments.map mapping.value)
        targetFrame (stack.map (indices.value mapping)) target) := by
  simp only [step_ldelem_any_eq, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    exact related.typedElementStep frames sourceFormed sourceBody targetBody metadata element
      false pc stack bounds observable
#print axioms Memory.Renamed.stepLdelemAny

/-- A checked typed `stelem` step keeps the allocation map. -/
theorem Memory.Renamed.stepStelemAny {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (element : CIL.Extraction.TypeExpr)
    (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.stelem_any element) pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.stelem_any element) pc arguments sourceFrame stack source)
      (step targetBody (.stelem_any element) pc (arguments.map mapping.value)
        targetFrame (stack.map (indices.value mapping)) target) := by
  simp only [step_stelem_any_eq, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    exact related.typedElementStep frames sourceFormed sourceBody targetBody metadata element
      true pc stack bounds observable
#print axioms Memory.Renamed.stepStelemAny

/-- A checked `ldelema` step keeps the allocation map: both bodies give the element the same
    shape. -/
theorem Memory.Renamed.stepLdelema {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (sourceBody targetBody : CIL.Method)
    (metadata : StepMetadata sourceBody targetBody) (element : CIL.Extraction.TypeExpr)
    (readOnly : Bool) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.ldelema element readOnly) pc arguments sourceFrame stack source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.ldelema element readOnly) pc arguments sourceFrame stack source)
      (step targetBody (.ldelema element readOnly) pc (arguments.map mapping.value)
        targetFrame (stack.map (indices.value mapping)) target) := by
  simp only [step_ldelema_eq, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    have shaped : targetBody.elementShape element = sourceBody.elementShape element := by
      simp only [CIL.Method.elementShape, metadata.environment]
    rw [shaped]
    apply (related.elementAddressInstructionResult _ readOnly sourceFormed stack bounds
      observable.bind_left).bind
    intro first second result
    rcases first with ⟨sourceAfter, values⟩
    rcases second with ⟨targetAfter, targetValues⟩
    rcases result with ⟨memories, rfl⟩
    exact .ok (.next memories frames)
#print axioms Memory.Renamed.stepLdelema

/-- `ldsfld` reads the descriptor bound to its pc, which a step renaming keeps. -/
theorem staticLoad_metadata {sourceBody targetBody : CIL.Method}
    (metadata : StepMetadata sourceBody targetBody) (pc : Nat) (memory : Memory) :
    staticLoad targetBody pc memory = staticLoad sourceBody pc memory := by
  unfold staticLoad CIL.Method.staticAt
  rw [metadata.staticSites]
#print axioms staticLoad_metadata

/-- `ldsflda` reads the descriptor bound to its pc, which a step renaming keeps. -/
theorem staticAddress_metadata {sourceBody targetBody : CIL.Method}
    (metadata : StepMetadata sourceBody targetBody) (pc : Nat) (memory : Memory) :
    staticAddress targetBody pc memory = staticAddress sourceBody pc memory := by
  unfold staticAddress CIL.Method.staticAt
  rw [metadata.staticSites]
#print axioms staticAddress_metadata

/-- A checked `ldsfld` step keeps the allocation map. -/
theorem Memory.Renamed.stepLdsfld {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceBody targetBody : CIL.Method) (metadata : StepMetadata sourceBody targetBody)
    (field : CIL.Extraction.FieldRef) (pc : Nat) (arguments stack : List Value) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (step sourceBody (.ldsfld field) pc arguments sourceFrame stack source)
      (step targetBody (.ldsfld field) pc (arguments.map mapping.value) targetFrame
        (stack.map (indices.value mapping)) target) := by
  show ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
    (do
      let (memory, value) ← staticLoad sourceBody pc source
      return FrameAction.next (pc + 1) (value :: stack) sourceFrame memory)
    (do
      let (memory, value) ← staticLoad targetBody pc target
      return FrameAction.next (pc + 1) (value :: stack.map (indices.value mapping)) targetFrame
        memory)
  rw [staticLoad_metadata metadata]
  apply (related.staticLoadResult staticBounds sourceBody pc).bindWithSuccess
  intro first second loaded result
  rcases first with ⟨sourceAfter, value⟩
  rcases second with ⟨targetAfter, targetValue⟩
  rcases result with ⟨memories, rfl⟩
  dsimp only
  rw [indices.push_of_not_home mapping stack (staticLoad_not_spanHome loaded)]
  exact .ok (.next memories frames)
#print axioms Memory.Renamed.stepLdsfld

/-- A checked `ldsflda` or field `ldtoken` step extends the map only when the field's storage
    is allocated. -/
theorem Memory.Renamed.stepStaticAddress {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceBody targetBody : CIL.Method) (metadata : StepMetadata sourceBody targetBody)
    (operation : CIL.Instruction)
    (addressed : ∀ body pc args frame stack memory,
      step body operation pc args frame stack memory = do
        let (memory, value) ← staticAddress body pc memory
        return FrameAction.next (pc + 1) (value :: stack) frame memory)
    (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody operation pc arguments sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody operation pc arguments sourceFrame stack source)
        (step targetBody operation pc (arguments.map mapping.value)
          targetFrame (stack.map (indices.value mapping)) target) := by
  simp only [addressed, staticAddress_metadata metadata] at observable ⊢
  obtain ⟨later, extension, operations⟩ := related.staticAddressResult sourceFormed
    targetFormed staticBounds sourceBody pc observable.bind_left
  refine ⟨later, extension, ?_⟩
  apply operations.bindWithSuccess
  intro first second addressed result
  rcases first with ⟨sourceAfter, value⟩
  rcases second with ⟨targetAfter, targetValue⟩
  rcases result with ⟨memories, rfl⟩
  dsimp only
  rw [← indices.values_extends extension stack bounds,
    indices.push_of_not_home later stack (staticAddress_not_spanHome addressed)]
  exact .ok (.next memories (frames.extend extension (fun _ _ scope => scope)))
#print axioms Memory.Renamed.stepStaticAddress

/-- An instance field load reads the related field, which both bodies resolve alike. -/
theorem Memory.Renamed.stepFieldLoad {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed)
    (sourceBody targetBody : CIL.Method) (metadata : StepMetadata sourceBody targetBody)
    (field : CIL.Extraction.FieldRef) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.ldfld field) pc arguments sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody (.ldfld field) pc arguments sourceFrame stack source)
        (step targetBody (.ldfld field) pc (arguments.map mapping.value)
          targetFrame (stack.map (indices.value mapping)) target) := by
  refine ⟨mapping, .refl mapping, ?_⟩
  have shape : targetBody.fieldShape field = sourceBody.fieldShape field := by
    simp only [CIL.Method.fieldShape, metadata.environment]
  simp only [step_ldfld_eq, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    unfold fieldLoad at observable ⊢
    rw [shape]
    cases resolved : sourceBody.fieldShape field
    all_goals simp only [resolved] at observable ⊢
    all_goals first
      | exact .error _
      | apply (related.classFieldLoadResult _ _ _ sourceFormed stack bounds
          observable.bind_left).bind
      | apply (related.loadAggregateFieldResult sourceFormed _ _ stack bounds
          observable.bind_left).bind
      | apply (related.loadValueFieldResult sourceFormed _ _ _ stack bounds observable.bind_left).bind
    all_goals
      intro first second result
      rcases first with ⟨sourceAfter, values⟩
      rcases second with ⟨targetAfter, targetValues⟩
      rcases result with ⟨memories, rfl⟩
      exact .ok (.next memories frames)
#print axioms Memory.Renamed.stepFieldLoad

/-- An instance field store writes the related field, which both bodies resolve alike. -/
theorem Memory.Renamed.stepFieldStore {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed)
    (sourceBody targetBody : CIL.Method) (metadata : StepMetadata sourceBody targetBody)
    (field : CIL.Extraction.FieldRef) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.stfld field) pc arguments sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody (.stfld field) pc arguments sourceFrame stack source)
        (step targetBody (.stfld field) pc (arguments.map mapping.value)
          targetFrame (stack.map (indices.value mapping)) target) := by
  refine ⟨mapping, .refl mapping, ?_⟩
  have shape : targetBody.fieldShape field = sourceBody.fieldShape field := by
    simp only [CIL.Method.fieldShape, metadata.environment]
  simp only [step_stfld_eq, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    unfold fieldStore at observable ⊢
    rw [shape]
    cases resolved : sourceBody.fieldShape field
    all_goals simp only [resolved] at observable ⊢
    all_goals first
      | exact .error _
      | apply (related.classFieldStoreResult _ _ _ sourceFormed stack bounds
          observable.bind_left).bind
      | apply (related.storeAggregateFieldResult sourceFormed _ _ stack bounds
          observable.bind_left).bind
      | apply (related.storeValueFieldResult sourceFormed _ _ stack bounds observable.bind_left).bind
    all_goals
      intro first second result
      rcases first with ⟨sourceAfter, values⟩
      rcases second with ⟨targetAfter, targetValues⟩
      rcases result with ⟨memories, rfl⟩
      exact .ok (.next memories frames)
#print axioms Memory.Renamed.stepFieldStore

/-- An instance field address forms the related address, which both bodies resolve alike. -/
theorem Memory.Renamed.stepFieldAddress {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed)
    (sourceBody targetBody : CIL.Method) (metadata : StepMetadata sourceBody targetBody)
    (field : CIL.Extraction.FieldRef) (pc : Nat) (arguments stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.ldflda field) pc arguments sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody (.ldflda field) pc arguments sourceFrame stack source)
        (step targetBody (.ldflda field) pc (arguments.map mapping.value)
          targetFrame (stack.map (indices.value mapping)) target) := by
  refine ⟨mapping, .refl mapping, ?_⟩
  have shape : targetBody.fieldShape field = sourceBody.fieldShape field := by
    simp only [CIL.Method.fieldShape, metadata.environment]
  simp only [step_ldflda_eq, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    unfold fieldReference at observable ⊢
    rw [shape]
    cases resolved : sourceBody.fieldShape field
    all_goals simp only [resolved] at observable ⊢
    all_goals first
      | exact .error _
      | (apply (related.structFieldAddressResult sourceFormed _ stack bounds observable.bind_left).bind
         intro first second result
         rcases first with ⟨sourceAfter, values⟩
         rcases second with ⟨targetAfter, targetValues⟩
         rcases result with ⟨memories, rfl⟩
         exact .ok (.next memories frames))
#print axioms Memory.Renamed.stepFieldAddress

/-- Stack allocation faults are resource or memory failures, never named CLR exceptions. -/
theorem allocateStack_not_thrown (memory : Memory) (frame : Frame) (size : Nat)
    (initLocals : Bool) (exception : ExceptionType) :
    allocateStack memory frame size initLocals ≠ .error (.thrown exception) := by
  intro raised
  unfold allocateStack allocateHome checkedAt at raised
  repeat' first
    | cases raised
    | split at raised
    | simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at raised
  all_goals rename_i found
  all_goals split at found <;> cases found
  all_goals rename_i found
  all_goals split at found <;> cases found
#print axioms allocateStack_not_thrown

/-- Actual dynamic stack steps extend ownership and preserve exact quota and initialization rules.
    -/
theorem Memory.Renamed.stepLocalloc {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceBody targetBody : CIL.Method) (declared : targetBody.declared = sourceBody.declared)
    (pc : Nat) (arguments stack : List Value)
    (observable : SuccessOrThrow
      (step sourceBody .localloc pc arguments sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody .localloc pc arguments sourceFrame stack source)
        (step targetBody .localloc pc (arguments.map mapping.value)
          targetFrame (stack.map (indices.value mapping)) target) := by
  simp only [step, declared, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false, localAllocation] at observable ⊢
    split at observable
    · rename_i size
      simp only [List.map_cons, List.map_nil, LocalIndexMap.value]
      cases size <;> simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at observable ⊢
      all_goals try cases observable
      all_goals rename_i bits
      all_goals
        cases allocated : CIL.Safety.allocateStack source sourceFrame bits.toNat
            sourceBody.declared.initLocals with
        | error fault =>
          cases fault <;> simp only [allocated, SuccessOrThrow] at observable
          rename_i exception
          exact False.elim (allocateStack_not_thrown source sourceFrame _ _
            exception allocated)
        | ok result =>
          obtain ⟨reference, finalFrame, finalMemory⟩ := result
          obtain ⟨later, targetReference, targetFinal, targetAfter, extension, targetAllocated,
            referenceEqual, finalFrames, memories⟩ :=
            related.allocateStack frames sourceFormed targetFormed staticBounds _ _
              reference allocated
          subst targetReference
          refine ⟨later, extension, ?_⟩
          simp only [targetAllocated]
          exact .ok (.next memories finalFrames)
    · cases observable
#print axioms Memory.Renamed.stepLocalloc

/-- Heap-resource and allocator faults cannot discharge a named exception obligation. -/
theorem allocateArray_not_thrown (memory : Memory) (element : CIL.ArrayElement) (length : Nat)
    (exception : ExceptionType) :
    allocateArray memory element length ≠ .error (.thrown exception) := by
  intro raised
  unfold allocateArray checkedAt at raised
  repeat' first
    | cases raised
    | split at raised
    | simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at raised
  all_goals rename_i found
  all_goals split at found <;> cases found
#print axioms allocateArray_not_thrown


/-- Heap-budget and allocator faults cannot discharge a named exception obligation. -/
theorem allocateObject_not_thrown (memory : Memory) (type : RuntimeType) (size : Nat)
    (exception : ExceptionType) :
    allocateObject memory type size ≠ .error (.thrown exception) := by
  intro raised
  unfold allocateObject checkedAt at raised
  repeat' first
    | cases raised
    | split at raised
    | simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at raised
  all_goals rename_i found
  all_goals split at found <;> cases found
#print axioms allocateObject_not_thrown

/-- A class construction transports its fresh instance and checked arguments into the
    constructor call, and leaves the instance under the same mapped caller stack. -/
theorem Memory.Renamed.constructObject {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (callee argc : Nat) (type : RuntimeType) (size : Nat)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (CIL.Safety.constructObject callee argc type size sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (CIL.Safety.constructObject callee argc type size sourceFrame stack source)
        (CIL.Safety.constructObject callee argc type size targetFrame
          (stack.map (indices.value mapping)) target) := by
  unfold CIL.Safety.constructObject at observable ⊢
  simp only [List.length_map, ← List.map_take, ← List.map_drop, ← List.map_reverse]
  by_cases short : stack.length < argc
  · simp only [short, ite_true]
    exact ⟨mapping, .refl mapping, .error _⟩
  · simp only [short, ite_false] at observable ⊢
    have checks := frames.callArguments related (stack.take argc).reverse (by
      intro value member
      exact bounds value (List.mem_of_mem_take (List.mem_reverse.mp member)))
    cases checked :
        (stack.take argc).reverse.mapM (CIL.Safety.callArgument sourceFrame source) with
    | error fault =>
      rw [checked] at checks
      generalize ((stack.take argc).reverse.map (indices.value mapping)).mapM
        (CIL.Safety.callArgument targetFrame target) = targetChecked at checks ⊢
      cases checks
      exact ⟨mapping, .refl mapping, .error fault⟩
    | ok operands =>
      have operandBounds : ∀ value ∈ operands, value.Below mapping.sourceLimit := by
        intro value member
        rw [related.sourceLimit]
        exact (callArguments_valid checked value member).below sourceFormed
      rw [checked] at checks
      obtain ⟨targetOperands, targetChecked, rfl⟩ := checks.success
      simp only [checked, Bind.bind, Except.bind] at observable
      cases allocated : CIL.Safety.allocateObject source type size with
      | error fault =>
        rw [allocated] at observable
        cases fault <;> simp only [SuccessOrThrow] at observable
        rename_i exception
        exact False.elim (allocateObject_not_thrown source _ _ exception allocated)
      | ok result =>
        obtain ⟨object, sourceAfter⟩ := result
        obtain ⟨targetAfter, targetAllocated, memories⟩ := related.allocateObject sourceFormed
          targetFormed staticBounds _ size object sourceAfter allocated
        refine ⟨mapping.allocate, mapping.allocate_extends, ?_⟩
        simp only [targetChecked, targetAllocated, Bind.bind, Except.bind]
        have operandsSame := mapping.allocate_extends.values operands operandBounds
        have restSame := indices.values_extends mapping.allocate_extends (stack.drop argc) (by
          intro value member
          exact bounds value (List.mem_of_mem_drop member))
        rw [← operandsSame, ← restSame]
        simpa only [List.map_cons, AllocationRenaming.value, LocalIndexMap.value,
          AllocationRenaming.managedReference, Pure.pure, Except.pure] using
          ResultRenamed.ok (FrameAction.Renamed.call (indices := indices) (callee := callee)
            (arguments := .object (.address object) :: operands)
            (rest := .object (.address object) :: stack.drop argc) memories)

#print axioms Memory.Renamed.constructObject

/-- `newarr` transports its fresh heap identity and retains the current frame: both bodies give
    the element the same shape, since their layout environments are equal. -/
theorem Memory.Renamed.stepNewarr {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceBody targetBody : CIL.Method) (metadata : StepMetadata sourceBody targetBody)
    (element : CIL.Extraction.TypeExpr) (pc : Nat)
    (arguments stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (step sourceBody (.newarr element) pc arguments sourceFrame stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later (FrameAction.Renamed indices later scopes)
        (step sourceBody (.newarr element) pc arguments sourceFrame stack source)
        (step targetBody (.newarr element) pc (arguments.map mapping.value)
          targetFrame (stack.map (indices.value mapping)) target) := by
  have shaped : targetBody.elementShape element = sourceBody.elementShape element := by
    simp only [CIL.Method.elementShape, metadata.environment]
  simp only [step, indices.unspecifiedOperands mapping] at observable ⊢
  split at observable
  · cases observable
  · rename_i guard
    simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    split at observable <;> try contradiction
    · rename_i length rest same
      cases same
      simp only [List.map_cons, LocalIndexMap.value, shaped]
      have restBounds : ∀ value ∈ rest, value.Below mapping.sourceLimit :=
        fun value member => bounds value (List.mem_cons_of_mem _ member)
      generalize sourceBody.elementShape element = shape at observable ⊢
      cases shape with
      | value inline =>
        cases length <;> simp only [allocateElements, newArray, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at observable ⊢
        all_goals cases supported : inline.allocationSupported
        all_goals simp only [supported, Bool.not_true, Bool.not_false, Bool.false_eq_true,
          ite_true, ite_false] at observable ⊢
        all_goals try cases observable
        all_goals rename_i bits
        all_goals by_cases negative : bits.toInt < 0
        all_goals simp only [negative, ite_true, ite_false] at observable ⊢
        all_goals first
        | exact ⟨mapping, .refl mapping, .error _⟩
        | (cases allocated : CIL.Safety.allocateArray source inline bits.toInt.toNat with
           | error fault =>
             cases fault <;> simp only [allocated, SuccessOrThrow] at observable
             rename_i exception
             exact False.elim (allocateArray_not_thrown source inline _ exception allocated)
           | ok result =>
             obtain ⟨view, sourceAfter⟩ := result
             obtain ⟨targetAfter, targetAllocated, memories⟩ := related.allocateArray
               sourceFormed targetFormed staticBounds inline _ view sourceAfter allocated
             refine ⟨mapping.allocate, mapping.allocate_extends, ?_⟩
             simp only [targetAllocated]
             rw [← indices.values_extends mapping.allocate_extends rest restBounds]
             exact .ok (.next memories
               (frames.extend mapping.allocate_extends (fun _ _ scope => scope))))
      | reference classElement =>
        cases length <;> simp only [allocateElements, newReferenceArray, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at observable ⊢
        all_goals try cases observable
        all_goals rename_i bits
        all_goals by_cases negative : bits.toInt < 0
        all_goals simp only [negative, ite_true, ite_false] at observable ⊢
        all_goals by_cases large : maxArrayLength < bits.toInt.toNat
        all_goals try simp only [gt_iff_lt, large, ite_true, ite_false] at observable ⊢
        all_goals first
        | exact ⟨mapping, .refl mapping, .error _⟩
        | (cases allocated : CIL.Safety.allocateObject source (referenceArrayType classElement)
              (objectFieldSlot * bits.toInt.toNat) with
           | error fault =>
             cases fault <;> simp only [allocated, SuccessOrThrow] at observable
             rename_i exception
             exact False.elim (allocateObject_not_thrown source _ _ exception allocated)
           | ok result =>
             obtain ⟨array, sourceAfter⟩ := result
             obtain ⟨targetAfter, targetAllocated, memories⟩ := related.allocateObject
               sourceFormed targetFormed staticBounds _ _ array sourceAfter allocated
             refine ⟨mapping.allocate, mapping.allocate_extends, ?_⟩
             simp only [targetAllocated]
             rw [← indices.values_extends mapping.allocate_extends rest restBounds]
             simpa only [List.map_cons, AllocationRenaming.value, LocalIndexMap.value,
               AllocationRenaming.managedReference, Pure.pure, Except.pure] using
               ResultRenamed.ok (FrameAction.Renamed.next (pc := pc + 1)
                 (stack := .object (.address array) :: rest) memories
                 (frames.extend mapping.allocate_extends (fun _ _ scope => scope))))
      | method signature => exact ⟨mapping, .refl mapping, .error _⟩
      | unsupported reason => exact ⟨mapping, .refl mapping, .error _⟩
    · rw [show pureArity (.newarr element) = none from rfl] at observable
      simp only [instruction] at observable
      split at observable <;> cases observable

#print axioms Memory.Renamed.stepNewarr

end CIL.Safety
