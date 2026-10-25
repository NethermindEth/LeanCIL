import CIL.Safety.MethodRenaming
import CIL.Safety.StaticBindingBounds
import CIL.Safety.ReturnReferences
import CIL.Safety.RenamedMemoryBelow
import CIL.Safety.LocalLoadRenaming
import CIL.Safety.OutcomeContract

/-!
# Whole checked executions under allocation renaming

Successful runs compose checked instruction transport, paired frame entry and frame exit.
Nested calls extend allocation and activation correspondences without changing caller values.
-/

namespace CIL.Safety

/-- Successful corresponding instructions produce related actions and an extended allocation map. -/
theorem MethodRenaming.step_success (transport : StepTransport)
    {sourceBody targetBody : CIL.Method} (methods : MethodRenaming sourceBody targetBody)
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} {sourceFrame targetFrame : Frame}
    (memory : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed methods.indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (statics : source.StaticBindingsBounded) {arguments stack : List Value}
    (argumentValues : ValuesValid source arguments) (stackValues : ValuesValid source stack)
    {operation : CIL.Op} {pc : Nat} {action : FrameAction}
    (stepped : step sourceBody operation pc arguments sourceFrame stack source = .ok action) :
    ∃ later targetAction, mapping.Extends later ∧
      step targetBody (methods.indices.operation operation) pc (arguments.map mapping.value)
        targetFrame (stack.map mapping.value) target = .ok targetAction ∧
      FrameAction.Renamed methods.indices later scopes action targetAction := by
  obtain ⟨later, extension, actions⟩ := transport methods.indices mapping scopes
    sourceBody targetBody operation pc arguments stack sourceFrame targetFrame source target
    methods.metadata memory frames sourceFormed targetFormed
    (by rw [memory.sourceLimit]; exact statics)
    (by rw [memory.sourceLimit]; exact argumentValues.below sourceFormed)
    (by rw [memory.sourceLimit]; exact stackValues.below sourceFormed)
    (by rw [stepped]; trivial)
  rw [stepped] at actions
  obtain ⟨targetAction, targetStepped, related⟩ := actions.success
  exact ⟨later, targetAction, extension, targetStepped, related⟩
#print axioms MethodRenaming.step_success

/-- A successful result has corresponding final memory and values under an extended map. -/
def SuccessfulRenaming (mapping : AllocationRenaming) (scopes : Nat → Nat → Prop)
    (source : Memory) (values : List Value)
    (target : Except LocatedFault (Memory × List Value)) : Prop :=
  ∃ later after final, mapping.Extends later ∧
    (∀ left right, scopes left right → after left right) ∧
    Memory.Renamed later after source final ∧ target = .ok (final, values.map later.value)

/-- Earlier map and activation extensions compose with a successful continuation. -/
theorem SuccessfulRenaming.prepend {earlier middle : AllocationRenaming}
    {before after : Nat → Nat → Prop} {source : Memory} {values : List Value}
    {target : Except LocatedFault (Memory × List Value)}
    (related : SuccessfulRenaming middle after source values target)
    (extension : earlier.Extends middle)
    (scopes : ∀ left right, before left right → after left right) :
    SuccessfulRenaming earlier before source values target := by
  obtain ⟨later, finalScopes, final, laterExtension, scopeExtension, memory, result⟩ := related
  exact ⟨later, finalScopes, final, extension.trans laterExtension,
    fun left right known => scopeExtension left right (scopes left right known), memory, result⟩
#print axioms SuccessfulRenaming.prepend

/-- Actual successful traces transport through local relocation and paired frame allocation. -/
theorem RunTrace.rename (transport : StepTransport)
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {fuel method pc : Nat} {arguments stack values : List Value} {sourceFrame : Frame}
    {source final : Memory}
    (trace : RunTrace sourceProgram fuel method pc arguments sourceFrame stack source final values)
    {sourceBody targetBody : CIL.Method}
    (sourceFound : sourceProgram[method]? = some sourceBody)
    (targetFound : targetProgram[method]? = some targetBody)
    (methods : MethodRenaming sourceBody targetBody)
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {target : Memory}
    {targetFrame : Frame} (memory : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed methods.indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (statics : source.StaticBindingsBounded)
    (argumentValues : ValuesValid source arguments) (stackValues : ValuesValid source stack) :
    SuccessfulRenaming mapping scopes final values
      (run targetProgram fuel method pc (arguments.map mapping.value) targetFrame
        (stack.map mapping.value) target) := by
  induction trace generalizing sourceBody targetBody mapping scopes target targetFrame with
  | @next fuel method pc arguments sourceFrame stack source nextPc nextStack nextFrame
      updated final values actual following induction =>
    obtain ⟨body, operation, found, fetched, stepped⟩ := actual
    have same : body = sourceBody := Option.some.inj (found.symm.trans sourceFound)
    subst body
    obtain ⟨middle, action, extension, targetStepped, actions⟩ := methods.step_success transport
      memory frames sourceFormed targetFormed statics argumentValues stackValues stepped
    cases actions with
    | next renamed nextFrames =>
      have contract := step_contract _ _ _ _ _ _ _ _ stepped
      have sourceReady := contract.effect.wellFormed sourceFormed
      have targetReady := step_preserves_wellFormed _ _ _ _ _ _ _ _ targetFormed targetStepped
      have continued := induction sourceFound targetFound methods renamed nextFrames sourceReady
        targetReady (contract.effect.staticBindingsBounded statics)
        (argumentValues.preserve sourceFormed contract.effect.allocations)
        (contract.values sourceFormed stackValues)
      have argumentBounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit := by
        rw [memory.sourceLimit]
        exact argumentValues.below sourceFormed
      simp only [run, targetFound, methods.instruction fetched, targetStepped,
        Except.mapError, Bind.bind, Except.bind]
      rw [← extension.values arguments argumentBounds]
      exact continued.prepend extension (fun _ _ scope => scope)
  | @returned fuel method pc arguments sourceFrame stack source raw updated values
      actual checked =>
    obtain ⟨body, operation, found, fetched, stepped⟩ := actual
    have same : body = sourceBody := Option.some.inj (found.symm.trans sourceFound)
    subst body
    obtain ⟨middle, action, extension, targetStepped, actions⟩ := methods.step_success transport
      memory frames sourceFormed targetFormed statics argumentValues stackValues stepped
    cases actions with
    | returned renamed =>
      have contract := step_contract _ _ _ _ _ _ _ _ stepped
      have live : ValuesValid updated raw := contract.values sourceFormed stackValues
      have departed := renamed.leaveFrame _ _ (frames.owned.extend extension)
      have bounds : ∀ value ∈ raw, value.Below updated.nextIdentity :=
        live.below (contract.effect.wellFormed sourceFormed)
      rw [← renamed.sourceLimit] at bounds
      have checks := departed.checkedValues _ bounds
      rw [checked] at checks
      obtain ⟨result, targetChecked, equal⟩ := checks.success
      subst result
      refine ⟨middle, scopes, _, extension, fun _ _ scope => scope, departed, ?_⟩
      simp only [run, targetFound, methods.instruction fetched, targetStepped, targetChecked,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | @call fuel method pc arguments sourceFrame stack source callee childArguments rest updated
      child childFrame childMemory returned result final values actual childFound entered
      childFinished childTrace following childInduction induction =>
    obtain ⟨body, operation, found, fetched, stepped⟩ := actual
    have same : body = sourceBody := Option.some.inj (found.symm.trans sourceFound)
    subst body
    obtain ⟨middle, action, extension, targetStepped, actions⟩ := methods.step_success transport
      memory frames sourceFormed targetFormed statics argumentValues stackValues stepped
    cases actions with
    | @call _ targetUpdated _ _ _ renamed =>
      have contract := step_contract _ _ _ _ _ _ _ _ stepped
      have sourceReady : updated.WellFormed := contract.effect.wellFormed sourceFormed
      have targetReady : targetUpdated.WellFormed :=
        step_preserves_wellFormed _ _ _ _ _ _ _ _ targetFormed targetStepped
      have live : ValuesValid updated childArguments ∧ ValuesValid updated rest :=
        contract.values sourceFormed stackValues
      have updatedStatics := contract.effect.staticBindingsBounded statics
      obtain ⟨targetChild, targetChildFound, ⟨childMethods⟩⟩ := programs _ _ childFound
      obtain ⟨entryMap, sourceChildFrame, targetChildFrame, sourceChildMemory,
        targetChildMemory, entryExtension, sourceEntry, targetEntry, childMemoryRelated,
        childFrames⟩ := renamed.enterFrameInitialized sourceReady targetReady
          (by rw [renamed.sourceLimit]; exact updatedStatics)
          childMethods.sourceReady childMethods.targetReady childMethods.indices
          childMethods.declarations childArguments (childArguments.map middle.value) entered
      have same := Except.ok.inj (sourceEntry.symm.trans entered)
      cases same
      have childBounds : ∀ value ∈ childArguments, value.Below middle.sourceLimit := by
        rw [renamed.sourceLimit]
        exact live.1.below sourceReady
      have enteredSourceReady :=
        enterFrame_preserves_wellFormed _ _ _ _ _ sourceReady entered
      have enteredTargetReady :=
        enterFrame_preserves_wellFormed _ _ _ _ _ targetReady targetEntry
      have childRenamed := childInduction childFound targetChildFound childMethods
        childMemoryRelated childFrames enteredSourceReady enteredTargetReady
        (enterFrame_staticBindingsBounded updatedStatics entered)
        (live.1.preserve sourceReady (enterFrame_fresh _ _ _ _ _ entered).1)
        (by intro value member; cases member)
      obtain ⟨later, after, targetReturned, childExtension, childScopes, returnedMemory,
        targetFinished⟩ := childRenamed
      simp only [List.map_nil] at targetFinished
      rw [entryExtension.values childArguments childBounds] at targetFinished
      have callerAllocations := entered_run_preserves_caller_allocations
        _ _ _ _ _ _ _ _ _ _ entered childFinished
      have returnedSourceReady :=
        run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ enteredSourceReady childFinished
      have returnedTargetReady :=
        run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ enteredTargetReady targetFinished
      have middleExtension := entryExtension.trans childExtension
      have fullExtension := extension.trans middleExtension
      have scopeExtension : ∀ left right, scopes left right → after left right :=
        fun left right scope => childScopes left right (Or.inl scope)
      have continued := induction sourceFound targetFound methods returnedMemory
        (frames.extend fullExtension scopeExtension) returnedSourceReady returnedTargetReady
        (run_staticBindingsBounded
          (enterFrame_staticBindingsBounded updatedStatics entered) childFinished)
        ((argumentValues.preserve sourceFormed contract.effect.allocations).preserve
          sourceReady callerAllocations)
        ((run_result_valid _ _ _ _ _ _ _ _ _ _ childFinished).append
          (live.2.preserve sourceReady callerAllocations))
      have argumentBounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit := by
        rw [memory.sourceLimit]
        exact argumentValues.below sourceFormed
      have restBounds : ∀ value ∈ rest, value.Below middle.sourceLimit := by
        rw [renamed.sourceLimit]
        exact live.2.below sourceReady
      simp only [run, targetFound, methods.instruction fetched, targetStepped,
        targetChildFound, targetEntry, targetFinished, Except.mapError, Bind.bind, Except.bind]
      rw [← fullExtension.values arguments argumentBounds,
        ← middleExtension.values rest restBounds, ← List.map_append]
      exact continued.prepend fullExtension scopeExtension
  | @construct fuel method pc arguments sourceFrame stack source callee childArguments rest
      nextFrame temporary kind updated child childFrame childMemory returned value final values
      actual childFound entered childFinished childTrace loaded following
      childInduction induction =>
    obtain ⟨body, operation, found, fetched, stepped⟩ := actual
    have same : body = sourceBody := Option.some.inj (found.symm.trans sourceFound)
    subst body
    obtain ⟨middle, action, extension, targetStepped, actions⟩ := methods.step_success transport
      memory frames sourceFormed targetFormed statics argumentValues stackValues stepped
    cases actions with
    | @construct _ targetUpdated _ targetNextFrame _ _ _ _ _ renamed nextFrames temporaryBound =>
      have contract := step_contract _ _ _ _ _ _ _ _ stepped
      have sourceReady : updated.WellFormed := contract.effect.wellFormed sourceFormed
      have targetReady : targetUpdated.WellFormed :=
        step_preserves_wellFormed _ _ _ _ _ _ _ _ targetFormed targetStepped
      have live : ValuesValid updated childArguments ∧ ValuesValid updated rest :=
        contract.values sourceFormed stackValues
      have updatedStatics := contract.effect.staticBindingsBounded statics
      obtain ⟨targetChild, targetChildFound, ⟨childMethods⟩⟩ := programs _ _ childFound
      obtain ⟨entryMap, sourceChildFrame, targetChildFrame, sourceChildMemory,
        targetChildMemory, entryExtension, sourceEntry, targetEntry, childMemoryRelated,
        childFrames⟩ := renamed.enterFrameInitialized sourceReady targetReady
          (by rw [renamed.sourceLimit]; exact updatedStatics)
          childMethods.sourceReady childMethods.targetReady childMethods.indices
          childMethods.declarations childArguments (childArguments.map middle.value) entered
      have same := Except.ok.inj (sourceEntry.symm.trans entered)
      cases same
      have childBounds : ∀ value ∈ childArguments, value.Below middle.sourceLimit := by
        rw [renamed.sourceLimit]
        exact live.1.below sourceReady
      have enteredSourceReady :=
        enterFrame_preserves_wellFormed _ _ _ _ _ sourceReady entered
      have enteredTargetReady :=
        enterFrame_preserves_wellFormed _ _ _ _ _ targetReady targetEntry
      have childRenamed := childInduction childFound targetChildFound childMethods
        childMemoryRelated childFrames enteredSourceReady enteredTargetReady
        (enterFrame_staticBindingsBounded updatedStatics entered)
        (live.1.preserve sourceReady (enterFrame_fresh _ _ _ _ _ entered).1)
        (by intro value member; cases member)
      obtain ⟨later, after, targetReturned, childExtension, childScopes, returnedMemory,
        targetFinished⟩ := childRenamed
      simp only [List.map_nil] at targetFinished
      rw [entryExtension.values childArguments childBounds] at targetFinished
      have callerAllocations := entered_run_preserves_caller_allocations
        _ _ _ _ _ _ _ _ _ _ entered childFinished
      have returnedSourceReady :=
        run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ enteredSourceReady childFinished
      have returnedTargetReady :=
        run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ enteredTargetReady targetFinished
      have middleExtension := entryExtension.trans childExtension
      have fullExtension := extension.trans middleExtension
      have scopeExtension : ∀ left right, scopes left right → after left right :=
        fun left right scope => childScopes left right (Or.inl scope)
      have temporaryLater : temporary.allocation < later.sourceLimit :=
        Nat.lt_of_lt_of_le temporaryBound middleExtension.source
      have loads := returnedMemory.loadLocal (.bytes kind temporary) temporaryLater
      rw [loaded] at loads
      obtain ⟨targetValue, targetLoaded, valueEqual⟩ := loads.success
      subst targetValue
      change loadLocal targetReturned (.bytes kind (later.reference temporary)) =
        .ok (later.value value) at targetLoaded
      rw [middleExtension.reference temporary temporaryBound] at targetLoaded
      have continued := induction sourceFound targetFound methods returnedMemory
        (nextFrames.extend middleExtension scopeExtension) returnedSourceReady returnedTargetReady
        (run_staticBindingsBounded
          (enterFrame_staticBindingsBounded updatedStatics entered) childFinished)
        ((argumentValues.preserve sourceFormed contract.effect.allocations).preserve
          sourceReady callerAllocations)
        (ValuesValid.cons (loadLocal_result_valid _ _ _ loaded)
          (live.2.preserve sourceReady callerAllocations))
      have argumentBounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit := by
        rw [memory.sourceLimit]
        exact argumentValues.below sourceFormed
      have restBounds : ∀ value ∈ rest, value.Below middle.sourceLimit := by
        rw [renamed.sourceLimit]
        exact live.2.below sourceReady
      simp only [run, targetFound, methods.instruction fetched, targetStepped,
        targetChildFound, targetEntry, targetFinished, List.isEmpty_nil,
        Bool.not_true, Bool.false_eq_true, ite_false, targetLoaded, Except.mapError,
        Bind.bind, Except.bind]
      rw [← fullExtension.values arguments argumentBounds,
        ← middleExtension.values rest restBounds, ← List.map_cons]
      exact continued.prepend fullExtension scopeExtension

#print axioms RunTrace.rename

/-- Successful invocations transport argument checking, frame entry and the complete run. -/
theorem invoke_rename (transport : StepTransport)
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target final : Memory}
    (memory : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (statics : source.StaticBindingsBounded) {fuel method : Nat} {arguments values : List Value}
    (success : invoke sourceProgram fuel method arguments source = .ok (final, values)) :
    SuccessfulRenaming mapping scopes final values
      (invoke targetProgram fuel method (arguments.map mapping.value) target) := by
  obtain ⟨body, checkedArguments, frame, entered, found, checked, entry, finished⟩ :=
    invoke_success_setup success
  obtain ⟨same, argumentValues⟩ := checkedValues_valid _ _ _ checked
  subst checkedArguments
  have bounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit := by
    rw [memory.sourceLimit]
    exact argumentValues.below sourceFormed
  have checks := memory.checkedValues arguments bounds
  rw [checked] at checks
  obtain ⟨targetArguments, targetChecked, checkedEqual⟩ := checks.success
  subst targetArguments
  obtain ⟨targetBody, targetFound, ⟨methods⟩⟩ := programs _ _ found
  obtain ⟨entryMap, sourceFrame, targetFrame, sourceEntered, targetEntered, extension,
    sourceEntry, targetEntry, enteredMemory, enteredFrames⟩ :=
    memory.enterFrameInitialized sourceFormed targetFormed
      (by rw [memory.sourceLimit]; exact statics) methods.sourceReady methods.targetReady
      methods.indices methods.declarations arguments (arguments.map mapping.value) entry
  have same := Except.ok.inj (sourceEntry.symm.trans entry)
  cases same
  have renamed := (run_success_trace _ _ _ _ _ _ _ _ _ _ finished).rename transport programs
    found targetFound methods enteredMemory enteredFrames
    (enterFrame_preserves_wellFormed _ _ _ _ _ sourceFormed entry)
    (enterFrame_preserves_wellFormed _ _ _ _ _ targetFormed targetEntry)
    (enterFrame_staticBindingsBounded statics entry)
    (argumentValues.preserve sourceFormed (enterFrame_fresh _ _ _ _ _ entry).1)
    (by intro value member; cases member)
  simp only [List.map_nil] at renamed
  rw [extension.values arguments bounds] at renamed
  simp only [invoke, targetFound, targetChecked, targetEntry,
    Except.mapError, Bind.bind, Except.bind]
  exact renamed.prepend extension (fun _ _ scope => Or.inl scope)
#print axioms invoke_rename

/-- Whole invocations retain exact caller descriptors while fresh allocation maps grow. -/
theorem invoke_rename_below (transport : StepTransport)
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {watermark : Nat} {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target final : Memory}
    (memory : Memory.RenamedBelow watermark mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (statics : source.StaticBindingsBounded) {fuel method : Nat} {arguments values : List Value}
    (success : invoke sourceProgram fuel method arguments source = .ok (final, values)) :
    ∃ later after targetFinal, mapping.Extends later ∧
      (∀ left right, scopes left right → after left right) ∧
      Memory.RenamedBelow watermark later after final targetFinal ∧
      invoke targetProgram fuel method (arguments.map mapping.value) target =
        .ok (targetFinal, values.map later.value) := by
  obtain ⟨later, after, targetFinal, extension, scopeExtension, renamed, targetSuccess⟩ :=
    invoke_rename transport programs memory.toRenamed sourceFormed targetFormed statics success
  refine ⟨later, after, targetFinal, extension, scopeExtension, ?_, targetSuccess⟩
  refine ⟨renamed, Nat.le_trans memory.sourceBound extension.source,
    Nat.le_trans memory.targetBound extension.target, ?_, ?_⟩
  · intro identity bound
    exact (extension.image identity (Nat.lt_of_lt_of_le bound memory.sourceBound)).trans
      (memory.fixed identity bound)
  · intro identity bound
    have sourceBound : identity < source.nextIdentity := by
      rw [← memory.sourceLimit]
      exact Nat.lt_of_lt_of_le bound memory.sourceBound
    have targetBound : identity < target.nextIdentity := by
      rw [← memory.targetLimit]
      exact Nat.lt_of_lt_of_le bound memory.targetBound
    rw [(invoke_preserves_caller_allocations _ _ _ _ _ _ _ targetSuccess).lookup
        identity targetBound,
      (invoke_preserves_caller_allocations _ _ _ _ _ _ _ success).lookup identity sourceBound,
      memory.descriptors identity bound]
#print axioms invoke_rename_below

/-- A named instruction exception keeps its name and source location under renaming. -/
theorem MethodRenaming.step_throw (transport : StepTransport)
    {sourceBody targetBody : CIL.Method} (methods : MethodRenaming sourceBody targetBody)
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} {sourceFrame targetFrame : Frame}
    (memory : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed methods.indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (statics : source.StaticBindingsBounded) {arguments stack : List Value}
    (argumentValues : ValuesValid source arguments) (stackValues : ValuesValid source stack)
    {operation : CIL.Op} {pc : Nat} {exception : String}
    (stepped : step sourceBody operation pc arguments sourceFrame stack source =
      .error (.thrown exception)) :
    step targetBody (methods.indices.operation operation) pc (arguments.map mapping.value)
      targetFrame (stack.map mapping.value) target = .error (.thrown exception) := by
  obtain ⟨later, _, actions⟩ := transport methods.indices mapping scopes
    sourceBody targetBody operation pc arguments stack sourceFrame targetFrame source target
    methods.metadata memory frames sourceFormed targetFormed
    (by rw [memory.sourceLimit]; exact statics)
    (by rw [memory.sourceLimit]; exact argumentValues.below sourceFormed)
    (by rw [memory.sourceLimit]; exact stackValues.below sourceFormed)
    (by rw [stepped]; trivial)
  rw [stepped] at actions
  exact actions.thrown
#print axioms MethodRenaming.step_throw

/-- Related checked computations propagate a located named exception exactly. -/
theorem ResultRenamed.located_throw {mapping : AllocationRenaming} {relation : α → β → Prop}
    {source : ExecutionResult α} {target : ExecutionResult β}
    (related : ResultRenamed mapping relation source target) {method pc : Nat}
    {fault : LocatedFault} {exception : String}
    (failed : source.mapError (fun fault => ⟨method, pc, fault⟩) = .error fault)
    (thrown : fault.fault = .thrown exception) :
    target.mapError (fun fault => ⟨method, pc, fault⟩) = .error fault := by
  cases related with
  | ok _ => cases failed
  | error reason =>
    cases failed
    dsimp only at thrown
    subst reason
    rfl
#print axioms ResultRenamed.located_throw

/-- Named exceptions transport through all calls and resumed continuations at the same fuel. -/
theorem run_throw_rename (transport : StepTransport)
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {fuel method pc : Nat} {arguments stack : List Value} {sourceFrame : Frame}
    {source : Memory} {fault : LocatedFault} {exception : String}
    (failed : run sourceProgram fuel method pc arguments sourceFrame stack source = .error fault)
    (thrown : fault.fault = .thrown exception)
    {sourceBody targetBody : CIL.Method}
    (sourceFound : sourceProgram[method]? = some sourceBody)
    (targetFound : targetProgram[method]? = some targetBody)
    (methods : MethodRenaming sourceBody targetBody)
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {target : Memory}
    {targetFrame : Frame} (memory : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed methods.indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (statics : source.StaticBindingsBounded)
    (argumentValues : ValuesValid source arguments) (stackValues : ValuesValid source stack) :
    run targetProgram fuel method pc (arguments.map mapping.value) targetFrame
      (stack.map mapping.value) target = .error fault := by
  induction fuel generalizing method pc arguments stack sourceFrame source sourceBody targetBody
      mapping scopes target targetFrame with
  | zero => cases failed; cases thrown
  | succ fuel induction =>
    cases fetched : sourceBody.code[pc]? with
    | none =>
      simp only [run, sourceFound, fetched] at failed
      cases failed
      cases thrown
    | some operation =>
      cases stepped : step sourceBody operation pc arguments sourceFrame stack source with
      | error reason =>
        simp only [run, sourceFound, fetched, stepped, Except.mapError, Bind.bind,
          Except.bind] at failed
        cases failed
        dsimp only at thrown
        subst reason
        have targetStepped := methods.step_throw transport memory frames sourceFormed
          targetFormed statics argumentValues stackValues stepped
        simp only [run, targetFound, methods.instruction fetched, targetStepped,
          Except.mapError, Bind.bind, Except.bind]
      | ok action =>
        obtain ⟨middle, targetAction, extension, targetStepped, actions⟩ :=
          methods.step_success transport memory frames sourceFormed targetFormed statics
            argumentValues stackValues stepped
        have contract := step_contract _ _ _ _ _ _ _ _ stepped
        have sourceReady := contract.effect.wellFormed sourceFormed
        have targetReady := step_preserves_wellFormed _ _ _ _ _ _ _ _ targetFormed targetStepped
        have updatedStatics := contract.effect.staticBindingsBounded statics
        have argumentBounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit := by
          rw [memory.sourceLimit]
          exact argumentValues.below sourceFormed
        simp only [run, sourceFound, fetched, stepped, Except.mapError, Bind.bind,
          Except.bind] at failed
        simp only [run, targetFound, methods.instruction fetched, targetStepped,
          Except.mapError, Bind.bind, Except.bind]
        cases actions with
        | next renamed nextFrames =>
          rw [← extension.values arguments argumentBounds]
          exact induction failed sourceFound targetFound methods renamed nextFrames
            sourceReady targetReady updatedStatics
            (argumentValues.preserve sourceFormed contract.effect.allocations)
            (contract.values sourceFormed stackValues)
        | @returned updated targetUpdated raw renamed =>
          have live := contract.values sourceFormed stackValues
          have departed := renamed.leaveFrame _ _ (frames.owned.extend extension)
          have bounds : ∀ value ∈ raw, value.Below middle.sourceLimit := by
            rw [renamed.sourceLimit]
            exact live.below sourceReady
          have checks := departed.checkedValues _ bounds
          cases checked : raw.mapM (checkedValue (leaveFrame sourceFrame updated)) with
          | ok result => simp only [checked] at failed; cases failed
          | error reason =>
            simp only [checked] at failed
            cases failed
            dsimp only at thrown
            subst reason
            rw [checked] at checks
            simp only []
            rw [checks.thrown]
        | @call updated targetUpdated callee childArguments rest renamed =>
          have live : ValuesValid updated childArguments ∧ ValuesValid updated rest :=
            contract.values sourceFormed stackValues
          cases childFound : sourceProgram[callee]? with
          | none =>
            simp only [childFound] at failed
            cases failed
            cases thrown
          | some child =>
            obtain ⟨targetChild, targetChildFound, ⟨childMethods⟩⟩ := programs _ _ childFound
            obtain ⟨initialFrame, initialMemory, entered⟩ :
                ∃ childFrame childMemory,
                  enterFrame child childArguments updated = .ok (childFrame, childMemory) := by
              cases entry : enterFrame child childArguments updated with
              | ok result => exact ⟨result.1, result.2, rfl⟩
              | error reason =>
                simp only [childFound, entry] at failed
                cases failed
                exact False.elim (enterFrame_not_thrown child childMethods.sourceReady
                  childArguments updated exception
                  (by simpa only [show reason = .thrown exception from thrown] using entry))
            obtain ⟨entryMap, childFrame, targetChildFrame, childMemory, targetChildMemory,
              entryExtension, sourceEntry, targetEntry, childMemoryRelated, childFrames⟩ :=
              renamed.enterFrameInitialized sourceReady targetReady
                (by rw [renamed.sourceLimit]; exact updatedStatics)
                childMethods.sourceReady childMethods.targetReady childMethods.indices
                childMethods.declarations childArguments (childArguments.map middle.value) entered
            have childBounds : ∀ value ∈ childArguments, value.Below middle.sourceLimit := by
              rw [renamed.sourceLimit]
              exact live.1.below sourceReady
            have enteredSourceReady :=
              enterFrame_preserves_wellFormed _ _ _ _ _ sourceReady sourceEntry
            have enteredTargetReady :=
              enterFrame_preserves_wellFormed _ _ _ _ _ targetReady targetEntry
            have enteredStatics := enterFrame_staticBindingsBounded updatedStatics sourceEntry
            have enteredValues :=
              live.1.preserve sourceReady (enterFrame_fresh _ _ _ _ _ sourceEntry).1
            simp only [childFound, sourceEntry] at failed
            simp only [targetChildFound, targetEntry]
            cases childFinished : run sourceProgram fuel callee 0 childArguments
                childFrame [] childMemory with
            | error reason =>
              simp only [childFinished] at failed
              have targetFailed := induction (childFinished.trans failed) childFound
                targetChildFound childMethods childMemoryRelated childFrames
                enteredSourceReady enteredTargetReady enteredStatics enteredValues
                (by intro value member; cases member)
              simp only [List.map_nil] at targetFailed
              rw [entryExtension.values childArguments childBounds] at targetFailed
              rw [targetFailed]
            | ok result =>
              obtain ⟨returned, result⟩ := result
              simp only [childFinished] at failed
              obtain ⟨later, after, targetReturned, childExtension, childScopes,
                returnedMemory, targetFinished⟩ :=
                (run_success_trace _ _ _ _ _ _ _ _ _ _ childFinished).rename transport programs
                  childFound targetChildFound childMethods childMemoryRelated childFrames
                  enteredSourceReady enteredTargetReady enteredStatics enteredValues
                  (by intro value member; cases member)
              simp only [List.map_nil] at targetFinished
              rw [entryExtension.values childArguments childBounds] at targetFinished
              have callerAllocations := entered_run_preserves_caller_allocations
                _ _ _ _ _ _ _ _ _ _ sourceEntry childFinished
              have returnedSourceReady :=
                run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ enteredSourceReady childFinished
              have returnedTargetReady :=
                run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ enteredTargetReady targetFinished
              have middleExtension := entryExtension.trans childExtension
              have fullExtension := extension.trans middleExtension
              have scopeExtension : ∀ left right, scopes left right → after left right :=
                fun left right scope => childScopes left right (Or.inl scope)
              have continued := induction failed sourceFound targetFound methods returnedMemory
                (frames.extend fullExtension scopeExtension) returnedSourceReady returnedTargetReady
                (run_staticBindingsBounded enteredStatics childFinished)
                ((argumentValues.preserve sourceFormed contract.effect.allocations).preserve
                  sourceReady callerAllocations)
                ((run_result_valid _ _ _ _ _ _ _ _ _ _ childFinished).append
                  (live.2.preserve sourceReady callerAllocations))
              have restBounds : ∀ value ∈ rest, value.Below middle.sourceLimit := by
                rw [renamed.sourceLimit]
                exact live.2.below sourceReady
              rw [targetFinished]
              simp only []
              rw [← fullExtension.values arguments argumentBounds,
                ← middleExtension.values rest restBounds, ← List.map_append]
              exact continued
        | @construct updated targetUpdated nextFrame targetNextFrame callee childArguments rest
            temporary kind renamed nextFrames temporaryBound =>
          have live : ValuesValid updated childArguments ∧ ValuesValid updated rest :=
            contract.values sourceFormed stackValues
          cases childFound : sourceProgram[callee]? with
          | none =>
            simp only [childFound] at failed
            cases failed
            cases thrown
          | some child =>
            obtain ⟨targetChild, targetChildFound, ⟨childMethods⟩⟩ := programs _ _ childFound
            obtain ⟨initialFrame, initialMemory, entered⟩ :
                ∃ childFrame childMemory,
                  enterFrame child childArguments updated = .ok (childFrame, childMemory) := by
              cases entry : enterFrame child childArguments updated with
              | ok result => exact ⟨result.1, result.2, rfl⟩
              | error reason =>
                simp only [childFound, entry] at failed
                cases failed
                exact False.elim (enterFrame_not_thrown child childMethods.sourceReady
                  childArguments updated exception
                  (by simpa only [show reason = .thrown exception from thrown] using entry))
            obtain ⟨entryMap, childFrame, targetChildFrame, childMemory, targetChildMemory,
              entryExtension, sourceEntry, targetEntry, childMemoryRelated, childFrames⟩ :=
              renamed.enterFrameInitialized sourceReady targetReady
                (by rw [renamed.sourceLimit]; exact updatedStatics)
                childMethods.sourceReady childMethods.targetReady childMethods.indices
                childMethods.declarations childArguments (childArguments.map middle.value) entered
            have childBounds : ∀ value ∈ childArguments, value.Below middle.sourceLimit := by
              rw [renamed.sourceLimit]
              exact live.1.below sourceReady
            have enteredSourceReady :=
              enterFrame_preserves_wellFormed _ _ _ _ _ sourceReady sourceEntry
            have enteredTargetReady :=
              enterFrame_preserves_wellFormed _ _ _ _ _ targetReady targetEntry
            have enteredStatics := enterFrame_staticBindingsBounded updatedStatics sourceEntry
            have enteredValues :=
              live.1.preserve sourceReady (enterFrame_fresh _ _ _ _ _ sourceEntry).1
            simp only [childFound, sourceEntry] at failed
            simp only [targetChildFound, targetEntry]
            cases childFinished : run sourceProgram fuel callee 0 childArguments
                childFrame [] childMemory with
            | error reason =>
              simp only [childFinished] at failed
              have targetFailed := induction (childFinished.trans failed) childFound
                targetChildFound childMethods childMemoryRelated childFrames
                enteredSourceReady enteredTargetReady enteredStatics enteredValues
                (by intro value member; cases member)
              simp only [List.map_nil] at targetFailed
              rw [entryExtension.values childArguments childBounds] at targetFailed
              rw [targetFailed]
            | ok result =>
              obtain ⟨returned, result⟩ := result
              simp only [childFinished] at failed
              cases result with
              | cons head tail =>
                simp only [List.isEmpty_cons, Bool.not_false, ite_true] at failed
                cases failed
                cases thrown
              | nil =>
                simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false] at failed
                obtain ⟨later, after, targetReturned, childExtension, childScopes,
                  returnedMemory, targetFinished⟩ :=
                  (run_success_trace _ _ _ _ _ _ _ _ _ _ childFinished).rename transport programs
                    childFound targetChildFound childMethods childMemoryRelated childFrames
                    enteredSourceReady enteredTargetReady enteredStatics enteredValues
                    (by intro value member; cases member)
                simp only [List.map_nil] at targetFinished
                rw [entryExtension.values childArguments childBounds] at targetFinished
                have callerAllocations := entered_run_preserves_caller_allocations
                  _ _ _ _ _ _ _ _ _ _ sourceEntry childFinished
                have returnedSourceReady :=
                  run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ enteredSourceReady childFinished
                have returnedTargetReady :=
                  run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ enteredTargetReady targetFinished
                have middleExtension := entryExtension.trans childExtension
                have fullExtension := extension.trans middleExtension
                have scopeExtension : ∀ left right, scopes left right → after left right :=
                  fun left right scope => childScopes left right (Or.inl scope)
                have temporaryLater : temporary.allocation < later.sourceLimit :=
                  Nat.lt_of_lt_of_le temporaryBound middleExtension.source
                have loads := returnedMemory.loadLocal (.bytes kind temporary) temporaryLater
                rw [targetFinished]
                simp only [List.isEmpty_nil, Bool.not_true,
                  Bool.false_eq_true, ite_false]
                cases loaded : loadLocal returned (.bytes kind temporary) with
                | error reason =>
                  simp only [loaded] at failed
                  cases failed
                  dsimp only at thrown
                  subst reason
                  rw [loaded] at loads
                  have targetLoaded := loads.thrown
                  change loadLocal targetReturned (.bytes kind (later.reference temporary)) =
                    .error (.thrown exception) at targetLoaded
                  rw [middleExtension.reference temporary temporaryBound] at targetLoaded
                  rw [targetLoaded]
                | ok value =>
                  simp only [loaded] at failed
                  rw [loaded] at loads
                  obtain ⟨targetValue, targetLoaded, valueEqual⟩ := loads.success
                  subst targetValue
                  change loadLocal targetReturned (.bytes kind (later.reference temporary)) =
                    .ok (later.value value) at targetLoaded
                  rw [middleExtension.reference temporary temporaryBound] at targetLoaded
                  have continued := induction failed sourceFound targetFound methods returnedMemory
                    (nextFrames.extend middleExtension scopeExtension)
                    returnedSourceReady returnedTargetReady
                    (run_staticBindingsBounded enteredStatics childFinished)
                    ((argumentValues.preserve sourceFormed contract.effect.allocations).preserve
                      sourceReady callerAllocations)
                    (ValuesValid.cons (loadLocal_result_valid _ _ _ loaded)
                      (live.2.preserve sourceReady callerAllocations))
                  have restBounds : ∀ value ∈ rest, value.Below middle.sourceLimit := by
                    rw [renamed.sourceLimit]
                    exact live.2.below sourceReady
                  rw [targetLoaded]
                  simp only []
                  rw [← fullExtension.values arguments argumentBounds,
                    ← middleExtension.values rest restBounds, ← List.map_cons]
                  exact continued
#print axioms run_throw_rename

/-- Valid arguments and paired entry transport named invocation exceptions, including nested calls.
    -/
theorem invoke_throw_rename (transport : StepTransport)
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    (memory : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (statics : source.StaticBindingsBounded) {fuel method : Nat} {arguments : List Value}
    (argumentValues : ValuesValid source arguments) {fault : LocatedFault} {exception : String}
    (failed : invoke sourceProgram fuel method arguments source = .error fault)
    (thrown : fault.fault = .thrown exception) :
    invoke targetProgram fuel method (arguments.map mapping.value) target = .error fault := by
  cases found : sourceProgram[method]? with
  | none =>
    simp only [invoke, found] at failed
    cases failed
    cases thrown
  | some body =>
    have checked := checkedValues_of_valid argumentValues
    have bounds : ∀ value ∈ arguments, value.Below mapping.sourceLimit := by
      rw [memory.sourceLimit]
      exact argumentValues.below sourceFormed
    have checks := memory.checkedValues arguments bounds
    rw [checked] at checks
    obtain ⟨targetArguments, targetChecked, checkedEqual⟩ := checks.success
    subst targetArguments
    obtain ⟨targetBody, targetFound, ⟨methods⟩⟩ := programs _ _ found
    obtain ⟨initialFrame, initialMemory, entry⟩ :
        ∃ frame entered, enterFrame body arguments source = .ok (frame, entered) := by
      cases entry : enterFrame body arguments source with
      | ok result => exact ⟨result.1, result.2, rfl⟩
      | error reason =>
        simp only [invoke, found, checked, entry, Except.mapError, Bind.bind, Except.bind] at failed
        cases failed
        exact False.elim (enterFrame_not_thrown body methods.sourceReady arguments source exception
          (by simpa only [show reason = .thrown exception from thrown] using entry))
    obtain ⟨entryMap, sourceFrame, targetFrame, sourceEntered, targetEntered, extension,
      sourceEntry, targetEntry, enteredMemory, enteredFrames⟩ :=
      memory.enterFrameInitialized sourceFormed targetFormed
        (by rw [memory.sourceLimit]; exact statics) methods.sourceReady methods.targetReady
        methods.indices methods.declarations arguments (arguments.map mapping.value) entry
    simp only [invoke, found, checked, sourceEntry, Except.mapError, Bind.bind,
      Except.bind] at failed
    have renamed := run_throw_rename transport programs failed thrown found targetFound methods
      enteredMemory enteredFrames
      (enterFrame_preserves_wellFormed _ _ _ _ _ sourceFormed sourceEntry)
      (enterFrame_preserves_wellFormed _ _ _ _ _ targetFormed targetEntry)
      (enterFrame_staticBindingsBounded statics sourceEntry)
      (argumentValues.preserve sourceFormed (enterFrame_fresh _ _ _ _ _ sourceEntry).1)
      (by intro value member; cases member)
    simp only [List.map_nil] at renamed
    rw [extension.values arguments bounds] at renamed
    simpa only [invoke, targetFound, targetChecked, targetEntry,
      Except.mapError, Bind.bind, Except.bind] using renamed
#print axioms invoke_throw_rename

/-- The initial identity map leaves every caller argument unchanged. -/
theorem AllocationRenaming.identity_value (limit : Nat) (value : Value) :
    (AllocationRenaming.identity limit).value value = value := by
  have managed (reference : ManagedReference) :
      (AllocationRenaming.identity limit).managedReference reference = reference := by
    cases reference <;> rfl
  cases value <;> simp only [AllocationRenaming.value, AllocationRenaming.spanView,
    AllocationRenaming.arrayView, managed]
#print axioms AllocationRenaming.identity_value

/-- The initial identity map leaves a complete caller argument list unchanged. -/
theorem AllocationRenaming.identity_values (limit : Nat) (values : List Value) :
    values.map (AllocationRenaming.identity limit).value = values := by
  induction values with
  | nil => rfl
  | cons value values induction =>
    simp only [List.map_cons, AllocationRenaming.identity_value, induction]
#print axioms AllocationRenaming.identity_values

/-- Scalar outputs are exact and caller memory agrees, despite extra private target allocations. -/
theorem invoke_rename_scalars (transport : StepTransport)
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {initial final : Memory} (formed : initial.WellFormed)
    (statics : initial.StaticBindingsBounded) {fuel method : Nat} {arguments : List Value}
    {values : List CIL.Value}
    (success : invoke sourceProgram fuel method arguments initial =
      .ok (final, values.map Value.scalar)) :
    ∃ targetFinal, invoke targetProgram fuel method arguments initial =
      .ok (targetFinal, values.map Value.scalar) ∧
      MemoryBelow initial.nextIdentity final targetFinal := by
  obtain ⟨later, after, targetFinal, _, _, memory, targetSuccess⟩ :=
    invoke_rename_below transport programs (Memory.RenamedBelow.refl initial Eq)
      formed formed statics success
  rw [AllocationRenaming.identity_values] at targetSuccess
  simp only [List.map_map, Function.comp_def, AllocationRenaming.value] at targetSuccess
  exact ⟨targetFinal, targetSuccess, memory.memoryBelow⟩
#print axioms invoke_rename_scalars

/-- Same-input named exception contracts survive local relocation and private frame allocations. -/
theorem Raises.rename (transport : StepTransport)
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {initial : Memory} (formed : initial.WellFormed) (statics : initial.StaticBindingsBounded)
    {method : Nat} {arguments : List Value} (argumentValues : ValuesValid initial arguments)
    {exception : String} (raised : Raises sourceProgram method arguments initial exception) :
    Raises targetProgram method arguments initial exception := by
  obtain ⟨fuel, fault, failed, thrown⟩ := raised
  have targetFailed := invoke_throw_rename transport programs
    (Memory.Renamed.refl initial Eq) formed formed statics argumentValues failed thrown
  rw [AllocationRenaming.identity_values] at targetFailed
  exact ⟨fuel, fault, targetFailed, thrown⟩
#print axioms Raises.rename

end CIL.Safety
