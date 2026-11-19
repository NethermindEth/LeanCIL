import CIL.Safety.ExecutionTrace
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.StaticMemoryLemmas
import CIL.Safety.StackAllocationLemmas
import CIL.Safety.ArrayAllocationLemmas
import CIL.Safety.ObjectAllocationLemmas
import CIL.Safety.SpanConstructionLemmas

/-!
# What one checked step may change

`step_contract` classifies every successful checked step by its effect on memory and frame
(`StepEffect`) and shows that it pushes only values valid in the resulting memory. The
memory-preservation lemmas below, from `step_preserves_wellFormed` up to
`invoke_preserves_wellFormed`, are all derived from this one dispatcher proof, so a new
instruction needs a contract here before anything above it can be proved.
-/

namespace CIL.Safety

/-- The memory a step leaves behind, whatever it asks the driver to do next. -/
def FrameAction.memory : FrameAction → Memory
  | .next _ _ _ m | .call _ _ _ m | .tailCall _ _ m
  | .construct _ _ _ _ _ _ m | .returned _ m => m

/-- Calls and returns keep the current frame until the run dispatcher acts;
    ordinary steps and constructor allocation supply their updated frame. -/
def FrameAction.frameAfter (action : FrameAction) (current : Frame) : Frame :=
  match action with
  | .next _ _ frame _ | .construct _ _ _ frame _ _ _ => frame
  | .call _ _ _ _ | .tailCall _ _ _ | .returned _ _ => current

/-- The runtime type of the instance an instruction at `pc` of `body` creates: `newobj` an
    instance of its constructor's owner with the bases an `.object` link at `pc` states, and
    `newarr` of an element the body's layouts give a class reference shape the array type of that
    class; no other instruction, and `newobj` under no `.object` link, creates an instance. -/
def objectSiteType (body : CIL.Method) (pc : Nat) : CIL.Instruction → Option RuntimeType
  | .newobj constructor => match body.linkAt pc with
    | some (.object _ bases _) => some ⟨constructor.owner, bases⟩
    | _ => none
  | .newarr element => match body.elementShape element with
    | .reference element => some (referenceArrayType element)
    | _ => none
  | _ => none

/-- A step's memory and frame changes, with successful primitive operations as
    evidence. Value-stack validity is independent of this effect classification. Only the
    `operation` executed at `site` may create an instance, and only of the type
    `objectSiteType` gives it there. -/
inductive StepEffect (body : CIL.Method) (site : Nat) (operation : CIL.Instruction) (frame : Frame)
    (m : Memory) :
    Frame → Memory → Prop where
  | arrayAllocation {view result} (effect : ArrayAllocationEffect m view result) :
      StepEffect body site operation frame m frame result
  | objectAllocation {type object result} (effect : ObjectAllocationEffect m type object result)
      (created : objectSiteType body site operation = some type) :
      StepEffect body site operation frame m frame result
  | stackAllocation {reference final result}
      (effect : StackAllocationEffect m frame reference final result) :
      StepEffect body site operation frame m final result
  | memory {result} (effect : StaticInstructionEffect body m result) :
      StepEffect body site operation frame m frame result
  | store {index slot final value result}
      (found : frame.locals[index]? = some slot)
      (stored : storeLocal m slot value = .ok (final, result)) :
      StepEffect body site operation frame m { frame with locals := frame.locals.set index final }
        result
  | valueHome {home result r width value}
      (allocated : allocateHome m frame.activation width = .ok (r, home))
      (stored : storeValue home (.address r) value = .ok result) :
      StepEffect body site operation frame m { frame with owned := r.allocation :: frame.owned }
        result
  | localHome {home result r width slot final value}
      (allocated : allocateHome m frame.activation width = .ok (r, home))
      (stored : storeLocal home slot value = .ok (final, result)) :
      StepEffect body site operation frame m { frame with owned := r.allocation :: frame.owned }
        result

theorem StepEffect.wellFormed {body : CIL.Method} {site : Nat} {operation : CIL.Instruction}
    {frame final : Frame}
    {m result : Memory} (effect : StepEffect body site operation frame m final result)
    (hm : m.WellFormed) : result.WellFormed := by
  cases effect with
  | arrayAllocation effect => exact effect.wellFormed hm
  | objectAllocation effect => exact effect.wellFormed hm
  | stackAllocation effect => exact effect.wellFormed hm
  | memory effect => exact effect.wellFormed hm
  | store _ stored => exact storeLocal_preserves_wellFormed _ _ _ _ _ hm stored
  | valueHome allocated stored =>
    exact storeValue_preserves_wellFormed _ _ _ _
      (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocated) stored
  | localHome allocated stored =>
    exact storeLocal_preserves_wellFormed _ _ _ _ _
      (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocated) stored

theorem StepEffect.allocations {body : CIL.Method} {site : Nat} {operation : CIL.Instruction}
    {frame final : Frame}
    {m result : Memory} (effect : StepEffect body site operation frame m final result) :
    AllocationExtension m result := by
  cases effect with
  | arrayAllocation effect => exact effect.allocations
  | objectAllocation effect => exact effect.allocations
  | stackAllocation effect => exact effect.allocations
  | memory effect => exact effect.allocations
  | store _ stored => exact storeLocal_extends_allocations _ _ _ _ _ stored
  | valueHome allocated stored =>
    exact (allocateHome_fresh _ _ _ _ _ allocated).1.trans
      (storeValue_effect _ _ _ _ stored).allocations
  | localHome allocated stored =>
    exact (allocateHome_fresh _ _ _ _ _ allocated).1.trans
      (storeLocal_extends_allocations _ _ _ _ _ stored)

/-- A value loaded from a local is valid in the memory it was loaded from. -/
theorem loadLocal_result_valid (m : Memory) (slot : LocalSlot) (value : Value)
    (h : loadLocal m slot = .ok value) : value.Valid m := by
  unfold loadLocal at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | rfl
      | exact True.intro
      | solve | cases ‹Opaque128Value› <;> rfl
      | solve | exact loadSnapshot_numeric (by assumption)
      | solve | apply formValue_result_valid; assumption
      | solve | apply formValue_readOnly_valid; assumption
      | solve | exact formObject_result_valid (by assumption)
      | solve | exact checkedAt_ok (by assumption)
      | cases h
      | split at h

/-- An argument load pushes a value valid in the memory it was read from, from its home or
    checked from the incoming arguments. -/
theorem loadArgument_result_valid (body : CIL.Method) (index : Nat) (args : List Value)
    (frame : Frame) (m : Memory) (value : Value)
    (h : loadArgument body index args frame m = .ok value) : value.Valid m := by
  unfold loadArgument at h
  split at h <;> try simp only [Bind.bind, Except.bind] at h
  all_goals repeat' first
    | solve | exact (checkedValue_valid _ _ _ h).2
    | solve | exact loadLocal_result_valid _ _ _ h
    | cases h
    | split at h
#print axioms loadArgument_result_valid

/-- A successful argument store writes its home's frame slot, as `stloc` of that slot does. -/
theorem storeArgument_stores {body : CIL.Method} {index : Nat} {value : Value} {frame : Frame}
    {m : Memory} {stored : Frame × Memory}
    (h : storeArgument body index value frame m = .ok stored) :
    ∃ slot home final, frame.locals[slot]? = some home ∧
      storeLocal m home value = .ok (final, stored.2) ∧
      stored.1 = { frame with locals := frame.locals.set slot final } := by
  unfold storeArgument at h
  split at h
  · rename_i slot _
    cases found : frame.locals[slot]? with
    | none => simp only [found] at h; cases h
    | some home =>
      simp only [found, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      cases written : storeLocal m home value with
      | error _ => simp only [written] at h; cases h
      | ok result =>
        simp only [written, Except.ok.injEq] at h
        subst h
        exact ⟨slot, home, result.1, found, by rw [written], rfl⟩
  · cases h
#print axioms storeArgument_stores

theorem localAddress_result_valid (m : Memory) (index : Nat) (slot : LocalSlot) (value : Value)
    (h : localAddress m index slot = .ok value) : value.Valid m := by
  cases slot with
  | root root => cases h
  | readOnlyRoot _ => cases h
  | opaque128 _ => cases h
  | span _ _ _ => cases h; trivial
  | array _ _ => cases h
  | methodPointer _ _ | methodTable _ _ | object _ => cases h
  | bytes kind r => exact formValue_result_valid m (.address r) value h

/-- An argument address is valid in the memory it was taken in, as its home's address is. -/
theorem addressArgument_result_valid (body : CIL.Method) (index : Nat) (frame : Frame)
    (m : Memory) (value : Value) (h : addressArgument body index frame m = .ok value) :
    value.Valid m := by
  unfold addressArgument at h
  split at h
  · split at h
    · exact localAddress_result_valid _ _ _ _ h
    · cases h
  · cases h
#print axioms addressArgument_result_valid

theorem ValuesValid.drop {m : Memory} {values : List Value}
    (valid : ValuesValid m values) (count : Nat) : ValuesValid m (values.drop count) :=
  fun _ member => valid _ (List.mem_of_mem_drop member)

theorem checkedValues_preserved (m result : Memory) (values checked : List Value)
    (hm : m.WellFormed) (ext : AllocationExtension m result)
    (h : values.mapM (checkedValue m) = .ok checked) : ValuesValid result checked :=
  (checkedValues_valid _ _ _ h).2.preserve hm ext

/-- A call argument is a checked value: valid in the memory it was read in, and never a home. -/
theorem callArgument_checked {frame : Frame} {m : Memory} {value result : Value}
    (h : callArgument frame m value = .ok result) : result.Valid m ∧ result.isHome = false := by
  unfold callArgument at h
  cases viewed : spanView frame m value with
  | error _ => simp [viewed, Bind.bind, Except.bind] at h
  | ok projected =>
    simp only [viewed, Bind.bind, Except.bind] at h
    exact ⟨(checkedValue_valid _ _ _ h).2, checkedValue_not_spanHome h⟩

#print axioms callArgument_checked

/-- A call's arguments, read from `frame`, are valid in the memory they were read in. -/
theorem callArguments_valid {frame : Frame} {m : Memory} {values checked : List Value}
    (h : values.mapM (callArgument frame m) = .ok checked) : ValuesValid m checked :=
  mapM_ok_forall (fun _ _ read => (callArgument_checked read).1) h

#print axioms callArguments_valid

/-- A call's arguments, read from `frame`, stay valid as memory only gains allocations. -/
theorem callArguments_preserved (m result : Memory) (frame : Frame) (values checked : List Value)
    (hm : m.WellFormed) (ext : AllocationExtension m result)
    (h : values.mapM (callArgument frame m) = .ok checked) : ValuesValid result checked :=
  (callArguments_valid h).preserve hm ext

#print axioms callArguments_preserved

/-- A call argument has unspecified bits exactly when the value it was read from has them; a
    home stands for a view, which has none. -/
theorem callArgument_hasUnspecified {frame : Frame} {m : Memory} {value result : Value}
    (h : callArgument frame m value = .ok result) :
    result.hasUnspecified = value.hasUnspecified := by
  unfold callArgument at h
  cases viewed : spanView frame m value with
  | error _ => simp [viewed, Bind.bind, Except.bind] at h
  | ok projected =>
    simp only [viewed, Bind.bind, Except.bind] at h
    rw [(checkedValue_valid _ _ _ h).1]
    cases value <;> simp only [spanView, Pure.pure, Except.pure, Except.ok.injEq] at viewed
    all_goals first
      | (subst viewed; rfl)
      | (split at viewed
         · simp only [loadLocal, Bind.bind, Except.bind, Pure.pure, Except.pure] at viewed
           repeat' (first | (cases viewed; rfl) | contradiction | split at viewed)
         · cases viewed)

#print axioms callArgument_hasUnspecified

/-- A call's arguments have unspecified bits exactly when the values they were read from have. -/
theorem callArguments_hasUnspecified {frame : Frame} {m : Memory} :
    ∀ {values checked : List Value}, values.mapM (callArgument frame m) = .ok checked →
      checked.any Value.hasUnspecified = values.any Value.hasUnspecified
  | [], checked, mapped => by cases mapped; rfl
  | value :: rest, checked, mapped => by
    simp only [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure] at mapped
    cases head : callArgument frame m value with
    | error _ => simp [head] at mapped
    | ok produced =>
      cases tail : rest.mapM (callArgument frame m) with
      | error _ => simp [head, tail] at mapped
      | ok others =>
        simp only [head, tail, Except.ok.injEq] at mapped
        subst mapped
        simp only [List.any_cons, callArgument_hasUnspecified head,
          callArguments_hasUnspecified tail]

#print axioms callArguments_hasUnspecified

/-- The view a home stands for is valid where it was read, and every other value is unchanged. -/
theorem spanView_valid {frame : Frame} {m : Memory} {value result : Value}
    (h : spanView frame m value = .ok result) (valid : value.Valid m) : result.Valid m := by
  cases value with
  | spanHome index =>
    simp only [spanView] at h
    split at h
    · exact loadLocal_result_valid _ _ _ h
    · cases h
  | _ => cases h; exact valid

#print axioms spanView_valid

/-- Reading the homes among a stack's top operands keeps every value valid. -/
theorem viewOperands_valid {frame : Frame} {m : Memory} :
    ∀ {count : Nat} {stack operands : List Value},
      viewOperands frame m count stack = .ok operands → ValuesValid m stack →
        ValuesValid m operands
  | 0, _, _, h, valid => by cases h; exact valid
  | _ + 1, [], _, h, _ => by cases h; intro _ member; cases member
  | count + 1, value :: rest, operands, h, valid => by
    simp only [viewOperands, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases viewed : spanView frame m value with
    | error _ => simp [viewed] at h
    | ok produced =>
      cases others : viewOperands frame m count rest with
      | error _ => simp [viewed, others] at h
      | ok tail =>
        simp only [viewed, others, Except.ok.injEq] at h
        subst h
        exact ValuesValid.cons (spanView_valid viewed (valid value (List.mem_cons_self ..)))
          (viewOperands_valid others valid.tail)

#print axioms viewOperands_valid

theorem allocated_store_reference_valid (m home result : Memory) (activation width : Nat)
    (r : Reference) (value : CIL.Value) (hm : m.WellFormed)
    (allocation : allocateHome m activation width = .ok (r, home))
    (store : storeValue home (.address r) value = .ok result) : form result r = .ok r :=
  (storeValue_effect _ _ _ _ store).allocations.preserves_reference
    (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocation) r r
    (allocateHome_reference_valid _ _ _ _ _ allocation)

theorem allocated_storeLocal_reference_valid (m home result : Memory) (activation width : Nat)
    (r : Reference) (slot finalSlot : LocalSlot) (value : Value) (hm : m.WellFormed)
    (allocation : allocateHome m activation width = .ok (r, home))
    (store : storeLocal home slot value = .ok (finalSlot, result)) : form result r = .ok r :=
  (storeLocal_extends_allocations _ _ _ _ _ store).preserves_reference
    (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocation) r r
    (allocateHome_reference_valid _ _ _ _ _ allocation)

/-- Every value the action carries is valid in its memory: the new stack, the returned
    values, or a child's arguments together with the caller stack left behind. -/
def FrameAction.LiveValues (action : FrameAction) : Prop :=
  match action with
  | .next _ values _ memory | .tailCall _ values memory | .returned values memory =>
    ValuesValid memory values
  | .call _ args rest memory | .construct _ args rest _ _ _ memory =>
    ValuesValid memory args ∧ ValuesValid memory rest

/-- One dispatcher proof supplies memory/frame effects and conditional value validity. -/
structure StepContract (body : CIL.Method) (site : Nat) (operation : CIL.Instruction)
    (frame : Frame)
    (stack : List Value) (m : Memory) (action : FrameAction) : Prop where
  effect : StepEffect body site operation frame m (action.frameAfter frame) action.memory
  values : m.WellFormed → ValuesValid m stack → action.LiveValues

theorem StepContract.of_effect {body : CIL.Method} {site : Nat} {operation : CIL.Instruction}
    {frame : Frame}
    {stack : List Value}
    {m : Memory} {action : FrameAction}
    (effect : StepEffect body site operation frame m (action.frameAfter frame) action.memory)
    (preserve : m.WellFormed → AllocationExtension m action.memory →
      ValuesValid action.memory stack → action.LiveValues) :
    StepContract body site operation frame stack m action :=
  ⟨effect, fun hm valid => preserve hm effect.allocations (valid.preserve hm effect.allocations)⟩

/-- A successful argument store has the effect of a local store to the argument's home. -/
theorem StepContract.storeArgument {body : CIL.Method} {site : Nat} {index : Nat} {frame : Frame}
    {value : Value} {rest : List Value} {m : Memory} {stored : Frame × Memory} {pc : Nat}
    (h : storeArgument body index value frame m = .ok stored) :
    StepContract body site (.starg index) frame (value :: rest) m
      (.next pc rest stored.1 stored.2) := by
  obtain ⟨slot, home, final, found, written, same⟩ := storeArgument_stores h
  rw [same]
  refine StepContract.of_effect (.store found written) ?_
  intro _ _ retained
  exact retained.tail
#print axioms StepContract.storeArgument

theorem StepContract.instruction {body : CIL.Method} {site : Nat} {operation : CIL.Instruction}
    {frame : Frame}
    {stack values : List Value}
    {m result : Memory} {pc : Nat} (contract : InstructionContract m result stack values) :
    StepContract body site operation frame stack m (.next pc values frame result) :=
  ⟨.memory (.ordinary contract.effect), contract.values⟩

/-- A step that runs on the stack with its homes read as views has that step's contract. -/
theorem StepContract.viewed {body : CIL.Method} {site : Nat} {operation : CIL.Instruction}
    {frame : Frame} {stack operands : List Value} {m : Memory} {action : FrameAction}
    {count : Nat} (viewed : viewOperands frame m count stack = .ok operands)
    (contract : StepContract body site operation frame operands m action) :
    StepContract body site operation frame stack m action :=
  ⟨contract.effect, fun hm valid => contract.values hm (viewOperands_valid viewed valid)⟩

#print axioms StepContract.viewed

theorem StepContract.staticInstruction {body : CIL.Method} {site : Nat}
    {operation : CIL.Instruction}
    {frame : Frame}
    {stack values : List Value} {m result : Memory} {pc : Nat}
    (contract : StaticInstructionContract body m result stack values) :
    StepContract body site operation frame stack m (.next pc values frame result) :=
  ⟨.memory contract.effect, contract.values⟩

/-- Dynamic allocation supplies a live reference and preserves existing memory. -/
theorem StepContract.stackAllocation {body : CIL.Method} {site : Nat} {operation : CIL.Instruction}
    {frame final : Frame}
    {stack : List Value} {memory result : Memory} {reference : ManagedReference}
    {size pc : Nat} {initLocals : Bool}
    (success : allocateStack memory frame size initLocals = .ok (reference, final, result)) :
    StepContract body site operation frame stack memory
      (.next pc [.reference reference] final result) := by
  have effect := allocateStack_effect success
  refine ⟨.stackAllocation effect, ?_⟩
  intro valid _ value member
  obtain rfl := List.mem_singleton.mp member
  exact effect.reference_valid valid

#print axioms StepContract.stackAllocation

/-- Heap arrays stay live independently of frame-owned storage. -/
theorem StepContract.arrayAllocation {body : CIL.Method} {site : Nat} {operation : CIL.Instruction}
    {frame : Frame}
    {stack : List Value} {memory result : Memory} {view : ArrayView}
    {element : CIL.ArrayElement} {length : CIL.Value} {pc : Nat}
    (success : newArray memory element length = .ok (view, result)) :
    StepContract body site operation frame (.scalar length :: stack) memory
      (.next pc (.array view :: stack) frame result) := by
  have effect := newArray_effect success
  apply StepContract.of_effect (.arrayAllocation effect)
  intro _ _ retained
  exact ValuesValid.cons effect.view_valid retained.tail

#print axioms StepContract.arrayAllocation

/-- `newobj` under an `.object` link hands the constructor a fresh instance of its owner with the
    link's bases ahead of arguments checked before the allocation, and leaves the same instance
    under the caller's remaining stack. -/
theorem StepContract.objectAllocation {body : CIL.Method} {site : Nat} {frame : Frame}
    {stack arguments : List Value} {memory result : Memory} {object : Reference}
    {constructor : CIL.Extraction.MethodRef} {bases : List CIL.Extraction.TypeExpr}
    {size linkedSize index callee argc : Nat}
    (linked : body.linkAt site = some (.object index bases linkedSize))
    (checked : (stack.take argc).reverse.mapM (callArgument frame memory) = .ok arguments)
    (success : allocateObject memory ⟨constructor.owner, bases⟩ size = .ok (object, result)) :
    StepContract body site (.newobj constructor) frame stack memory
      (.call callee (.object (.address object) :: arguments)
        (.object (.address object) :: stack.drop argc) result) := by
  have effect := allocateObject_effect success
  apply StepContract.of_effect (.objectAllocation effect (by simp only [objectSiteType, linked]))
  intro hm extension retained
  exact ⟨ValuesValid.cons effect.object_valid
      (callArguments_preserved _ _ _ _ _ hm extension checked),
    ValuesValid.cons effect.object_valid (retained.drop _)⟩

#print axioms StepContract.objectAllocation

/-- `newarr` pushes a fresh array of the shape the body's layouts give its element: inline
    storage, or an instance of the array type of a class element. -/
theorem StepContract.newarr {body : CIL.Method} {site : Nat} {frame : Frame}
    {stack : List Value} {memory result : Memory} {array : Value}
    {element : CIL.Extraction.TypeExpr} {length : CIL.Value} {pc : Nat}
    (success : allocateElements (body.elementShape element) length memory = .ok (array, result)) :
    StepContract body site (.newarr element) frame (.scalar length :: stack) memory
      (.next pc (array :: stack) frame result) := by
  cases shaped : body.elementShape element with
  | value inline =>
    simp only [shaped, allocateElements, Bind.bind, Except.bind, Pure.pure, Except.pure]
      at success
    split at success
    · cases success
    · rename_i allocated
      cases success
      exact StepContract.arrayAllocation allocated
  | reference classElement =>
    simp only [shaped, allocateElements, Bind.bind, Except.bind, Pure.pure, Except.pure]
      at success
    split at success
    · cases success
    · rename_i allocated
      cases success
      obtain ⟨size, created⟩ := newReferenceArray_allocation allocated
      have effect := allocateObject_effect created
      apply StepContract.of_effect (.objectAllocation effect
        (by simp only [objectSiteType, shaped]))
      intro _ _ retained
      exact ValuesValid.cons effect.object_valid retained.tail
  | method signature => simp [shaped, allocateElements] at success
  | unsupported reason => simp [shaped, allocateElements] at success

#print axioms StepContract.newarr

/-- A successful pointer subtraction forms a valid result without changing its capability. -/
theorem referenceSubtract_valid (memory : Memory) (reference result : ManagedReference)
    (offset : CIL.Value) (success : referenceSubtract memory reference offset = .ok result) :
    (Value.reference result).Valid memory ∧ (Value.readOnlyReference result).Valid memory := by
  simp only [referenceSubtract] at success
  split at success
  · exact displaceReference_valid success
  · cases success
#print axioms referenceSubtract_valid
/-- Constructing a view and storing it changes only the destination local. -/
theorem StepContract.initializeSpanLocal {body : CIL.Method} {site : Nat}
    {operation : CIL.Instruction}
    {frame : Frame}
    {stack rest : List Value} {memory result : Memory} {construction : Memory × List Value}
    {index pc : Nat} {slot final : LocalSlot} {value : Value}
    {constructor : CIL.SpanConstructor}
    (found : frame.locals[index]? = some slot)
    (constructed : memoryInstruction constructor.operation stack memory =
      .ok construction)
    (values : construction.2 = value :: rest)
    (stored : storeLocal construction.1 slot value = .ok (final, result)) :
    StepContract body site operation frame stack memory
      (.next pc rest { frame with locals := frame.locals.set index final } result) := by
  obtain ⟨constructedMemory, constructedValues⟩ := construction
  dsimp only at values stored
  subst constructedValues
  obtain ⟨same, _⟩ := spanConstructor_result constructor memory constructedMemory stack
    value rest constructed
  subst constructedMemory
  refine ⟨.store found stored, ?_⟩
  intro formed valid
  exact ((memoryInstruction_contract _ _ _ _ _ constructed).values formed valid).tail.preserve
    formed (storeLocal_extends_allocations _ _ _ _ _ stored)

#print axioms StepContract.initializeSpanLocal

/-- Managed identities change no memory; dispatched arguments are checked before use. -/
theorem managedStep_contract {dispatched : CIL.Instruction} (body : CIL.Method)
    (operation : CIL.ManagedOp) (link : Option CIL.Link) (pc : Nat)
    (frame : Frame) (stack : List Value) (memory : Memory) (action : FrameAction)
    (executed : managedStep operation link pc frame stack memory = .ok action) :
    StepContract body pc dispatched frame stack memory action := by
  unfold managedStep at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | solve |
      cases executed
      refine ⟨.memory (.ordinary (.unchanged _)), ?_⟩
      intro formed retained
      repeat' first
        | exact retained
        | exact retained.tail
        | exact retained.tail.tail
        | exact retained.tail.drop _
        | exact callArguments_valid (by assumption)
        | (apply ValuesValid.cons; first | trivial | exact retained | exact retained.tail.tail)
        | constructor
    | cases executed
    | split at executed
#print axioms managedStep_contract

/-- An instance field load that succeeds preserves checked effects and stack validity. -/
theorem fieldLoad_contract (body : CIL.Method) (field : CIL.Extraction.FieldRef)
    (stack values : List Value) (memory result : Memory)
    (executed : fieldLoad body field stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold fieldLoad at executed
  split at executed
  · exact classFieldLoad_contract _ _ _ _ _ _ _ executed
  · exact instruction_contract _ _ _ _ _ executed
  · exact instruction_contract _ _ _ _ _ executed
  · cases executed
#print axioms fieldLoad_contract

/-- An instance field store that succeeds preserves checked effects and stack validity. -/
theorem fieldStore_contract (body : CIL.Method) (field : CIL.Extraction.FieldRef)
    (stack values : List Value) (memory result : Memory)
    (executed : fieldStore body field stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold fieldStore at executed
  split at executed
  · exact classFieldStore_contract _ _ _ _ _ _ _ executed
  · exact instruction_contract _ _ _ _ _ executed
  · exact instruction_contract _ _ _ _ _ executed
  · cases executed
#print axioms fieldStore_contract

/-- An instance field address that succeeds preserves checked effects and stack validity. -/
theorem fieldReference_contract (body : CIL.Method) (field : CIL.Extraction.FieldRef)
    (stack values : List Value) (memory result : Memory)
    (executed : fieldReference body field stack memory = .ok (result, values)) :
    InstructionContract memory result stack values := by
  unfold fieldReference at executed
  split at executed
  · exact instruction_contract _ _ _ _ _ executed
  · exact instruction_contract _ _ _ _ _ executed
  · cases executed
  · cases executed
#print axioms fieldReference_contract

/-- A runtime model preserves the caller's frame and has the checked effect of its operation. -/
theorem modelStep_contract {body : CIL.Method} {model : Option CIL.RuntimeModel}
    {pc : Nat} {frame : Frame} {stack : List Value} {memory : Memory} {action : FrameAction}
    {operation : CIL.Instruction}
    (executed : modelStep model body pc frame stack memory = .ok action) :
    StepContract body pc operation frame stack memory action := by
  unfold modelStep observedCall runModel intrinsicCall featureCall referenceCompareCall
    referenceSubtractCall typedTransferCall skipInitCall at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first | split at executed | cases executed
  all_goals first
    | exact StepContract.instruction (memoryInstruction_contract _ _ _ _ _ (by assumption))
    | exact StepContract.instruction (instruction_contract _ _ _ _ _ (by assumption))
    | exact StepContract.viewed (by assumption)
        (StepContract.instruction (memoryInstruction_contract _ _ _ _ _ (by assumption)))
    | refine StepContract.of_effect (.memory (.ordinary (.unchanged _))) ?_
  all_goals
    intro formed extended retained
    first
    | exact retained.tail
    | apply ValuesValid.cons
      · first
        | trivial
        | exact (checkedValue_valid _ _ _ (by assumption)).2
        | exact (referenceSubtract_valid _ _ _ _ (by assumption)).1
        | exact (referenceSubtract_valid _ _ _ _ (by assumption)).2
      · first | exact retained | exact retained.tail.tail | exact retained.drop _

#print axioms modelStep_contract

-- The walk splits every arm of both dispatcher matches, argument homes included.
set_option maxHeartbeats 400000 in
/-- Every successful checked step has a `StepContract`. The proof walks every dispatcher arm,
    so it is the place that breaks when an instruction is added without an effect. -/
theorem step_contract (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (h : step body operation pc args frame stack m = .ok action) :
    StepContract body pc operation frame stack m action := by
  unfold step intrinsicCall referenceCompareCall referenceSubtractCall newobjStep
    constructAggregate constructObject observedCall initializeSpanHome at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals repeat' first
    | solve | exact modelStep_contract (by assumption)
    | solve | apply managedStep_contract; assumption
    | solve | exact StepContract.storeArgument (by assumption)
    | unfold returnFrom at h
    | unfold localAllocation at h
    | unfold initializeSpanHome at h
    | unfold intrinsicCall at h
    | unfold referenceCompareCall at h
    | unfold referenceSubtractCall at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    | solve |
        apply StepContract.initializeSpanLocal
        all_goals assumption
    | solve | exact .stackAllocation (by assumption)
    | solve | exact .arrayAllocation (by assumption)
    | solve | exact .newarr (by assumption)
    | solve | exact .objectAllocation (by assumption) (by assumption) (by assumption)
    | solve |
        apply StepContract.viewed (by assumption)
        apply StepContract.staticInstruction
        apply staticInstruction_contract
        assumption
    | solve |
        apply StepContract.staticInstruction
        first
          | (apply staticLoad_contract; assumption)
          | (apply staticAddress_contract; assumption)
    | solve |
        apply StepContract.instruction
        apply instruction_contract
        assumption
    | solve |
        apply StepContract.viewed (by assumption)
        apply StepContract.instruction
        apply memoryInstruction_contract
        assumption
    | solve |
        apply StepContract.instruction
        apply referenceAddInstruction_contract
        assumption
    | solve |
        apply StepContract.instruction
        apply typedElementInstruction_contract
        assumption
    | solve |
        apply StepContract.instruction
        apply elementAddressInstruction_contract
        assumption
    | solve |
        apply StepContract.instruction
        first
          | (apply copyInitializedBytes_contract; assumption)
          | (apply initializeBytes_contract; assumption)
          | (apply transferObject_contract; assumption)
          | (apply fieldLoad_contract; assumption)
          | (apply fieldStore_contract; assumption)
          | (apply fieldReference_contract; assumption)
    | solve |
        apply StepContract.viewed (by assumption)
        apply StepContract.instruction
        apply transferObject_contract
        assumption
    | solve |
        refine StepContract.of_effect ?_ ?_
        · first
          | exact .memory (.ordinary (.unchanged _))
          | exact .store (by assumption) (by assumption)
          | exact .valueHome (by assumption) (by assumption)
          | exact .localHome (by assumption) (by assumption)
        · intro hm ext retained
          repeat' first
            | exact retained
            | solve |
                simp only [FrameAction.LiveValues, ValuesValid, Value.Valid, numericValue,
                  List.mem_cons, List.mem_nil, forall_eq_or_imp, false_implies, forall_const,
                  and_true, true_and]
            | exact retained.tail
            | exact retained.tail.tail
            | solve | exact retained.drop _
            | solve | apply checkedValues_preserved _ _ _ _ hm ext; assumption
            | solve | apply callArguments_preserved _ _ _ _ _ hm ext; assumption
            | solve |
                apply ValuesValid.append
                · apply checkedValues_preserved _ _ _ _ hm ext; assumption
                · first | exact retained.drop _ | exact retained.tail.tail
            | solve |
                apply ValuesValid.cons
                · first
                  | rfl
                  | trivial
                  | exact (checkedValue_valid _ _ _ (by assumption)).2
                  | exact objectTest_valid (by assumption)
                  | exact (referenceSubtract_valid _ _ _ _ (by assumption)).1
                  | exact (referenceSubtract_valid _ _ _ _ (by assumption)).2
                  | apply loadLocal_result_valid; assumption
                  | apply loadArgument_result_valid; assumption
                  | apply addressArgument_result_valid; assumption
                  | apply localAddress_result_valid; assumption
                  | apply allocated_store_reference_valid; exact hm; assumption; assumption
                  | apply allocated_storeLocal_reference_valid; exact hm; assumption; assumption
                · first
                  | exact retained
                  | exact retained.drop _
                  | exact retained.tail.tail
                  | exact retained.tail
                  | apply checkedValues_preserved _ _ _ _ hm ext; assumption
                  | apply callArguments_preserved _ _ _ _ _ hm ext; assumption
            | constructor
    | cases h
    | split at h

#print axioms step_contract

/-- No value `action` hands to another frame is a home: the arguments of a call, tail call or
    construction and the returned values. A `.next` keeps its stack in the same frame. -/
def FrameAction.HomeFree : FrameAction → Prop
  | .next .. => True
  | .call _ arguments _ _ | .tailCall _ arguments _ | .construct _ arguments _ _ _ _ _
  | .returned arguments _ => ∀ value ∈ arguments, value.isHome = false

/-- Call arguments read from a frame contain no home. -/
theorem callArguments_not_spanHome {frame : Frame} {m : Memory} {values checked : List Value}
    (h : values.mapM (callArgument frame m) = .ok checked) :
    ∀ value ∈ checked, value.isHome = false :=
  mapM_ok_forall (fun _ _ read => (callArgument_checked read).2) h

#print axioms callArguments_not_spanHome

/-- Closes the home-freedom of an action built from checked lists and fixed values. -/
local macro "home_free_close" : tactic => `(tactic| (
  dsimp only [FrameAction.HomeFree]
  all_goals first
    | trivial
    | exact callArguments_not_spanHome (by assumption)
    | exact checkedValues_not_spanHome (by assumption)
    | exact List.forall_mem_cons.2 ⟨rfl, callArguments_not_spanHome (by assumption)⟩
    | exact List.forall_mem_cons.2 ⟨rfl, fun _ member => nomatch member⟩))


/-- A managed pointer call hands its callee checked arguments, none of them a home. -/
theorem managedStep_homeFree {operation : CIL.ManagedOp} {link : Option CIL.Link} {pc : Nat}
    {frame : Frame} {stack : List Value} {memory : Memory} {action : FrameAction}
    (executed : managedStep operation link pc frame stack memory = .ok action) :
    action.HomeFree := by
  unfold managedStep at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | (cases executed; home_free_close; done)
    | (cases executed; done)
    | split at executed

#print axioms managedStep_homeFree

/-- No successful step hands a home to another frame, so a home never leaves the frame whose
    slot it names. -/
theorem step_homeFree {body : CIL.Method} {operation : CIL.Instruction} {pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body operation pc args frame stack m = .ok action) : action.HomeFree := by
  unfold step intrinsicCall referenceCompareCall referenceSubtractCall newobjStep
    constructAggregate constructObject modelStep observedCall runModel featureCall
    typedTransferCall skipInitCall initializeSpanHome at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals repeat' first
    | (cases h; home_free_close; done)
    | (cases h; done)
    | exact managedStep_homeFree h
    | unfold returnFrom at h
    | unfold localAllocation at h
    | unfold initializeSpanHome at h
    | unfold intrinsicCall at h
    | unfold referenceCompareCall at h
    | unfold referenceSubtractCall at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    | split at h

#print axioms step_homeFree

/-- A list holding an element that `apply` refuses is refused by `mapM`. -/
theorem mapM_error_of_mem {α β ε : Type} {apply : α → Except ε β} {value : α} {fault : ε}
    (refused : apply value = .error fault) :
    ∀ {values : List α}, value ∈ values → ∃ fault, values.mapM apply = .error fault
  | head :: rest, member => by
    rw [List.mapM_cons]
    cases headResult : apply head with
    | error other => exact ⟨other, by simp only [Bind.bind, Except.bind]⟩
    | ok result =>
      cases member with
      | head => rw [refused] at headResult; cases headResult
      | tail _ inRest =>
        obtain ⟨other, failed⟩ := mapM_error_of_mem refused inRest
        exact ⟨other, by simp only [failed, Bind.bind, Except.bind]⟩

#print axioms mapM_error_of_mem

/-- A home among the entry arguments stops `invokeWith` before any frame starts, so no frame
    begins holding a home that names a slot of a frame that does not exist. -/
theorem invokeWith_spanHome (lookup : Nat → Option CIL.Method) (fuel method : Nat)
    {args : List Value} {m : Memory} {slot : Nat} (forged : Value.spanHome slot ∈ args) :
    ∃ fault, invokeWith lookup fuel method args m = .error ⟨method, 0, fault⟩ := by
  obtain ⟨fault, refused⟩ := mapM_error_of_mem (apply := checkedValue m) rfl forged
  unfold invokeWith
  cases lookup method with
  | none => exact ⟨.invalidState, rfl⟩
  | some body =>
    exact ⟨fault, by simp only [refused, Except.mapError, Bind.bind, Except.bind]⟩

#print axioms invokeWith_spanHome

theorem step_effect (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (h : step body operation pc args frame stack m = .ok action) :
    StepEffect body pc operation frame m (action.frameAfter frame) action.memory :=
  (step_contract _ _ _ _ _ _ _ _ h).effect

theorem step_preserves_wellFormed (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed)
    (h : step body operation pc args frame stack m = .ok action) : action.memory.WellFormed := by
  exact (step_effect _ _ _ _ _ _ _ _ h).wellFormed hm

#print axioms step_preserves_wellFormed

theorem programStep_preserves_wellFormed (program : CIL.Program) (method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction)
    (hm : m.WellFormed) (hs : ProgramStep program method pc args frame stack m action) :
    action.memory.WellFormed := by
  obtain ⟨body, op, _, _, hs⟩ := hs
  exact step_preserves_wellFormed _ _ _ _ _ _ _ _ hm hs

/-- A successful run, including all nested calls and frame teardowns, ends in well-formed
    memory. -/
theorem run_preserves_wellFormed (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value) (hm : m.WellFormed)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    final.WellFormed := by
  have trace := run_success_trace program fuel method pc args frame stack m final values h
  clear h
  induction trace with
  | next step _ ih =>
    exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
  | returned step _ =>
    exact leaveFrame_preserves_wellFormed _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
  | tailCall step _ _ _ _ enter _ _ ih =>
    exact ih (enterFrame_preserves_wellFormed _ _ _ _ _
      (leaveFrame_preserves_wellFormed _ _
        (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)) enter)
  | call step _ enter _ _ _ childIH ih
  | construct step _ enter _ _ _ _ childIH ih =>
    exact ih (childIH (enterFrame_preserves_wellFormed _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter))

#print axioms run_preserves_wellFormed

theorem invoke_preserves_wellFormed (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory) (hm : m.WellFormed)
    (h : invoke program fuel method args m = .ok (final, values)) : final.WellFormed := by
  obtain ⟨_, _, _, _, _, _, setup, executed⟩ := invoke_success_setup h
  exact run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _
    (enterFrame_preserves_wellFormed _ _ _ _ _ hm setup) executed

#print axioms invoke_preserves_wellFormed

end CIL.Safety
