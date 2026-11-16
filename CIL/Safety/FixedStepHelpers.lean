import CIL.Safety.StepTransport
import CIL.Safety.PureStepRenaming
import CIL.Safety.InstructionRenaming
import CIL.Safety.NativeMethodTableRenaming

/-!+# Fixed-allocation checked steps

Reference observations and numeric computations preserve the current allocation correspondence.
Fresh allocation instructions are handled separately by the extending step simulation.
-/

namespace CIL.Safety

/-- The ordinary dispatcher tail preserves corresponding frames and checked result stacks. -/
theorem Memory.Renamed.stepFallback {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory} {sourceFrame targetFrame : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (operation : CIL.Instruction) (pc : Nat)
    (profile : CIL.FeatureProfile)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (do
      match pureArity operation with
      | some argc =>
        if stack.length < argc then .error .invalidState else
          let values ← CIL.Safety.scalars (stack.take argc)
          let some (.next destination result _) :=
            CIL.step operation false none pc values (fun _ => none) profile |
              .error .invalidState
          let result ← (result.map Value.scalar).mapM (CIL.Safety.checkedValue source)
          return FrameAction.next destination (result ++ stack.drop argc) sourceFrame source
      | none =>
        let (memory, values) ← CIL.Safety.instruction operation stack source
        return FrameAction.next (pc + 1) values sourceFrame memory)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (do
        match pureArity operation with
        | some argc =>
          if stack.length < argc then .error .invalidState else
            let values ← CIL.Safety.scalars (stack.take argc)
            let some (.next destination result _) :=
              CIL.step operation false none pc values (fun _ => none) profile |
                .error .invalidState
            let result ← (result.map Value.scalar).mapM (CIL.Safety.checkedValue source)
            return FrameAction.next destination (result ++ stack.drop argc) sourceFrame source
        | none =>
          let (memory, values) ← CIL.Safety.instruction operation stack source
          return FrameAction.next (pc + 1) values sourceFrame memory)
      (do
        match pureArity operation with
        | some argc =>
          if (stack.map mapping.value).length < argc then .error .invalidState else
            let values ← CIL.Safety.scalars ((stack.map mapping.value).take argc)
            let some (.next destination result _) :=
              CIL.step operation false none pc values (fun _ => none) profile |
                .error .invalidState
            let result ← (result.map Value.scalar).mapM (CIL.Safety.checkedValue target)
            return FrameAction.next destination (result ++ (stack.map mapping.value).drop argc)
              targetFrame target
        | none =>
          let (memory, values) ← CIL.Safety.instruction operation (stack.map mapping.value) target
          return FrameAction.next (pc + 1) values targetFrame memory) := by
  cases arity : pureArity operation with
  | none =>
    simp only [arity] at observable ⊢
    apply (related.instructionResult operation formed stack bounds observable.bind_left).bind
    intro first second same
    rcases first with ⟨memory, values⟩
    rcases second with ⟨otherMemory, otherValues⟩
    rcases same with ⟨memories, rfl⟩
    exact .ok (.next memories frames)
  | some argc =>
    simp only [arity, List.length_map, ← List.map_take, ← List.map_drop]
    split
    · exact .error .invalidState
    · apply (mapping.scalarOperands (stack.take argc)).bind
      intro values otherValues same
      subst otherValues
      split
      · rename_i destination result ignored _
        apply (related.scalarChecks result).bind
        intro checked otherChecked same
        subst otherChecked
        simpa only [List.map_append, pure, Except.pure] using
          ResultRenamed.ok (FrameAction.Renamed.next (pc := destination)
            (stack := checked ++ stack.drop argc) related frames)
      · exact .error .invalidState
#print axioms Memory.Renamed.stepFallback

/-- An observable native table addition selects the same cursor in the renamed memory: renaming
    keeps the table's stable binding identity and resolves it to the renamed allocation. -/
theorem Memory.Renamed.nativeTableAddition {indices : LocalIndexMap}
    {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop} {source target : Memory}
    {sourceFrame targetFrame : Frame} (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (formed : source.WellFormed) (pc : Nat) (offset : CIL.Value) (table : CIL.MethodTable)
    (rest : List Value)
    (observable : SuccessOrThrow (do
      let offset ← match offset with
        | .i32 bits => .ok (bits.signExtend 64)
        | .i64 bits => .ok bits
        | _ => .error .invalidState
      let selected ← checkedAt .null nativeMethodWidth (addNativeTable table source offset)
      return FrameAction.next (pc + 1) (.methodTable selected :: rest) sourceFrame source)) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (do
        let offset ← match offset with
          | .i32 bits => .ok (bits.signExtend 64)
          | .i64 bits => .ok bits
          | _ => .error .invalidState
        let selected ← checkedAt .null nativeMethodWidth (addNativeTable table source offset)
        return FrameAction.next (pc + 1) (.methodTable selected :: rest) sourceFrame source)
      (do
        let offset ← match offset with
          | .i32 bits => .ok (bits.signExtend 64)
          | .i64 bits => .ok bits
          | _ => .error .invalidState
        let selected ← checkedAt .null nativeMethodWidth (addNativeTable table target offset)
        return FrameAction.next (pc + 1) (.methodTable selected :: rest.map mapping.value)
          targetFrame target) := by
  cases offset
  all_goals simp only [Bind.bind, Except.bind] at observable ⊢
  all_goals try exact .error _
  all_goals
    apply checkedNative_bind _ _ _ _
      (fun value proof => related.addNativeTable_success formed _ value _ proof) observable
    intro value found observable
    exact .ok (.next related frames)
#print axioms Memory.Renamed.nativeTableAddition

/-- Nonallocating families separate reference observations, numeric and boundary steps. -/
inductive FixedStepFamily where
  | reference | numeric | boundary | other | excluded

/-- Allocating and relocated-local operations have separate concrete step proofs. -/
def fixedStepFamily : CIL.Instruction → FixedStepFamily
  | .ldloc .. | .ldloca _ | .stloc .. | .initializeSpanLocal .. | .localloc | .newarr _
  | .newAggregate .. | .newObject .. | .memory _ | .ldfld _ | .ldflda _ | .stfld _ => .excluded
  | .add | .sub => .reference
  | .clt_un | .cgt_un | .ceq => .reference
  | .blt_un _ | .bge_un _ | .bgt_un _ | .ble_un _ => .reference
  | .brfalse _ | .brtrue _ | .beq _ | .bne_un _ => .reference
  | .intrinsic .. | .conv_ovf _ | .conv_ovf_un _ | .div | .div_un | .rem
  | .rem_un | .add_ovf | .add_ovf_un | .sub_ovf | .sub_ovf_un | .mul_ovf | .mul_ovf_un => .numeric
  | .managed _ | .ldarg _ | .starg _ | .ldarga _ | .call .. | .callInstance .. | .callVirtual ..
  | .castclass _ | .isinst _ | .tailCall ..
  | .throw _ | .ret => .boundary
  | _ => .other

/-- The finite reference-operation family exposes only the cases that can observe references. -/
inductive ReferenceStepOperation : CIL.Instruction → Prop where
  | add : ReferenceStepOperation .add
  | sub : ReferenceStepOperation .sub
  | clt_un : ReferenceStepOperation .clt_un
  | cgt_un : ReferenceStepOperation .cgt_un
  | ceq : ReferenceStepOperation .ceq
  | blt_un (destination : Nat) : ReferenceStepOperation (.blt_un destination)
  | bge_un (destination : Nat) : ReferenceStepOperation (.bge_un destination)
  | bgt_un (destination : Nat) : ReferenceStepOperation (.bgt_un destination)
  | ble_un (destination : Nat) : ReferenceStepOperation (.ble_un destination)
  | brfalse (destination : Nat) : ReferenceStepOperation (.brfalse destination)
  | brtrue (destination : Nat) : ReferenceStepOperation (.brtrue destination)
  | beq (destination : Nat) : ReferenceStepOperation (.beq destination)
  | bne_un (destination : Nat) : ReferenceStepOperation (.bne_un destination)

/-- Reference-family classification supplies its finite case analysis independently of step goals. -/
theorem referenceStepOperation (operation : CIL.Instruction)
    (family : fixedStepFamily operation = .reference) : ReferenceStepOperation operation := by
  cases operation <;> try cases family
  all_goals constructor
#print axioms referenceStepOperation

set_option hygiene false in
/-- Resolve dispatcher fallback patterns without unfolding the checked fallback computation. -/
macro "fixed_fallback" : tactic => `(tactic| (
  let originalStack := stack
  have fallback := related.stepFallback frames formed operation pc sourceBody.profile
    stack bounds observable
  try rw [metadata.profile]
  first
  | (have referenceCases := referenceStepOperation operation family
     cases referenceCases)
  | (cases operation <;> try cases family)
  -- A hole has its own faulting arm, so the fallback arm excludes it.
  all_goals try exact False.elim (unadmitted _ rfl)
  all_goals try exact fallback
  all_goals cases stack with
  | nil =>
    try dsimp only [List.map_nil]
    exact fallback
  | cons first rest =>
    cases first
    all_goals try dsimp only [List.map_cons, AllocationRenaming.value]
    all_goals try exact fallback
    all_goals cases rest with
    | nil =>
      try dsimp only [List.map_nil, List.map_cons, AllocationRenaming.value]
      first
      | contradiction
      | exact fallback
    | cons second rest =>
      cases second
      all_goals try dsimp only [List.map_nil, List.map_cons, AllocationRenaming.value]
      all_goals first
      | contradiction
      | exact fallback
      | (exfalso
         have excluded : ∀ (offset : CIL.Value) (reference : ManagedReference) (tail : List Value),
             CIL.Instruction.add = CIL.Instruction.add →
             originalStack = Value.scalar offset :: Value.reference reference :: tail → False :=
           by assumption
         exact excluded _ _ _ rfl rfl)
      | (exfalso
         have excluded : ∀ (reference : ManagedReference) (offset : CIL.Value) (tail : List Value),
             CIL.Instruction.add = CIL.Instruction.add →
             originalStack = Value.reference reference :: Value.scalar offset :: tail → False :=
           by assumption
         exact excluded _ _ _ rfl rfl)
      | (exfalso
         have excluded : ∀ (offset : CIL.Value) (reference : ManagedReference) (tail : List Value),
             CIL.Instruction.add = CIL.Instruction.add →
             originalStack =
               Value.scalar offset :: Value.readOnlyReference reference :: tail → False :=
           by assumption
         exact excluded _ _ _ rfl rfl)
      | (exfalso
         have excluded : ∀ (reference : ManagedReference) (offset : CIL.Value) (tail : List Value),
             CIL.Instruction.add = CIL.Instruction.add →
             originalStack =
               Value.readOnlyReference reference :: Value.scalar offset :: tail → False :=
           by assumption
         exact excluded _ _ _ rfl rfl)
      | (exfalso
         have excluded : ∀ (offset : CIL.Value) (table : CIL.MethodTable) (tail : List Value),
             CIL.Instruction.add = CIL.Instruction.add →
             originalStack = Value.scalar offset :: Value.methodTable table :: tail → False :=
           by assumption
         exact excluded _ _ _ rfl rfl)
      | (exfalso
         have excluded : ∀ (table : CIL.MethodTable) (offset : CIL.Value) (tail : List Value),
             CIL.Instruction.add = CIL.Instruction.add →
             originalStack = Value.methodTable table :: Value.scalar offset :: tail → False :=
           by assumption
         exact excluded _ _ _ rfl rfl)
      | (exfalso
         have excluded : ∀ (offset : CIL.Value) (reference : ManagedReference) (tail : List Value),
             CIL.Instruction.sub = CIL.Instruction.sub →
             originalStack = Value.scalar offset :: Value.reference reference :: tail → False :=
           by assumption
         exact excluded _ _ _ rfl rfl)
      | (exfalso
         have excluded : ∀ (offset : CIL.Value) (reference : ManagedReference) (tail : List Value),
             CIL.Instruction.sub = CIL.Instruction.sub →
             originalStack = Value.scalar offset :: Value.readOnlyReference reference :: tail →
               False := by assumption
         exact excluded _ _ _ rfl rfl)
))

set_option hygiene false in
/-- Compose fixed-map primitives after selecting one checked dispatcher family. -/
macro "allocation_fixed_step" following:tactic : tactic => `(tactic| (
  unfold CIL.Safety.step intrinsicCall referenceCompareCall referenceSubtractCall at observable ⊢
  change SuccessOrThrow (if unspecifiedOperands (observerCount operation) stack then _ else _)
    at observable
  change ResultRenamed mapping _
    (if unspecifiedOperands (observerCount operation) stack then _ else _)
    (if unspecifiedOperands (observerCount operation) (stack.map mapping.value) then _ else _)
  rw [mapping.unspecifiedOperands]
  by_cases guard : unspecifiedOperands (observerCount operation) stack = true
  · simp only [guard, ite_true] at observable
    cases observable
  · simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    split at observable
    -- The catch-all's exclusions are named so the arms' own names stay the newest inaccessible
    -- ones; `fixed_fallback` reads the hole and table-offset exclusions, the others are cleared.
    -- `split` states the exclusions of the arms that ignore the stack first.
    all_goals try (
      rename_i addressHome localAllocation unadmitted offsetBeforeTable tableBeforeOffset addOvf
        addOvfUn subOvf subOvfUn mulOvf mulOvfUn div divUn rem remUn convOvf convOvfUn objectsEqual
        objectsBranchEqual objectsBranchUnequal objectAbove objectBranchFalse objectBranchTrue
        castClass isInst storeHome allocatedArray
      guard_hyp addressHome : ∀ (index : Nat), operation = .ldarga index → False
      guard_hyp localAllocation : operation = .localloc → False
      guard_hyp unadmitted : ∀ (opcode : Nat), operation = .unadmitted opcode → False
      guard_hyp storeHome : ∀ (index : Nat) (value : Value) (rest : List Value),
        operation = .starg index → stack = value :: rest → False
      guard_hyp allocatedArray : ∀ (element : CIL.Extraction.TypeExpr) (length : CIL.Value)
        (rest : List Value), operation = .newarr element → stack = Value.scalar length :: rest →
        False
      guard_hyp tableBeforeOffset : ∀ (table : CIL.MethodTable) (offset : CIL.Value)
        (rest : List Value), operation = .add →
        stack = Value.methodTable table :: Value.scalar offset :: rest → False
      guard_hyp div : ∀ (y x : CIL.Value) (rest : List Value), operation = .div →
        stack = Value.scalar y :: Value.scalar x :: rest → False
      guard_hyp objectsEqual : ∀ (right left : ManagedReference) (rest : List Value),
        operation = .ceq → stack = Value.object right :: Value.object left :: rest → False
      guard_hyp isInst : ∀ (type : CIL.Extraction.TypeExpr) (value : ManagedReference)
        (rest : List Value), operation = .isinst type → stack = Value.object value :: rest → False
      clear addOvf addOvfUn subOvf subOvfUn mulOvf mulOvfUn div divUn rem remUn convOvf
        convOvfUn objectsEqual objectsBranchEqual objectsBranchUnequal objectAbove
        objectBranchFalse objectBranchTrue castClass isInst storeHome allocatedArray addressHome
        localAllocation
      split at observable)
    all_goals try solve | cases family
    all_goals try simp only [List.map_cons, AllocationRenaming.value, metadata.profile,
      metadata.returnsValue, metadata.returnNarrow]
    all_goals try exact (related.stepFallback frames formed operation pc sourceBody.profile
      stack bounds observable)
    -- Only the dispatcher's final arm excludes `.managed`, so the guard skips every other arm
    -- and fails if no arm is left to select.
    any_goals
      first
        | (have excludesManaged : ∀ native, operation = .managed native → False := by assumption
           clear excludesManaged)
        | fail "not the dispatcher's fallback arm"
      first
      | (have boundary : fixedStepFamily operation = .boundary := family
         have noManaged : ∀ op, operation = .managed op → False := by assumption
         have noArgument : ∀ position, operation = .ldarg position → False := by assumption
         have noCall : ∀ callee argc, operation = .call callee argc → False := by assumption
         have noTailCall : ∀ callee argc, operation = .tailCall callee argc → False := by assumption
         have noThrow : ∀ exception, operation = .throw exception → False := by assumption
         have noReturn : operation = .ret → False := by assumption
         cases operation <;> try cases boundary
         all_goals try exact False.elim (noManaged _ rfl)
         all_goals try exact False.elim (noArgument _ rfl)
         all_goals try exact False.elim (noCall _ _ rfl)
         all_goals try exact False.elim (noTailCall _ _ rfl)
         all_goals try exact False.elim (noThrow _ rfl)
         all_goals try exact False.elim (noReturn rfl)
         all_goals simp only [pureArity, CIL.Safety.instruction] at observable
         all_goals repeat first | cases observable | split at observable)
      | (have numeric : fixedStepFamily operation = .numeric := family
         have noIntrinsic : ∀ intrinsic argc, operation = .intrinsic intrinsic argc → False :=
           by assumption
         cases operation <;> try cases numeric
         all_goals try exact False.elim (noIntrinsic _ _ rfl)
         all_goals simp only [pureArity, CIL.Safety.instruction] at observable
         all_goals repeat first | cases observable | split at observable)
      | fixed_fallback
    all_goals try solve | repeat first | contradiction | cases observable | split at observable
    all_goals try solve |
      apply (related.referenceAddInstructionResult 1 true _ bounds
        (SuccessOrThrow.bind_left observable)).bind
      intro first second same
      obtain ⟨memory, values⟩ := first
      obtain ⟨otherMemory, otherValues⟩ := second
      obtain ⟨memories, rfl⟩ := same
      exact .ok (.next memories frames)
    all_goals try solve | exact related.nativeTableAddition frames formed _ _ _ _ observable
    all_goals clear observable
    all_goals try simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
    all_goals repeat' rcases bounds with ⟨_, bounds⟩
    all_goals repeat first
      | exact .ok (.next related frames)
      | exact .error _
      | (apply (related.referenceSubtract _ (by assumption) _).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
      | (apply (related.referenceDifference _ _ (by assumption) (by assumption)).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
      | (apply (related.referenceLess _ _ (by assumption) (by assumption)).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
      | (apply (related.referenceEqual _ _ (by assumption) (by assumption)).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
      | (apply (related.referenceNonNull _ (by assumption)).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
      | (apply (related.objectEqual _ _ (by assumption) (by assumption)).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
      | (apply (related.objectNonNull _ (by assumption)).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
      | (apply (related.objectAboveNull _ _ (by assumption)).bind
         intro first second same
         subst second
         exact .ok (.next related frames))
    all_goals ($following:tactic)
))

end CIL.Safety
