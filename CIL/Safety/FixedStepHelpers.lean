import CIL.Safety.StepTransport
import CIL.Safety.PureStepRenaming
import CIL.Safety.InstructionRenaming

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
    (formed : source.WellFormed) (operation : CIL.Op) (pc : Nat) (profile : CIL.FeatureProfile)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (do
      match pureArity operation with
      | some argc =>
        if stack.length < argc then .error .invalidState else
          let values ← CIL.Safety.scalars (stack.take argc)
          let some (.next destination result _) :=
            CIL.step operation false pc [] 0 values (fun _ => none) profile |
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
              CIL.step operation false pc [] 0 values (fun _ => none) profile |
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
              CIL.step operation false pc [] 0 values (fun _ => none) profile |
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

/-- Nonallocating families separate reference observations, numeric and boundary steps. -/
inductive FixedStepFamily where
  | reference | numeric | boundary | other | excluded

/-- Allocating and relocated-local operations have separate concrete step proofs. -/
def fixedStepFamily : CIL.Op → FixedStepFamily
  | .local .. | .localAddr _ | .setLocal .. | .vectorLocal _ | .vectorLocalAddr _
  | .setVectorLocal _ | .initializeSpanLocal .. | .stackAlloc _ | .newVector256 ..
  | .newAggregate .. | .memory _ => .excluded
  | .sub => .reference
  | .ltu | .gtu | .eq => .reference
  | .bltu _ | .bgeu _ | .bgtu _ | .bleu _ => .reference
  | .brzero _ | .brnonzero _ | .beq _ | .bne _ => .reference
  | .intrinsic .. | .nativeBinary _ | .checkedConvert .. | .checkedArithmetic ..
  | .divide .. => .numeric
  | .arg .. | .vectorArg _ | .vectorArgAddr _ | .call .. | .tailCall ..
  | .throw _ | .ret _ => .boundary
  | _ => .other

/-- The dispatcher rejects a narrow argument whose source value contains unspecified bits. -/
def argumentUnspecified (operation : CIL.Op) (arguments : List Value) : Bool :=
  match operation with
  | .arg position (some _) => (arguments[position]?.map Value.hasUnspecified).getD false
  | _ => false

/-- Allocation renaming cannot change the narrow argument observation. -/
theorem argumentUnspecified_map (mapping : AllocationRenaming)
    (operation : CIL.Op) (arguments : List Value) :
    argumentUnspecified operation (arguments.map mapping.value) =
      argumentUnspecified operation arguments := by
  cases operation <;> try rfl
  rename_i position narrow
  cases narrow <;> simp only [argumentUnspecified, List.getElem?_map, Option.map_map,
    Function.comp_def, mapping.hasUnspecified]
#print axioms argumentUnspecified_map

/-- The finite reference-operation family exposes only the cases that can observe references. -/
inductive ReferenceStepOperation : CIL.Op → Prop where
  | sub : ReferenceStepOperation .sub
  | ltu : ReferenceStepOperation .ltu
  | gtu : ReferenceStepOperation .gtu
  | eq : ReferenceStepOperation .eq
  | bltu (destination : Nat) : ReferenceStepOperation (.bltu destination)
  | bgeu (destination : Nat) : ReferenceStepOperation (.bgeu destination)
  | bgtu (destination : Nat) : ReferenceStepOperation (.bgtu destination)
  | bleu (destination : Nat) : ReferenceStepOperation (.bleu destination)
  | brzero (destination : Nat) : ReferenceStepOperation (.brzero destination)
  | brnonzero (destination : Nat) : ReferenceStepOperation (.brnonzero destination)
  | beq (destination : Nat) : ReferenceStepOperation (.beq destination)
  | bne (destination : Nat) : ReferenceStepOperation (.bne destination)

/-- Reference-family classification supplies its finite case analysis independently of step goals. -/
theorem referenceStepOperation (operation : CIL.Op)
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
             CIL.Op.sub = CIL.Op.sub →
             originalStack = Value.scalar offset :: Value.reference reference :: tail → False :=
           by assumption
         exact excluded _ _ _ rfl rfl)
      | (exfalso
         have excluded : ∀ (offset : CIL.Value) (reference : ManagedReference) (tail : List Value),
             CIL.Op.sub = CIL.Op.sub →
             originalStack = Value.scalar offset :: Value.readOnlyReference reference :: tail →
               False := by assumption
         exact excluded _ _ _ rfl rfl)
))

set_option hygiene false in
/-- Compose fixed-map primitives after selecting one checked dispatcher family. -/
macro "allocation_fixed_step" following:tactic : tactic => `(tactic| (
  unfold CIL.Safety.step at observable ⊢
  change SuccessOrThrow (if (unspecifiedOperands (observerCount operation) stack ||
    argumentUnspecified operation arguments) then _ else _) at observable
  change ResultRenamed mapping _
    (if (unspecifiedOperands (observerCount operation) stack ||
      argumentUnspecified operation arguments) then _ else _)
    (if (unspecifiedOperands (observerCount operation) (stack.map mapping.value) ||
      argumentUnspecified operation (arguments.map mapping.value)) then _ else _)
  rw [mapping.unspecifiedOperands, argumentUnspecified_map]
  by_cases guard : (unspecifiedOperands (observerCount operation) stack ||
    argumentUnspecified operation arguments) = true
  · simp only [guard, ite_true] at observable
    cases observable
  · simp only [guard, Bool.false_eq_true, ite_false] at observable ⊢
    split at observable
    all_goals try solve | cases family
    all_goals try simp only [List.map_cons, AllocationRenaming.value, metadata.profile,
      metadata.returnsValue]
    all_goals try exact (related.stepFallback frames formed operation pc sourceBody.profile
      stack bounds observable)
    case h_72 =>
      first
      | (have boundary : fixedStepFamily operation = .boundary := family
         have noArg : ∀ position, operation = .arg position none → False := by assumption
         have noNarrowArg : ∀ position kind, operation = .arg position (some kind) → False :=
           by assumption
         have noVectorArg : ∀ position, operation = .vectorArg position → False := by assumption
         have noVectorAddress : ∀ position, operation = .vectorArgAddr position → False :=
           by assumption
         have noCall : ∀ callee argc, operation = .call callee argc → False := by assumption
         have noTailCall : ∀ callee argc, operation = .tailCall callee argc → False := by assumption
         have noThrow : ∀ exception, operation = .throw exception → False := by assumption
         have noReturn : operation = .ret none → False := by assumption
         have noArgument : ∀ position narrow, operation = .arg position narrow → False := by
           intro position narrow
           cases narrow
           · exact noArg position
           · exact noNarrowArg position _
         cases operation <;> try cases boundary
         all_goals try exact False.elim (noArgument _ _ rfl)
         all_goals try exact False.elim (noVectorArg _ rfl)
         all_goals try exact False.elim (noVectorAddress _ rfl)
         all_goals try exact False.elim (noCall _ _ rfl)
         all_goals try exact False.elim (noTailCall _ _ rfl)
         all_goals try exact False.elim (noThrow _ rfl)
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
    all_goals ($following:tactic)
))

end CIL.Safety
