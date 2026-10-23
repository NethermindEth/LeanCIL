import CIL.Embedding.BaseStep
import CIL.Safety.Execution

/-!
One checked step of a relabeled instruction at a renamed pc produces the relabeled
action, provided the fallthrough pc, profile, return arity and static descriptor agree.
-/

namespace CIL.Embedding

open CIL

/-- A mixed native operation resumes at the relabeled successor. -/
theorem nativeBinaryValues_relabel (r : Nat → Nat) (op : Op) (pc q : Nat) (x y : Value)
    (next : r (pc + 1) = q + 1) (target : Nat) (values : List Value)
    (h : nativeBinaryValues op pc x y = .ok (target, values)) :
    nativeBinaryValues (op.relabel r) q x y = .ok (r target, values) := by
  unfold nativeBinaryValues at h ⊢
  simp only [bind, Except.bind] at h ⊢
  rw [widenNativeOperand_relabel]
  split at h
  rotate_right
  · cases h
  all_goals
    try simp only at h ⊢
    cases op <;> simp only [Op.relabel, nativePureBinary, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h ⊢
    all_goals (split at h <;> (try (cases h; done)))
    all_goals rename_i found
    all_goals first
      | ((try simp only [found])
         simp only [pure, Except.pure] at h ⊢
         cases h
         rw [next]
         done)
      | (have stepped := base_relabel_of_nativePure _ rfl r pc q _ _ _ _ _ (fun _ => next) found
         simp only [Op.relabel] at stepped
         rw [stepped]
         cases h
         rfl)


end CIL.Embedding

namespace CIL.Safety

open CIL.Embedding

/-- Renames the pc an action resumes at; calls, constructions and returns are unchanged. -/
def FrameAction.relabel (r : Nat → Nat) : FrameAction → FrameAction
  | .next target stack frame memory => .next (r target) stack frame memory
  | action => action

/-- What one expected step at `pc` and its actual counterpart at `q` must share. -/
structure StepContext (expected actual : CIL.Method) (r : Nat → Nat) (op : CIL.Op) (pc q : Nat) : Prop where
  profile : actual.profile = expected.profile
  returnsValue : actual.returnsValue = expected.returnsValue
  statics : staticAt actual q = staticAt expected pc
  next : op.continues = true → r (pc + 1) = q + 1

/-- A successful expected step is matched by the relabeled step at the renamed pc. -/
def StepRelabel (op : CIL.Op) : Prop :=
  ∀ (expected actual : CIL.Method) (r : Nat → Nat) (pc q : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (m : Memory) (action : FrameAction),
    StepContext expected actual r op pc q →
    step expected op pc args frame stack m = .ok action →
    step actual (op.relabel r) q args frame stack m = .ok (action.relabel r)

theorem staticInstruction_congr {expected actual : CIL.Method} {pc q : Nat}
    (same : staticAt actual q = staticAt expected pc) (operation : CIL.MemoryOp) (stack : List Value)
    (m : Memory) : staticInstruction actual q operation stack m = staticInstruction expected pc operation stack m := by
  unfold staticAt at same
  cases operation
  case staticAddress bytes | staticValue bytes =>
    simp only [staticInstruction]
    cases h1 : actual.staticSites.find? (fun site => site.1 == q) <;>
      cases h2 : expected.staticSites.find? (fun site => site.1 == pc) <;> simp_all
  case spanCreate | createSpan =>
    unfold staticInstruction
    split <;> first | contradiction | rfl
  all_goals unfold staticInstruction; rfl

/-- The shared tail of `step` for instructions without a dedicated case. -/
theorem fallback_relabel {r : Nat → Nat} {pc q : Nat} {profile : FeatureProfile} {stack : List Value}
    {frame : Frame} {m : Memory} {action : FrameAction} (op : CIL.Op)
    (arity : pureArity (op.relabel r) = pureArity op)
    (base : pureArity op ≠ none → BaseRelabel op)
    (plain : pureArity op = none → ∀ result, instruction op stack m = .ok result →
      instruction (op.relabel r) stack m = .ok result ∧ r (pc + 1) = q + 1)
    (next : op.continues = true → r (pc + 1) = q + 1)
    (h : (match pureArity op with
    | some argc =>
      if stack.length < argc then Except.error ExecutionFault.invalidState
      else do
        let values ← scalars (List.take argc stack)
        match CIL.step op false pc [] 0 values (fun _ => none) profile with
          | some (CIL.Action.next target result _) => do
            let result ← List.mapM (checkedValue m) (List.map Value.scalar result)
            Pure.pure (FrameAction.next target (result ++ List.drop argc stack) frame m)
          | _ => Except.error ExecutionFault.invalidState
    | none => do
      let __x ← instruction op stack m
      Pure.pure (FrameAction.next (pc + 1) __x.snd frame __x.fst)) = Except.ok action) :
    (match pureArity (op.relabel r) with
    | some argc =>
      if stack.length < argc then Except.error ExecutionFault.invalidState
      else do
        let values ← scalars (List.take argc stack)
        match CIL.step (op.relabel r) false q [] 0 values (fun _ => none) profile with
          | some (CIL.Action.next target result _) => do
            let result ← List.mapM (checkedValue m) (List.map Value.scalar result)
            Pure.pure (FrameAction.next target (result ++ List.drop argc stack) frame m)
          | _ => Except.error ExecutionFault.invalidState
    | none => do
      let __x ← instruction (op.relabel r) stack m
      Pure.pure (FrameAction.next (q + 1) __x.snd frame __x.fst)) = Except.ok (action.relabel r) := by
  rw [arity]
  cases hp : pureArity op with
  | none =>
    rw [hp] at h
    simp only [bind, Except.bind] at h ⊢
    cases hi : instruction op stack m with
    | error _ => rw [hi] at h; cases h
    | ok result =>
      rw [hi] at h
      obtain ⟨same, next⟩ := plain hp result hi
      rw [same, ← next]
      cases h
      rfl
  | some argc =>
    rw [hp] at h
    simp only at h ⊢
    split at h
    · cases h
    · rename_i short
      simp only [short, ↓reduceIte]
      simp only [bind, Except.bind] at h ⊢
      cases hs : scalars (List.take argc stack) with
      | error _ => rw [hs] at h; cases h
      | ok values =>
        rw [hs] at h
        simp only at h ⊢
        split at h
        · rename_i target result memory found
          rw [base (by simp [hp]) r pc q values profile target result memory next found]
          simp only at h ⊢
          cases hc : List.mapM (checkedValue m) (List.map Value.scalar result) with
          | error _ => rw [hc] at h; cases h
          | ok checked => rw [hc] at h; cases h; rfl
        · cases h

private theorem observer_ok {observed : Bool} {result : ExecutionResult FrameAction} {action : FrameAction}
    (h : (if observed then .error (.unsupported "Instruction observes unspecified vector bits") else result) = .ok action) :
    observed = false ∧ result = .ok action := by
  cases observed with
  | false => exact ⟨rfl, h⟩
  | true => cases h

private theorem observer_thrown {observed : Bool} {result : ExecutionResult FrameAction} {exception : String}
    (h : (if observed then .error (.unsupported "Instruction observes unspecified vector bits") else result) =
      .error (.thrown exception)) : observed = false ∧ result = .error (.thrown exception) := by
  cases observed with
  | false => exact ⟨rfl, h⟩
  | true => cases h

set_option hygiene false in
macro "step_observers" : tactic => `(tactic| (
  first
  | (obtain ⟨observed, h⟩ := observer_ok h
     simp only [observerCount] at observed h ⊢
     simp only [observed, Bool.false_eq_true, ite_false] at h ⊢)
  | (obtain ⟨observed, h⟩ := observer_thrown h
     simp only [observerCount] at observed h ⊢
     simp only [observed, Bool.false_eq_true, ite_false] at h ⊢)
  | skip))

set_option hygiene false in
/-- Steps an instruction that `step` handles only in its shared tail. -/
macro "step_relabel_fallback" base:term:max plain:term:max : tactic => `(tactic| (
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers
  rw [context.profile]
  refine fallback_relabel (profile := expected.profile) _ rfl ?_ ?_ context.next h
  · exact $base
  · exact $plain))

theorem except_bind_ok {x : Except ε α} {f : α → Except ε β} {y : β} (h : (x >>= f) = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

@[simp] theorem ok_bind_eq (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

set_option hygiene false in
/-- Replays the shared monadic prefix of both steps, then matches the final action. -/
macro "lockstep" : tactic => `(tactic| (
  repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
  cases h
  first
  | rfl
  | (simp only [FrameAction.relabel]; rw [context.next rfl]; rfl)))

set_option hygiene false in
macro "explicit_intro" : tactic => `(tactic| (
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers))

theorem mapError_ok {x : Except ε α} {f : ε → ε'} {a : α} (h : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | error _ => cases h
  | ok _ => cases h; rfl

set_option hygiene false in
macro "stack_cases" : tactic => `(tactic| (
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers
  rcases stack with _ | ⟨v1, _ | ⟨v2, rest⟩⟩ <;> (try cases v1) <;> (try cases v2)
  all_goals dsimp only [CIL.Op.relabel] at h ⊢
  all_goals (try rw [context.profile])))

set_option hygiene false in
macro "fallback_vacuous" : tactic => `(tactic|
  exact fallback_relabel (profile := expected.profile) _ rfl (fun absent => absurd rfl absent)
    (fun _ _ ran => by unfold instruction at ran; dsimp only at ran; split at ran <;> cases ran) context.next h)

set_option hygiene false in
macro "plain_cases" : tactic => `(tactic| (
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers
  (try rw [context.profile])
  (try rw [context.returnsValue])))

set_option hygiene false in
/-- Splits an optional lookup shared by both steps. -/
macro "lookup_lockstep" : tactic => `(tactic| (
  split at h
  · rename_i found
    (try simp only [found])
    lockstep
  · cases h))

theorem step_relabel_nativeBinary (operation : Op) : StepRelabel (.nativeBinary operation) := by
  stack_cases
  all_goals first
    | fallback_vacuous
    | (obtain ⟨⟨target, values⟩, found, h⟩ := except_bind_ok h
       have native := nativeBinaryValues_relabel r operation pc q _ _ (context.next rfl) target values (mapError_ok found)
       simp only [native, Except.mapError, ok_bind_eq] at h ⊢
       lockstep)

theorem step_relabel_divide (signed remainder : Bool) : StepRelabel (.divide signed remainder) := by
  stack_cases
  all_goals first | fallback_vacuous | lockstep

theorem step_relabel_checkedArithmetic (kind : CheckedBinaryKind) (signed : Bool) :
    StepRelabel (.checkedArithmetic kind signed) := by
  stack_cases
  all_goals first | fallback_vacuous | lockstep

theorem step_relabel_checkedConvert (width : Nat) (signed unsignedInput : Bool) :
    StepRelabel (.checkedConvert width signed unsignedInput) := by
  stack_cases
  all_goals first | fallback_vacuous | lockstep

theorem step_relabel_arg (index : Nat) (narrow : Option NarrowKind) : StepRelabel (.arg index narrow) := by
  plain_cases
  cases narrow <;> dsimp only at h ⊢ <;> lookup_lockstep

theorem step_relabel_vectorArg (index : Nat) : StepRelabel (.vectorArg index) := by
  explicit_intro
  lockstep

theorem step_relabel_vectorArgAddr (index : Nat) : StepRelabel (.vectorArgAddr index) := by
  explicit_intro
  lockstep

theorem step_relabel_local (index : Nat) (narrow : Option NarrowKind) : StepRelabel (.local index narrow) := by
  plain_cases
  lookup_lockstep

theorem step_relabel_vectorLocal (index : Nat) : StepRelabel (.vectorLocal index) := by
  plain_cases
  lookup_lockstep

theorem step_relabel_vectorLocalAddr (index : Nat) : StepRelabel (.vectorLocalAddr index) := by
  plain_cases
  lookup_lockstep

theorem step_relabel_setVectorLocal (index : Nat) : StepRelabel (.setVectorLocal index) := by
  stack_cases
  all_goals first | fallback_vacuous | lookup_lockstep

theorem step_relabel_localAddr (index : Nat) : StepRelabel (.localAddr index) := by
  plain_cases
  lookup_lockstep

theorem step_relabel_setLocal (index : Nat) (narrow : Option NarrowKind) : StepRelabel (.setLocal index narrow) := by
  stack_cases
  all_goals first | fallback_vacuous | lookup_lockstep

theorem step_relabel_call (callee argc : Nat) : StepRelabel (.call callee argc) := by
  plain_cases
  by_cases short : stack.length < argc
  · simp [short] at h
  · simp only [short, ↓reduceIte] at h ⊢
    lockstep

theorem step_relabel_newVector256 (callee argc : Nat) : StepRelabel (.newVector256 callee argc) := by
  plain_cases
  by_cases short : stack.length < argc
  · simp [short] at h
  · simp only [short, ↓reduceIte] at h ⊢
    lockstep

theorem step_relabel_newAggregate (callee argc : Nat) (size : Fin (2^64)) :
    StepRelabel (.newAggregate callee argc size) := by
  plain_cases
  by_cases short : (size = 0 || stack.length < argc) = true
  · simp only [short, ↓reduceIte] at h; cases h
  · simp only [short, ↓reduceIte, Bool.false_eq_true] at h ⊢
    lockstep

theorem step_relabel_intrinsic (operation : Intrinsic) (argc : Nat) : StepRelabel (.intrinsic operation argc) := by
  explicit_intro
  rw [context.profile]
  by_cases avail : (!operation.available expected.profile) = true
  · simp [avail] at h
  · simp only [avail, ↓reduceIte, Bool.false_eq_true] at h ⊢
    by_cases short : stack.length < argc
    · simp [short] at h
    · simp only [short, ↓reduceIte] at h ⊢
      lockstep

theorem step_relabel_memory (operation : MemoryOp) : StepRelabel (.memory operation) := by
  plain_cases
  rw [staticInstruction_congr context.statics]
  lockstep

theorem step_relabel_ret (narrow : Option NarrowKind) : StepRelabel (.ret narrow) := by
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers
  cases narrow
  · dsimp only [CIL.Op.relabel] at h ⊢
    rw [context.returnsValue]
    by_cases sized : stack.length = (if expected.returnsValue then 1 else 0)
    · rw [ite_eq_left sized] at h ⊢
      lockstep
    · rw [ite_eq_right sized] at h
      cases h
  · rcases stack with _ | ⟨v, rest⟩
    · dsimp only [CIL.Op.relabel] at h ⊢
      fallback_vacuous
    · cases v with
      | scalar value =>
        cases value <;> cases rest
        all_goals (try dsimp only [CIL.Op.relabel] at h ⊢)
        all_goals (try rw [context.returnsValue])
        all_goals first
          | fallback_vacuous
          | (by_cases returns : expected.returnsValue = true
             · simp only [returns, ↓reduceIte] at h ⊢
               lockstep
             · simp only [returns, ↓reduceIte, Bool.false_eq_true] at h
               cases h)
      | reference reference =>
        cases rest <;> fallback_vacuous
      | span reference length =>
        cases rest <;> fallback_vacuous

theorem step_relabel_unsupported (description : String) : StepRelabel (.unsupported description) := by
  plain_cases
  fallback_vacuous

theorem step_relabel_throw (exception : String) : StepRelabel (.throw exception) := by
  explicit_intro
  cases h

/-- Closes `BaseRelabel op` for a value-only instruction from its shared relabeling lemma. -/
macro "base_relabels" : tactic => `(tactic|
  solve_by_elim [base_relabel_nop, base_relabel_neg, base_relabel_gt, base_relabel_bgt, base_relabel_ble,
    base_relabel_bleu, base_relabel_convI1, base_relabel_convI2, base_relabel_convU2,
    base_relabel_convI8, base_relabel_convI4, base_relabel_convU1, base_relabel_convU4,
    base_relabel_convU8, base_relabel_convU, base_relabel_bnot, base_relabel_add, base_relabel_sub,
    base_relabel_mul, base_relabel_band, base_relabel_bor, base_relabel_bxor, base_relabel_shl,
    base_relabel_shr, base_relabel_shrUn, base_relabel_lt, base_relabel_ltu, base_relabel_gtu,
    base_relabel_eq, base_relabel_branch, base_relabel_switch, base_relabel_brzero,
    base_relabel_brnonzero, base_relabel_bltu, base_relabel_bgeu, base_relabel_bgtu, base_relabel_bge,
    base_relabel_blt, base_relabel_beq, base_relabel_bne, base_relabel_feature])

/-- Every instruction steps in lockstep with its relabeled form. Pure operations
    share the base-step contract; ordinary memory operations share an unchanged
    instruction result. Dedicated dispatcher cases retain their own proofs. -/

theorem step_relabel (op : CIL.Op) : StepRelabel op := by
  cases op
  case nativeBinary operation => exact step_relabel_nativeBinary operation
  case divide signed remainder => exact step_relabel_divide signed remainder
  case checkedArithmetic kind signed => exact step_relabel_checkedArithmetic kind signed
  case checkedConvert width signed unsignedInput => exact step_relabel_checkedConvert width signed unsignedInput
  case arg index narrow => exact step_relabel_arg index narrow
  case vectorArg index => exact step_relabel_vectorArg index
  case vectorArgAddr index => exact step_relabel_vectorArgAddr index
  case «local» index narrow => exact step_relabel_local index narrow
  case vectorLocal index => exact step_relabel_vectorLocal index
  case vectorLocalAddr index => exact step_relabel_vectorLocalAddr index
  case setVectorLocal index => exact step_relabel_setVectorLocal index
  case localAddr index => exact step_relabel_localAddr index
  case setLocal index narrow => exact step_relabel_setLocal index narrow
  case call method argc => exact step_relabel_call method argc
  case newVector256 constructor argc => exact step_relabel_newVector256 constructor argc
  case newAggregate constructor argc size => exact step_relabel_newAggregate constructor argc size
  case intrinsic operation argc => exact step_relabel_intrinsic operation argc
  case memory operation => exact step_relabel_memory operation
  case ret narrow => exact step_relabel_ret narrow
  case throw exception => exact step_relabel_throw exception
  case unsupported description => exact step_relabel_unsupported description
  case nop | neg | gt | bgt | ble | bleu | convI1 | convI2 | convU2 | convI8 | convI4 | convU1 | convU4
    | convU8 | convU | bnot | add | sub | mul | band | bor | bxor | shl | shr | shrUn | lt | ltu | gtu | eq
    | branch | switch | brzero | brnonzero | bltu | bgeu | bgtu | bge | blt | beq | bne | feature =>
    step_relabel_fallback (fun _ => by base_relabels) (fun absent => nomatch absent)
  case loadAggregate | copyObject | storeAggregate | initAggregate | loadScalar | storeScalar | fieldAt
    | fieldAddress | setFieldAt | aggregateFieldAt | setAggregateFieldAt | lane | laneAddress | setLane
    | const32 | const64 | load64 | store64 | dup | pop | skipInit | asRef =>
    step_relabel_fallback (fun absent => absurd rfl absent) (fun _ _ ran => ⟨ran, context.next rfl⟩)

-- Preserve the named specializations for callers of the existing API.
theorem step_relabel_nop : StepRelabel .nop := step_relabel _
theorem step_relabel_neg : StepRelabel .neg := step_relabel _
theorem step_relabel_gt : StepRelabel .gt := step_relabel _
theorem step_relabel_bgt (target : Nat) : StepRelabel (.bgt target) := step_relabel _
theorem step_relabel_ble (target : Nat) : StepRelabel (.ble target) := step_relabel _
theorem step_relabel_bleu (target : Nat) : StepRelabel (.bleu target) := step_relabel _
theorem step_relabel_loadAggregate (size : Nat) : StepRelabel (.loadAggregate size) := step_relabel _
theorem step_relabel_copyObject (size : Nat) : StepRelabel (.copyObject size) := step_relabel _
theorem step_relabel_storeAggregate (size : Nat) : StepRelabel (.storeAggregate size) := step_relabel _
theorem step_relabel_initAggregate (size : Nat) : StepRelabel (.initAggregate size) := step_relabel _
theorem step_relabel_loadScalar (width : Nat) (signed : Bool) : StepRelabel (.loadScalar width signed) := step_relabel _
theorem step_relabel_storeScalar (width : Nat) : StepRelabel (.storeScalar width) := step_relabel _
theorem step_relabel_fieldAt (offset : Nat) (width : Nat) (signed : Bool) : StepRelabel (.fieldAt offset width signed) :=
  step_relabel _

theorem step_relabel_fieldAddress (offset : Nat) : StepRelabel (.fieldAddress offset) := step_relabel _
theorem step_relabel_setFieldAt (offset : Nat) (width : Nat) : StepRelabel (.setFieldAt offset width) := step_relabel _
theorem step_relabel_aggregateFieldAt (offset : Nat) (size : Nat) : StepRelabel (.aggregateFieldAt offset size) :=
  step_relabel _

theorem step_relabel_setAggregateFieldAt (offset : Nat) (size : Nat) : StepRelabel (.setAggregateFieldAt offset size) :=
  step_relabel _

theorem step_relabel_lane (index : Fin 4) : StepRelabel (.lane index) := step_relabel _
theorem step_relabel_laneAddress (index : Fin 4) : StepRelabel (.laneAddress index) := step_relabel _
theorem step_relabel_setLane (index : Fin 4) : StepRelabel (.setLane index) := step_relabel _
theorem step_relabel_const32 (word : W32) : StepRelabel (.const32 word) := step_relabel _
theorem step_relabel_const64 (word : W64) : StepRelabel (.const64 word) := step_relabel _
theorem step_relabel_convI1 : StepRelabel .convI1 := step_relabel _
theorem step_relabel_convI2 : StepRelabel .convI2 := step_relabel _
theorem step_relabel_convU2 : StepRelabel .convU2 := step_relabel _
theorem step_relabel_convI8 : StepRelabel .convI8 := step_relabel _
theorem step_relabel_convI4 : StepRelabel .convI4 := step_relabel _
theorem step_relabel_convU1 : StepRelabel .convU1 := step_relabel _
theorem step_relabel_convU4 : StepRelabel .convU4 := step_relabel _
theorem step_relabel_convU8 : StepRelabel .convU8 := step_relabel _
theorem step_relabel_convU : StepRelabel .convU := step_relabel _
theorem step_relabel_bnot : StepRelabel .bnot := step_relabel _
theorem step_relabel_add : StepRelabel .add := step_relabel _
theorem step_relabel_sub : StepRelabel .sub := step_relabel _
theorem step_relabel_mul : StepRelabel .mul := step_relabel _
theorem step_relabel_band : StepRelabel .band := step_relabel _
theorem step_relabel_bor : StepRelabel .bor := step_relabel _
theorem step_relabel_bxor : StepRelabel .bxor := step_relabel _
theorem step_relabel_shl : StepRelabel .shl := step_relabel _
theorem step_relabel_shr : StepRelabel .shr := step_relabel _
theorem step_relabel_shrUn : StepRelabel .shrUn := step_relabel _
theorem step_relabel_lt : StepRelabel .lt := step_relabel _
theorem step_relabel_ltu : StepRelabel .ltu := step_relabel _
theorem step_relabel_gtu : StepRelabel .gtu := step_relabel _
theorem step_relabel_eq : StepRelabel .eq := step_relabel _
theorem step_relabel_load64 : StepRelabel .load64 := step_relabel _
theorem step_relabel_store64 : StepRelabel .store64 := step_relabel _
theorem step_relabel_dup : StepRelabel .dup := step_relabel _
theorem step_relabel_pop : StepRelabel .pop := step_relabel _
theorem step_relabel_branch (target : Nat) : StepRelabel (.branch target) := step_relabel _
theorem step_relabel_switch (targets : List Nat) : StepRelabel (.switch targets) := step_relabel _
theorem step_relabel_brzero (target : Nat) : StepRelabel (.brzero target) := step_relabel _
theorem step_relabel_brnonzero (target : Nat) : StepRelabel (.brnonzero target) := step_relabel _
theorem step_relabel_bltu (target : Nat) : StepRelabel (.bltu target) := step_relabel _
theorem step_relabel_bgeu (target : Nat) : StepRelabel (.bgeu target) := step_relabel _
theorem step_relabel_bgtu (target : Nat) : StepRelabel (.bgtu target) := step_relabel _
theorem step_relabel_bge (target : Nat) : StepRelabel (.bge target) := step_relabel _
theorem step_relabel_blt (target : Nat) : StepRelabel (.blt target) := step_relabel _
theorem step_relabel_beq (target : Nat) : StepRelabel (.beq target) := step_relabel _
theorem step_relabel_bne (target : Nat) : StepRelabel (.bne target) := step_relabel _
theorem step_relabel_skipInit : StepRelabel .skipInit := step_relabel _
theorem step_relabel_asRef : StepRelabel .asRef := step_relabel _
theorem step_relabel_feature (id : Feature) : StepRelabel (.feature id) := step_relabel _

#print axioms step_relabel

/-- An expected step that throws is matched by the same throw from the relabeled step at the renamed pc. -/
def StepRaise (op : CIL.Op) : Prop :=
  ∀ (expected actual : CIL.Method) (r : Nat → Nat) (pc q : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (m : Memory) (exception : String),
    StepContext expected actual r op pc q →
    step expected op pc args frame stack m = .error (.thrown exception) →
    step actual (op.relabel r) q args frame stack m = .error (.thrown exception)

theorem except_bind_error {x : Except ε α} {f : α → Except ε β} {e : ε} (h : (x >>= f) = .error e) :
    x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x with
  | error _ => cases h; exact Or.inl rfl
  | ok a => exact Or.inr ⟨a, rfl, h⟩

@[simp] theorem error_bind_eq (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl

theorem mapError_arithmetic_ne_thrown {x : Except CIL.ArithmeticFault α} {exception : String} :
    x.mapError ExecutionFault.arithmetic ≠ .error (.thrown exception) := by
  cases x <;> simp [Except.mapError]

/-- The shared tail of `step` throws only from `instruction`, which both steps share. -/
theorem fallback_raise {r : Nat → Nat} {pc q : Nat} {profile : FeatureProfile} {stack : List Value}
    {frame : Frame} {m : Memory} {exception : String} (op : CIL.Op)
    (arity : pureArity (op.relabel r) = pureArity op)
    (base : pureArity op ≠ none → BaseRelabel op)
    (plain : pureArity op = none → instruction op stack m = .error (.thrown exception) →
      instruction (op.relabel r) stack m = .error (.thrown exception))
    (next : op.continues = true → r (pc + 1) = q + 1)
    (h : (match pureArity op with
    | some argc =>
      if stack.length < argc then Except.error ExecutionFault.invalidState
      else do
        let values ← scalars (List.take argc stack)
        match CIL.step op false pc [] 0 values (fun _ => none) profile with
          | some (CIL.Action.next target result _) => do
            let result ← List.mapM (checkedValue m) (List.map Value.scalar result)
            Pure.pure (FrameAction.next target (result ++ List.drop argc stack) frame m)
          | _ => Except.error ExecutionFault.invalidState
    | none => do
      let __x ← instruction op stack m
      Pure.pure (FrameAction.next (pc + 1) __x.snd frame __x.fst)) = Except.error (.thrown exception)) :
    (match pureArity (op.relabel r) with
    | some argc =>
      if stack.length < argc then Except.error ExecutionFault.invalidState
      else do
        let values ← scalars (List.take argc stack)
        match CIL.step (op.relabel r) false q [] 0 values (fun _ => none) profile with
          | some (CIL.Action.next target result _) => do
            let result ← List.mapM (checkedValue m) (List.map Value.scalar result)
            Pure.pure (FrameAction.next target (result ++ List.drop argc stack) frame m)
          | _ => Except.error ExecutionFault.invalidState
    | none => do
      let __x ← instruction (op.relabel r) stack m
      Pure.pure (FrameAction.next (q + 1) __x.snd frame __x.fst)) = Except.error (.thrown exception) := by
  rw [arity]
  cases hp : pureArity op with
  | none =>
    rw [hp] at h
    simp only [bind, Except.bind] at h ⊢
    cases hi : instruction op stack m with
    | error _ =>
      rw [hi] at h
      cases h
      rw [plain hp hi]
    | ok _ => rw [hi] at h; cases h
  | some argc =>
    rw [hp] at h
    simp only at h ⊢
    split at h
    · cases h
    · rename_i short
      simp only [short, ↓reduceIte]
      simp only [bind, Except.bind] at h ⊢
      cases hs : scalars (List.take argc stack) with
      | error _ => rw [hs] at h; cases h; rfl
      | ok values =>
        rw [hs] at h
        simp only at h ⊢
        split at h
        · rename_i target result memory found
          rw [base (by simp [hp]) r pc q values profile target result memory next found]
          simp only at h ⊢
          cases hc : List.mapM (checkedValue m) (List.map Value.scalar result) with
          | error _ => rw [hc] at h; cases h; rfl
          | ok _ => rw [hc] at h; cases h
        · cases h

set_option hygiene false in
/-- Throws from an instruction that `step` handles only in its shared tail. -/
macro "step_raise_fallback" base:term:max plain:term:max : tactic => `(tactic| (
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers
  rw [context.profile]
  refine fallback_raise (profile := expected.profile) _ rfl ?_ ?_ context.next h
  · exact $base
  · exact $plain))

set_option hygiene false in
macro "fallback_raise_vacuous" : tactic => `(tactic|
  exact fallback_raise (profile := expected.profile) _ rfl (fun absent => absurd rfl absent)
    (fun _ ran => by unfold instruction at ran; dsimp only at ran; split at ran <;> cases ran) context.next h)

set_option hygiene false in
/-- Replays the shared monadic prefix of both steps up to the bind that throws. -/
macro "raise_lockstep" : tactic => `(tactic| (
  repeat (rcases except_bind_error h with found | ⟨_, found, h⟩ <;> simp only [found, error_bind_eq, ok_bind_eq])
  first | exact h | cases h))

set_option hygiene false in
/-- Splits an optional lookup shared by both steps before a throw. -/
macro "lookup_raise" : tactic => `(tactic| (
  split at h
  · rename_i found
    (try simp only [found])
    raise_lockstep
  · cases h))

theorem step_raise_nativeBinary (operation : Op) : StepRaise (.nativeBinary operation) := by
  stack_cases
  all_goals first
    | fallback_raise_vacuous
    | (rcases except_bind_error h with found | ⟨⟨target, values⟩, found, h⟩
       · exact absurd found mapError_arithmetic_ne_thrown
       · have native := nativeBinaryValues_relabel r operation pc q _ _ (context.next rfl) target values
           (mapError_ok found)
         simp only [native, Except.mapError, ok_bind_eq] at h ⊢
         raise_lockstep)

theorem step_raise_divide (signed remainder : Bool) : StepRaise (.divide signed remainder) := by
  stack_cases
  all_goals first | fallback_raise_vacuous | raise_lockstep

theorem step_raise_checkedArithmetic (kind : CheckedBinaryKind) (signed : Bool) :
    StepRaise (.checkedArithmetic kind signed) := by
  stack_cases
  all_goals first | fallback_raise_vacuous | raise_lockstep

theorem step_raise_checkedConvert (width : Nat) (signed unsignedInput : Bool) :
    StepRaise (.checkedConvert width signed unsignedInput) := by
  stack_cases
  all_goals first | fallback_raise_vacuous | raise_lockstep

theorem step_raise_call (callee argc : Nat) : StepRaise (.call callee argc) := by
  plain_cases
  by_cases short : stack.length < argc
  · simp [short] at h
  · simp only [short, ↓reduceIte] at h ⊢
    raise_lockstep

theorem step_raise_newVector256 (callee argc : Nat) : StepRaise (.newVector256 callee argc) := by
  plain_cases
  by_cases short : stack.length < argc
  · simp [short] at h
  · simp only [short, ↓reduceIte] at h ⊢
    raise_lockstep

theorem step_raise_newAggregate (callee argc : Nat) (size : Fin (2^64)) :
    StepRaise (.newAggregate callee argc size) := by
  plain_cases
  by_cases short : (size = 0 || stack.length < argc) = true
  · simp only [short, ↓reduceIte] at h; cases h
  · simp only [short, ↓reduceIte, Bool.false_eq_true] at h ⊢
    raise_lockstep

theorem step_raise_intrinsic (operation : Intrinsic) (argc : Nat) : StepRaise (.intrinsic operation argc) := by
  explicit_intro
  rw [context.profile]
  by_cases avail : (!operation.available expected.profile) = true
  · simp [avail] at h
  · simp only [avail, ↓reduceIte, Bool.false_eq_true] at h ⊢
    by_cases short : stack.length < argc
    · simp [short] at h
    · simp only [short, ↓reduceIte] at h ⊢
      raise_lockstep

theorem step_raise_ret (narrow : Option NarrowKind) : StepRaise (.ret narrow) := by
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers
  cases narrow
  · dsimp only [CIL.Op.relabel] at h ⊢
    rw [context.returnsValue]
    by_cases sized : stack.length = (if expected.returnsValue then 1 else 0)
    · rw [ite_eq_left sized] at h ⊢
      raise_lockstep
    · rw [ite_eq_right sized] at h
      cases h
  · rcases stack with _ | ⟨v, rest⟩
    · dsimp only [CIL.Op.relabel] at h ⊢
      fallback_raise_vacuous
    · cases v with
      | scalar value =>
        cases value <;> cases rest
        all_goals (try dsimp only [CIL.Op.relabel] at h ⊢)
        all_goals (try rw [context.returnsValue])
        all_goals first
          | fallback_raise_vacuous
          | (by_cases returns : expected.returnsValue = true
             · simp only [returns, ↓reduceIte] at h ⊢
               raise_lockstep
             · simp only [returns, ↓reduceIte, Bool.false_eq_true] at h
               cases h)
      | reference reference =>
        cases rest <;> fallback_raise_vacuous
      | span reference length =>
        cases rest <;> fallback_raise_vacuous

/-- Only `throw` raises by itself; every other throw comes from a computation both steps share. -/
theorem step_raise (op : CIL.Op) : StepRaise op := by
  cases op
  case nativeBinary operation => exact step_raise_nativeBinary operation
  case divide signed remainder => exact step_raise_divide signed remainder
  case checkedArithmetic kind signed => exact step_raise_checkedArithmetic kind signed
  case checkedConvert width signed unsignedInput => exact step_raise_checkedConvert width signed unsignedInput
  case arg index narrow =>
    plain_cases
    cases narrow <;> dsimp only at h ⊢ <;> lookup_raise
  case vectorArg | vectorArgAddr =>
    explicit_intro
    raise_lockstep
  case «local» | vectorLocal | vectorLocalAddr | localAddr =>
    plain_cases
    lookup_raise
  case setVectorLocal | setLocal =>
    stack_cases
    all_goals first | fallback_raise_vacuous | lookup_raise
  case call callee argc => exact step_raise_call callee argc
  case newVector256 callee argc => exact step_raise_newVector256 callee argc
  case newAggregate callee argc size => exact step_raise_newAggregate callee argc size
  case intrinsic operation argc => exact step_raise_intrinsic operation argc
  case memory operation =>
    plain_cases
    rw [staticInstruction_congr context.statics]
    raise_lockstep
  case ret narrow => exact step_raise_ret narrow
  case throw =>
    explicit_intro
    exact h
  case unsupported =>
    plain_cases
    fallback_raise_vacuous
  case nop | neg | gt | bgt | ble | bleu | convI1 | convI2 | convU2 | convI8 | convI4 | convU1 | convU4
    | convU8 | convU | bnot | add | sub | mul | band | bor | bxor | shl | shr | shrUn | lt | ltu | gtu | eq
    | branch | switch | brzero | brnonzero | bltu | bgeu | bgtu | bge | blt | beq | bne | feature =>
    step_raise_fallback (fun _ => by base_relabels) (fun absent => nomatch absent)
  case loadAggregate | copyObject | storeAggregate | initAggregate | loadScalar | storeScalar | fieldAt
    | fieldAddress | setFieldAt | aggregateFieldAt | setAggregateFieldAt | lane | laneAddress | setLane
    | const32 | const64 | load64 | store64 | dup | pop | skipInit | asRef =>
    step_raise_fallback (fun absent => absurd rfl absent) (fun _ ran => ran)

#print axioms step_raise
end CIL.Safety
