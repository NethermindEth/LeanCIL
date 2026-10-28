import CIL.Embedding.BaseStep
import CIL.Safety.Execution

/-!
# Relabeled steps

One checked step of a relabeled instruction at a renamed pc produces the relabeled
action, provided the fallthrough pc, profile, return arity and static descriptor agree.
`step_relabel` covers successful steps and `step_raise` covers thrown exceptions; other
faults are not matched. `Embedding.Simulation` lifts both to whole runs.

The per-instruction lemmas follow the dispatcher in `CIL/Safety/Execution.lean`: value-only
instructions reuse the base-step lemmas of `CIL.Embedding.BaseStep`, and the rest replay
both steps in lockstep with the tactics defined here.
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
    cases op <;> simp only [Op.relabel, nativePureBinary, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq] at h ⊢
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
structure StepContext (expected actual : CIL.Method) (r : Nat → Nat) (op : CIL.Op) (pc q : Nat) :
    Prop where
  profile : actual.profile = expected.profile
  returnsValue : actual.returnsValue = expected.returnsValue
  statics : staticAt actual q = staticAt expected pc
  next : op.continues = true → r (pc + 1) = q + 1

/-- A successful expected step is matched by the relabeled step at the renamed pc. -/
def StepRelabel (op : CIL.Op) : Prop :=
  ∀ (expected actual : CIL.Method) (r : Nat → Nat) (pc q : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction),
    StepContext expected actual r op pc q →
    step expected op pc args frame stack m = .ok action →
    step actual (op.relabel r) q args frame stack m = .ok (action.relabel r)

/-- Static-memory instructions at two pcs that resolve the same descriptor behave alike. -/
theorem staticInstruction_congr {expected actual : CIL.Method} {pc q : Nat}
    (same : staticAt actual q = staticAt expected pc) (operation : CIL.MemoryOp)
    (stack : List Value) (m : Memory) :
    staticInstruction actual q operation stack m =
      staticInstruction expected pc operation stack m := by
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
theorem fallback_relabel {r : Nat → Nat} {pc q : Nat} {profile : FeatureProfile}
    {stack : List Value} {frame : Frame} {m : Memory} {action : FrameAction} (op : CIL.Op)
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
      Pure.pure (FrameAction.next (q + 1) __x.snd frame __x.fst)) =
        Except.ok (action.relabel r) := by
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

/-- A successful step passed the unspecified-bits guard. -/
private theorem observer_ok {observed : Bool} {result : ExecutionResult FrameAction}
    {action : FrameAction}
    (h : (if observed then .error (.unsupported "Instruction observes unspecified vector bits")
      else result) = .ok action) :
    observed = false ∧ result = .ok action := by
  cases observed with
  | false => exact ⟨rfl, h⟩
  | true => cases h

/-- A step that throws passed the unspecified-bits guard. -/
private theorem observer_thrown {observed : Bool} {result : ExecutionResult FrameAction}
    {exception : String}
    (h : (if observed then .error (.unsupported "Instruction observes unspecified vector bits")
      else result) = .error (.thrown exception)) :
    observed = false ∧ result = .error (.thrown exception) := by
  cases observed with
  | false => exact ⟨rfl, h⟩
  | true => cases h

set_option hygiene false in
/-- Discharges the unspecified-bits guard at the head of `step` in `h` and the goal, when
    `h` is a success or a throw; otherwise does nothing. -/
macro "step_observers" : tactic => `(tactic| (
  first
  | (obtain ⟨observed, h⟩ := observer_ok h
     dsimp only [observerCount] at observed h ⊢
     simp only [observed, Bool.false_eq_true, ite_false])
  | (obtain ⟨observed, h⟩ := observer_thrown h
     dsimp only [observerCount] at observed h ⊢
     simp only [observed, Bool.false_eq_true, ite_false])
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

/-- A successful bind succeeded at its first computation. -/
theorem except_bind_ok {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
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
/-- Introduces a `StepRelabel` or `StepRaise` goal, unfolds both steps and clears the guard. -/
macro "explicit_intro" : tactic => `(tactic| (
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers))

theorem mapError_ok {x : Except ε α} {f : ε → ε'} {a : α} (h : x.mapError f = .ok a) :
    x = .ok a := by
  cases x with
  | error _ => cases h
  | ok _ => cases h; rfl

set_option hygiene false in
/-- Splits operand shapes only while needed: unary and invalid-first-operand cases close
    before examining the second operand. -/
local macro "stack_cases" " => " close:tacticSeq : tactic => `(tactic| (
  intro expected actual r pc q args frame stack m action context h
  unfold step at h ⊢
  dsimp only [CIL.Op.relabel] at h ⊢
  step_observers
  rcases stack with _ | ⟨v1, rest⟩ <;> (try cases v1)
  all_goals (try dsimp only [CIL.Op.relabel] at h ⊢)
  all_goals (try rw [context.profile])
  all_goals first
    | (($close); done)
    | (rcases rest with _ | ⟨v2, rest⟩ <;> (try cases v2)
       all_goals (try dsimp only [CIL.Op.relabel] at h ⊢)
       all_goals (try rw [context.profile])
       all_goals ($close))))

set_option hygiene false in
/-- Closes a case that reached the shared tail of `step`, where `instruction` cannot succeed. -/
macro "fallback_vacuous" : tactic => `(tactic|
  exact fallback_relabel (profile := expected.profile) _ rfl (fun absent => absurd rfl absent)
    (fun _ _ ran => by unfold instruction at ran; dsimp only at ran; split at ran <;> cases ran)
    context.next h)

set_option hygiene false in
/-- `explicit_intro`, then rewrites the profile and return arity where they occur. -/
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

-- Instructions with a dedicated case in `step`.

theorem step_relabel_nativeBinary (operation : Op) : StepRelabel (.nativeBinary operation) := by
  stack_cases =>
    first
      | fallback_vacuous
      | (obtain ⟨⟨target, values⟩, found, h⟩ := except_bind_ok h
         have native := nativeBinaryValues_relabel r operation pc q _ _ (context.next rfl) target
           values (mapError_ok found)
         simp only [native, Except.mapError, ok_bind_eq] at h ⊢
         lockstep)

theorem step_relabel_divide (signed remainder : Bool) : StepRelabel (.divide signed remainder) := by
  stack_cases =>
    first | fallback_vacuous | lockstep

theorem step_relabel_checkedArithmetic (kind : CheckedBinaryKind) (signed : Bool) :
    StepRelabel (.checkedArithmetic kind signed) := by
  stack_cases =>
    first | fallback_vacuous | lockstep

theorem step_relabel_checkedConvert (width : Nat) (signed unsignedInput : Bool) :
    StepRelabel (.checkedConvert width signed unsignedInput) := by
  stack_cases =>
    first | fallback_vacuous | lockstep

theorem step_relabel_arg (index : Nat) (narrow : Option NarrowKind) :
    StepRelabel (.arg index narrow) := by
  plain_cases
  cases narrow <;> dsimp only at h ⊢ <;> lookup_lockstep

theorem step_relabel_vectorArg (index : Nat) : StepRelabel (.vectorArg index) := by
  explicit_intro
  lockstep

theorem step_relabel_vectorArgAddr (index : Nat) : StepRelabel (.vectorArgAddr index) := by
  explicit_intro
  lockstep

theorem step_relabel_local (index : Nat) (narrow : Option NarrowKind) :
    StepRelabel (.local index narrow) := by
  plain_cases
  lookup_lockstep

theorem step_relabel_vectorLocal (index : Nat) : StepRelabel (.vectorLocal index) := by
  plain_cases
  lookup_lockstep

theorem step_relabel_vectorLocalAddr (index : Nat) : StepRelabel (.vectorLocalAddr index) := by
  plain_cases
  lookup_lockstep

theorem step_relabel_setVectorLocal (index : Nat) : StepRelabel (.setVectorLocal index) := by
  stack_cases =>
    first | fallback_vacuous | lookup_lockstep

theorem step_relabel_localAddr (index : Nat) : StepRelabel (.localAddr index) := by
  plain_cases
  lookup_lockstep

theorem step_relabel_setLocal (index : Nat) (narrow : Option NarrowKind) :
    StepRelabel (.setLocal index narrow) := by
  stack_cases =>
    first | fallback_vacuous | lookup_lockstep

theorem step_relabel_call (callee argc : Nat) : StepRelabel (.call callee argc) := by
  plain_cases
  by_cases short : stack.length < argc
  · simp [short] at h
  · simp only [short, ↓reduceIte] at h ⊢
    lockstep

theorem step_relabel_newVector256 (callee argc : Nat) :
    StepRelabel (.newVector256 callee argc) := by
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

theorem step_relabel_intrinsic (operation : Intrinsic) (argc : Nat) :
    StepRelabel (.intrinsic operation argc) := by
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
      | bufferSpan _ | readOnlyReference _ | array _ =>
        cases rest <;> fallback_vacuous

theorem step_relabel_unsupported (description : String) :
    StepRelabel (.unsupported description) := by
  plain_cases
  fallback_vacuous

theorem step_relabel_throw (exception : String) : StepRelabel (.throw exception) := by
  explicit_intro
  cases h

open Lean Elab Tactic Meta in
/-- Selects the proved base-step equation for the goal's opcode constructor. -/
elab "base_relabels" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``BaseRelabel 1 do
    throwError "Expected a BaseRelabel goal"
  let operation ← whnfR target.getAppArgs[0]!
  let some constructor := operation.getAppFn.constName? |
    throwError "Expected an opcode constructor"
  let theoremName := `CIL.Embedding ++ Name.mkSimple s!"base_relabel_{constructor.getString!}"
  let goals ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels theoremName)
  unless goals.isEmpty do throwError "The base-step equation left unsolved goals"
  replaceMainGoal []

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_eq : StepRelabel .eq := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_eq

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_brzero (target : Nat) : StepRelabel (.brzero target) := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_brzero

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_brnonzero (target : Nat) : StepRelabel (.brnonzero target) := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_brnonzero

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_beq (target : Nat) : StepRelabel (.beq target) := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_beq

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_bne (target : Nat) : StepRelabel (.bne target) := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_bne

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_sub : StepRelabel .sub := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_sub

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_ltu : StepRelabel .ltu := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_ltu

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_gtu : StepRelabel .gtu := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_gtu

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_bltu (target : Nat) : StepRelabel (.bltu target) := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_bltu

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_bgeu (target : Nat) : StepRelabel (.bgeu target) := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_bgeu

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_bgtu (target : Nat) : StepRelabel (.bgtu target) := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_bgtu

/-- Relabel scalar or reference observations while preserving their result. -/
theorem step_relabel_bleu (target : Nat) : StepRelabel (.bleu target) := by
  stack_cases =>
    first
        | exact fallback_relabel (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | (repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found, ok_bind_eq])
           cases h
           simp only [FrameAction.relabel, apply_ite, context.next rfl, Pure.pure, Except.pure])

#print axioms step_relabel_bleu

/-- Every instruction steps in lockstep with its relabeled form. Pure operations
    share the base-step contract; ordinary memory operations share an unchanged
    instruction result. Dedicated dispatcher cases retain their own proofs. -/
theorem step_relabel (op : CIL.Op) : StepRelabel op := by
  cases op
  case stackAlloc initLocals =>
    stack_cases =>
      first
      | fallback_vacuous
      | (cases ‹CIL.Value›
         all_goals dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h ⊢
         all_goals try cases h
         all_goals repeat (obtain ⟨_, found, h⟩ := except_bind_ok h; simp only [found])
         all_goals cases h
         all_goals simp only [FrameAction.relabel]
         all_goals rw [context.next rfl])
  case nativeBinary operation => exact step_relabel_nativeBinary operation
  case divide signed remainder => exact step_relabel_divide signed remainder
  case checkedArithmetic kind signed => exact step_relabel_checkedArithmetic kind signed
  case checkedConvert width signed unsignedInput =>
    exact step_relabel_checkedConvert width signed unsignedInput
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
  case sub => exact step_relabel_sub
  case ltu => exact step_relabel_ltu
  case gtu => exact step_relabel_gtu
  case bltu target => exact step_relabel_bltu target
  case bgeu target => exact step_relabel_bgeu target
  case bgtu target => exact step_relabel_bgtu target
  case bleu target => exact step_relabel_bleu target
  case eq => exact step_relabel_eq
  case brzero target => exact step_relabel_brzero target
  case brnonzero target => exact step_relabel_brnonzero target
  case beq target => exact step_relabel_beq target
  case bne target => exact step_relabel_bne target
  case nop | neg | gt | bgt | ble | convI1 | convI2 | convU2 | convI8 | convI4 | convU1
    | convU4 | convU8 | convU | bnot | add | mul | band | bor | bxor | shl | shr | shrUn
    | lt | branch | switch | bge | blt | feature =>
    step_relabel_fallback (fun _ => by base_relabels) (fun absent => nomatch absent)
  case loadAggregate | copyObject | storeAggregate | initAggregate | loadScalar | storeScalar
    | fieldAt | fieldAddress | setFieldAt | aggregateFieldAt | setAggregateFieldAt | lane
    | laneAddress | setLane | const32 | const64 | load64 | store64 | dup | pop | skipInit | asRef =>
    step_relabel_fallback (fun absent => absurd rfl absent)
      (fun _ _ ran => ⟨ran, context.next rfl⟩)

-- Preserve the named specializations for callers of the existing API.
theorem step_relabel_nop : StepRelabel .nop := step_relabel _
theorem step_relabel_neg : StepRelabel .neg := step_relabel _
theorem step_relabel_gt : StepRelabel .gt := step_relabel _
theorem step_relabel_bgt (target : Nat) : StepRelabel (.bgt target) := step_relabel _
theorem step_relabel_ble (target : Nat) : StepRelabel (.ble target) := step_relabel _
theorem step_relabel_loadAggregate (size : Nat) : StepRelabel (.loadAggregate size) :=
  step_relabel _
theorem step_relabel_copyObject (size : Nat) : StepRelabel (.copyObject size) := step_relabel _
theorem step_relabel_storeAggregate (size : Nat) : StepRelabel (.storeAggregate size) :=
  step_relabel _
theorem step_relabel_initAggregate (size : Nat) : StepRelabel (.initAggregate size) :=
  step_relabel _
theorem step_relabel_loadScalar (width : Nat) (signed : Bool) :
    StepRelabel (.loadScalar width signed) := step_relabel _
theorem step_relabel_storeScalar (width : Nat) : StepRelabel (.storeScalar width) := step_relabel _
theorem step_relabel_fieldAt (offset : Nat) (width : Nat) (signed : Bool) :
    StepRelabel (.fieldAt offset width signed) := step_relabel _
theorem step_relabel_fieldAddress (offset : Nat) : StepRelabel (.fieldAddress offset) :=
  step_relabel _
theorem step_relabel_setFieldAt (offset : Nat) (width : Nat) :
    StepRelabel (.setFieldAt offset width) := step_relabel _
theorem step_relabel_aggregateFieldAt (offset : Nat) (size : Nat) :
    StepRelabel (.aggregateFieldAt offset size) := step_relabel _
theorem step_relabel_setAggregateFieldAt (offset : Nat) (size : Nat) :
    StepRelabel (.setAggregateFieldAt offset size) := step_relabel _
theorem step_relabel_lane (index : Fin 4) : StepRelabel (.lane index) := step_relabel _
theorem step_relabel_laneAddress (index : Fin 4) : StepRelabel (.laneAddress index) :=
  step_relabel _
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
theorem step_relabel_mul : StepRelabel .mul := step_relabel _
theorem step_relabel_band : StepRelabel .band := step_relabel _
theorem step_relabel_bor : StepRelabel .bor := step_relabel _
theorem step_relabel_bxor : StepRelabel .bxor := step_relabel _
theorem step_relabel_shl : StepRelabel .shl := step_relabel _
theorem step_relabel_shr : StepRelabel .shr := step_relabel _
theorem step_relabel_shrUn : StepRelabel .shrUn := step_relabel _
theorem step_relabel_lt : StepRelabel .lt := step_relabel _
theorem step_relabel_load64 : StepRelabel .load64 := step_relabel _
theorem step_relabel_store64 : StepRelabel .store64 := step_relabel _
theorem step_relabel_dup : StepRelabel .dup := step_relabel _
theorem step_relabel_pop : StepRelabel .pop := step_relabel _
theorem step_relabel_branch (target : Nat) : StepRelabel (.branch target) := step_relabel _
theorem step_relabel_switch (targets : List Nat) : StepRelabel (.switch targets) := step_relabel _
theorem step_relabel_bge (target : Nat) : StepRelabel (.bge target) := step_relabel _
theorem step_relabel_blt (target : Nat) : StepRelabel (.blt target) := step_relabel _
theorem step_relabel_skipInit : StepRelabel .skipInit := step_relabel _
theorem step_relabel_asRef : StepRelabel .asRef := step_relabel _
theorem step_relabel_feature (id : Feature) : StepRelabel (.feature id) := step_relabel _

#print axioms step_relabel

/-- An expected step that throws is matched by the same throw from the relabeled step at the
    renamed pc. -/
def StepRaise (op : CIL.Op) : Prop :=
  ∀ (expected actual : CIL.Method) (r : Nat → Nat) (pc q : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (exception : String),
    StepContext expected actual r op pc q →
    step expected op pc args frame stack m = .error (.thrown exception) →
    step actual (op.relabel r) q args frame stack m = .error (.thrown exception)

/-- A failed bind failed either at its first computation or in its continuation. -/
theorem except_bind_error {x : Except ε α} {f : α → Except ε β} {e : ε}
    (h : (x >>= f) = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x with
  | error _ => cases h; exact Or.inl rfl
  | ok a => exact Or.inr ⟨a, rfl, h⟩

@[simp] theorem error_bind_eq (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

/-- An arithmetic fault is never a thrown exception. -/
theorem mapError_arithmetic_ne_thrown {x : Except CIL.ArithmeticFault α} {exception : String} :
    x.mapError ExecutionFault.arithmetic ≠ .error (.thrown exception) := by
  cases x <;> simp [Except.mapError]

/-- The shared tail of `step` throws only from `instruction`, which both steps share. -/
theorem fallback_raise {r : Nat → Nat} {pc q : Nat} {profile : FeatureProfile}
    {stack : List Value} {frame : Frame} {m : Memory} {exception : String} (op : CIL.Op)
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
      Pure.pure (FrameAction.next (pc + 1) __x.snd frame __x.fst)) =
        Except.error (.thrown exception)) :
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
      Pure.pure (FrameAction.next (q + 1) __x.snd frame __x.fst)) =
        Except.error (.thrown exception) := by
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
/-- Closes a throwing case that reached the shared tail of `step`, where `instruction`
    cannot throw. -/
macro "fallback_raise_vacuous" : tactic => `(tactic|
  exact fallback_raise (profile := expected.profile) _ rfl (fun absent => absurd rfl absent)
    (fun _ ran => by unfold instruction at ran; dsimp only at ran; split at ran <;> cases ran)
    context.next h)

set_option hygiene false in
/-- Replays the shared monadic prefix of both steps up to the bind that throws. -/
macro "raise_lockstep" : tactic => `(tactic| (
  repeat (rcases except_bind_error h with found | ⟨_, found, h⟩ <;> simp only [found,
    error_bind_eq, ok_bind_eq])
  first | exact h | cases h))

set_option hygiene false in
/-- Splits an optional lookup shared by both steps before a throw. -/
macro "lookup_raise" : tactic => `(tactic| (
  split at h
  · rename_i found
    (try simp only [found])
    raise_lockstep
  · cases h))

-- Instructions with a dedicated case in `step`.

theorem step_raise_nativeBinary (operation : Op) : StepRaise (.nativeBinary operation) := by
  stack_cases =>
    first
      | fallback_raise_vacuous
      | (rcases except_bind_error h with found | ⟨⟨target, values⟩, found, h⟩
         · exact absurd found mapError_arithmetic_ne_thrown
         · have native := nativeBinaryValues_relabel r operation pc q _ _ (context.next rfl) target
             values (mapError_ok found)
           simp only [native, Except.mapError, ok_bind_eq] at h ⊢
           raise_lockstep)

theorem step_raise_divide (signed remainder : Bool) : StepRaise (.divide signed remainder) := by
  stack_cases =>
    first | fallback_raise_vacuous | raise_lockstep

theorem step_raise_checkedArithmetic (kind : CheckedBinaryKind) (signed : Bool) :
    StepRaise (.checkedArithmetic kind signed) := by
  stack_cases =>
    first | fallback_raise_vacuous | raise_lockstep

theorem step_raise_checkedConvert (width : Nat) (signed unsignedInput : Bool) :
    StepRaise (.checkedConvert width signed unsignedInput) := by
  stack_cases =>
    first | fallback_raise_vacuous | raise_lockstep

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

theorem step_raise_intrinsic (operation : Intrinsic) (argc : Nat) :
    StepRaise (.intrinsic operation argc) := by
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
      | bufferSpan _ | readOnlyReference _ | array _ =>
        cases rest <;> fallback_raise_vacuous

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_eq : StepRaise .eq := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_eq

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_brzero (target : Nat) : StepRaise (.brzero target) := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_brzero

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_brnonzero (target : Nat) : StepRaise (.brnonzero target) := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_brnonzero

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_beq (target : Nat) : StepRaise (.beq target) := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_beq

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_bne (target : Nat) : StepRaise (.bne target) := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_bne

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_sub : StepRaise .sub := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_sub

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_ltu : StepRaise .ltu := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_ltu

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_gtu : StepRaise .gtu := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_gtu

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_bltu (target : Nat) : StepRaise (.bltu target) := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_bltu

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_bgeu (target : Nat) : StepRaise (.bgeu target) := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_bgeu

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_bgtu (target : Nat) : StepRaise (.bgtu target) := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_bgtu

/-- Reference observations preserve exceptional outcomes under relabeling. -/
theorem step_raise_bleu (target : Nat) : StepRaise (.bleu target) := by
  stack_cases =>
    first
        | exact fallback_raise (profile := expected.profile) _ rfl
            (fun _ => by base_relabels) (by intro absent; contradiction) context.next h
        | raise_lockstep

#print axioms step_raise_bleu

/-- Instructions dispatched directly to the memory evaluator preserve its faults. -/
theorem step_raise_instruction (op : CIL.Op)
    (relabels : ∀ r, op.relabel r = op)
    (dispatch : ∀ body pc args frame stack memory,
      step body op pc args frame stack memory =
        if unspecifiedOperands (observerCount op) stack || false then
          .error (.unsupported "Instruction observes unspecified vector bits")
        else do
          let (result, values) ← instruction op stack memory
          return .next (pc + 1) values frame result) : StepRaise op := by
  intro expected actual r pc q args frame stack memory exception context raised
  rw [dispatch] at raised
  rw [relabels, dispatch]
  split at raised
  · cases raised
  · rename_i observed
    simp only [observed, Bool.false_eq_true, ↓reduceIte] at raised ⊢
    cases found : instruction op stack memory with
    | error fault => simpa only [found, bind, Except.bind] using raised
    | ok result =>
      simp only [found, bind, Except.bind, Pure.pure, Except.pure] at raised
      cases raised

#print axioms step_raise_instruction

set_option maxHeartbeats 400000 in
/-- Only `throw` raises by itself; every other throw comes from a computation both steps share. -/
theorem step_raise (op : CIL.Op) : StepRaise op := by
  cases op
  case stackAlloc initLocals =>
    stack_cases =>
      first
        | fallback_raise_vacuous
        | (cases ‹CIL.Value› <;>
            dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h ⊢ <;>
            first | cases h | raise_lockstep)
  case nativeBinary operation => exact step_raise_nativeBinary operation
  case divide signed remainder => exact step_raise_divide signed remainder
  case checkedArithmetic kind signed => exact step_raise_checkedArithmetic kind signed
  case checkedConvert width signed unsignedInput =>
    exact step_raise_checkedConvert width signed unsignedInput
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
    stack_cases =>
      first | fallback_raise_vacuous | lookup_raise
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
  case sub => exact step_raise_sub
  case ltu => exact step_raise_ltu
  case gtu => exact step_raise_gtu
  case bltu target => exact step_raise_bltu target
  case bgeu target => exact step_raise_bgeu target
  case bgtu target => exact step_raise_bgtu target
  case bleu target => exact step_raise_bleu target
  case eq => exact step_raise_eq
  case brzero target => exact step_raise_brzero target
  case brnonzero target => exact step_raise_brnonzero target
  case beq target => exact step_raise_beq target
  case bne target => exact step_raise_bne target
  case nop | neg | gt | bgt | ble | convI1 | convI2 | convU2 | convI8 | convI4 | convU1
    | convU4 | convU8 | convU | bnot | add | mul | band | bor | bxor | shl | shr | shrUn
    | lt | branch | switch | bge | blt | feature =>
    step_raise_fallback (fun _ => by base_relabels) (fun absent => nomatch absent)
  case loadAggregate | copyObject | storeAggregate | initAggregate | loadScalar | storeScalar
    | fieldAt | fieldAddress | setFieldAt | aggregateFieldAt | setAggregateFieldAt | lane
    | laneAddress | setLane | const32 | const64 | load64 | store64 | dup | pop | skipInit | asRef =>
    exact step_raise_instruction _ (fun _ => rfl) (fun _ _ _ _ _ _ => rfl)

#print axioms step_raise
end CIL.Safety
