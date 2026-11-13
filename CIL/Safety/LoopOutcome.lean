import CIL.Safety.LoopContract
import CIL.Safety.OutcomeContract
import CIL.Verification

/-!
# Loop outcomes: return or raise

`LoopOutcome` extends loop termination to outcome contracts: from a loop state the run either
returns satisfying `post` or throws exactly the named exception. The induction principle,
call rules and tactics mirror `CIL.Safety.LoopContract`, and `ensures_outcome_of_loop` lifts a
loop outcome from method entry to `EnsuresOutcome` for the whole method.
-/

namespace CIL.Safety

/-- The loop run from `state` returns satisfying `post` when `raises` is `none`, and throws
    exactly the named exception otherwise. -/
def LoopOutcome (program : CIL.Program) (method : Nat) (args : List Value)
    (post : Memory → List Value → Prop) (raises : Option String) (state : LoopState) : Prop :=
  match raises with
  | some exception =>
    RunRaises program method state.pc args state.frame state.stack state.memory exception
  | none => LoopTerminates program method args post state

theorem loop_outcome_none {program : CIL.Program} {method : Nat} {args : List Value}
    {post : Memory → List Value → Prop} {state : LoopState} :
    LoopOutcome program method args post none state =
      LoopTerminates program method args post state := rfl

theorem loop_outcome_some {program : CIL.Program} {method pc : Nat} {args stack : List Value}
    {post : Memory → List Value → Prop} {frame : Frame} {memory : Memory} {exception : String} :
    LoopOutcome program method args post (some exception) ⟨pc, frame, stack, memory⟩ =
      RunRaises program method pc args frame stack memory exception := rfl

/-- A continuing iteration may assume the outcome at every smaller invariant state; an exit
    proves it directly. -/
theorem loop_outcome_induction {α : Type} (program : CIL.Program) (method : Nat)
    (args : List Value) (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat)
    (post : Memory → List Value → Prop) (raises : Option String)
    (progress : ∀ state, invariant state →
      (∀ next, invariant next → measure next < measure state →
        LoopOutcome program method args post raises (configuration next)) →
      LoopOutcome program method args post raises (configuration state))
    (state : α) (valid : invariant state) :
    LoopOutcome program method args post raises (configuration state) := by
  generalize rank : measure state = n
  induction n using Nat.strongRecOn generalizing state with
  | ind n ih =>
    exact progress state valid fun next preserved decreases =>
      ih (measure next) (by omega) next preserved rfl

/-- A state has the outcome if its fetched instruction steps to a state that has it. -/
theorem loop_outcome_next {program : CIL.Program} {method pc next : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    {raises : Option String}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next next values nextFrame updated))
    (rest : LoopOutcome program method args post raises ⟨next, nextFrame, values, updated⟩) :
    LoopOutcome program method args post raises ⟨pc, frame, stack, memory⟩ := by
  cases raises with
  | some exception => exact run_next_raises found instruction stepped rest
  | none => exact loop_terminates_next found instruction stepped rest

/-- A loop path to a state with the outcome gives the outcome at its source. -/
theorem loop_reaches_outcome {program : CIL.Program} {method : Nat} {args : List Value}
    {source target : LoopState} {post : Memory → List Value → Prop} {raises : Option String}
    (path : LoopReaches program method args source target)
    (finished : LoopOutcome program method args post raises target) :
    LoopOutcome program method args post raises source := by
  cases raises with
  | none => exact loop_reaches_terminates path finished
  | some exception =>
    obtain ⟨cost, reached, segment, rfl⟩ := path
    obtain ⟨fuel, fault, ran, thrown⟩ := finished
    exact ⟨fuel + cost, fault, (segment fuel).trans ran, thrown⟩

/-- Continue a loop path past a callee whose outcome contract names no exception for this
    input. -/
theorem loop_outcome_call {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Instruction}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop} {raises : Option String}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (normal : c.raises input updated = none)
    (continuation : ∀ final output,
      CallResult c.toMethodContract program callee input updated final output →
      LoopOutcome program method args post raises
        ⟨pc + 1, frame, c.results output ++ rest, final⟩) :
    LoopOutcome program method args post raises ⟨pc, frame, stack, memory⟩ := by
  cases raises with
  | some exception =>
    exact run_call_raises_after_outcome holds input methodFound instructionFound stepped encoded
      permitted normal continuation
  | none =>
    exact WP.adequate.mpr (run_call_of_outcome holds input methodFound instructionFound stepped
      encoded permitted normal (fun final output result =>
        WP.adequate.mp (continuation final output result)))

/-- `loop_outcome_call` that also hands the continuation the callee's `WellFormed`, static
    world and catalog agreement. -/
theorem loop_outcome_call_formed {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Instruction}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop} {raises : Option String}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (formed : memory.WellFormed) (normal : c.raises input updated = none)
    (continuation : ∀ final output,
      CallResult c.toMethodContract program callee input updated final output →
      FrameInvariants program memory final →
      LoopOutcome program method args post raises
        ⟨pc + 1, frame, c.results output ++ rest, final⟩) :
    LoopOutcome program method args post raises ⟨pc, frame, stack, memory⟩ := by
  subst encoded
  exact loop_outcome_call holds input methodFound instructionFound stepped rfl permitted normal
    fun final output call => continuation final output call
      (call.frame_invariants methodFound instructionFound stepped formed)

/-- Exit a loop with the exception a callee's contract names; no invariant or measure is
    needed. -/
theorem loop_outcome_call_raises {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Instruction}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop} {exception : String}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input)
    (checked : arguments.mapM (checkedValue updated) = .ok arguments)
    (permitted : c.pre input updated) (raised : c.raises input updated = some exception) :
    LoopOutcome program method args post (some exception) ⟨pc, frame, stack, memory⟩ :=
  run_call_raises_of_contract holds input methodFound instructionFound stepped encoded checked
    permitted raised

/-- A fetched `throw` of the named exception exits the loop with that outcome. -/
theorem loop_outcome_throw {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack : List Value} {frame : Frame}
    {memory : Memory}
    {post : Memory → List Value → Prop} {exception : String}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .error (.thrown exception)) :
    LoopOutcome program method args post (some exception) ⟨pc, frame, stack, memory⟩ :=
  run_throw_raises methodFound instructionFound stepped

/-- A run that settles at any fuel without throwing `exception` refutes that outcome;
    exhaustion is not settled. -/
theorem loop_outcome_some_refuted {program : CIL.Program} {fuel method pc : Nat}
    {args stack : List Value}
    {frame : Frame} {memory : Memory} {post : Memory → List Value → Prop} {exception : String}
    {outcome : Except LocatedFault (Memory × List Value)}
    (ran : run program fuel method pc args frame stack memory = outcome) (settled : Settled outcome)
    (other : ∀ fault, outcome = .error fault → fault.fault ≠ .thrown exception) :
    ¬ LoopOutcome program method args post (some exception) ⟨pc, frame, stack, memory⟩ := by
  rintro ⟨later, fault, raised, thrown⟩
  have up := run_mono program fuel later method pc args frame stack memory outcome settled ran
  have down := run_mono program later fuel method pc args frame stack memory (.error fault)
    (by simp [Settled, thrown]) raised
  rw [Nat.add_comm] at down
  exact other fault (up.symm.trans down) thrown

/-- Each permitted input returns satisfying `post` or throws exactly the exception `raises`
    names for it. -/
def EnsuresOutcome (program : CIL.Program) (method : Nat)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Memory → List Value → Prop)
    (raises : List Value → Memory → Option String) : Prop :=
  ∀ args initial, pre args initial →
    match raises args initial with
    | some exception => Raises program method args initial exception
    | none => ∃ fuel final values, invoke program fuel method args initial = .ok (final, values) ∧
        post args initial final values

/-- Total correctness is the outcome specification that never raises. -/
theorem ensures_outcome_none {program : CIL.Program} {method : Nat}
    {pre : List Value → Memory → Prop} {post : List Value → Memory → Memory → List Value → Prop} :
    EnsuresOutcome program method pre post (fun _ _ => none) =
      Ensures program method pre post := rfl

/-- Lift a loop outcome through checked invocation setup to the outcome of the whole method. -/
theorem ensures_outcome_of_loop (program : CIL.Program) (method : Nat)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Memory → List Value → Prop)
    (raises : List Value → Memory → Option String)
    (verified : ∀ args initial, pre args initial →
      ∃ body frame entered,
        program[method]? = some body ∧
        args.mapM (checkedValue initial) = .ok args ∧
        enterFrame body args initial = .ok (frame, entered) ∧
        LoopOutcome program method args (post args initial) (raises args initial)
          ⟨0, frame, [], entered⟩) :
    EnsuresOutcome program method pre post raises := by
  intro args initial permitted
  obtain ⟨body, frame, entered, found, checked, setup, outcome⟩ := verified args initial permitted
  revert outcome
  cases raises args initial with
  | some exception => exact raises_of_run found checked setup
  | none =>
    rintro ⟨fuel, ⟨final, values⟩, executed, satisfied⟩
    exact ⟨fuel, final, values, invoke_of_run found checked setup executed, satisfied⟩

#print axioms loop_outcome_induction
#print axioms loop_outcome_next
#print axioms loop_reaches_outcome
#print axioms loop_outcome_call
#print axioms loop_outcome_call_formed
#print axioms loop_outcome_call_raises
#print axioms loop_outcome_throw
#print axioms loop_outcome_some_refuted
#print axioms ensures_outcome_of_loop

/-- Step a `LoopOutcome` goal through non-call, non-return instructions until one does not
    apply; the goal keeps its tag. -/
syntax "cil_loop_outcome_advance" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_loop_outcome_advance [$facts:term,*]) => keepingTag do
    let facts := facts.getElems
    let prepared ← cilNormalisedFacts facts
    let rewrite ← `(tactic| cil_simp_only [$[$facts:term],*])
    let next ← `(tactic| (
      apply CIL.Safety.loop_outcome_next
      · cil_lookup [$[$facts:term],*]
      · cil_lookup [$[$facts:term],*]
      · cil_checked_step_normalized [$[$prepared:term],*]))
    -- Rewrite the whole goal while that makes progress, else take one step; the record keeps
    -- each instruction's rewrite to the terms it produced. As under `repeat first`, a failure
    -- throws instead of logging an error and admitting the goal.
    withNormalRun <| withoutRecover do
      repeat
        let saved ← saveState
        let rewrote ← withNormalNodes facts do
          try cilSimpProgress rewrite catch _ => saved.restore; pure false
        if rewrote then continue
        let stepped ← withNormalNodes prepared do
          let beforeStep ← saveState
          try withMainContext (evalTactic next); pure true
          catch _ => beforeStep.restore; pure false
        unless stepped do break

/-- Continue past a returning callee at a `bind_call` site; leaves the `precondition`, the
    `raises` equation, then the continuation. -/
syntax "cil_loop_outcome_call" term:max term:max " at " ident "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_loop_outcome_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.loop_outcome_call $holds $input
      (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?precondition ?raises ?_
    cil_name_obligations $holds))

/-- Exit with the exception the callee's contract names at a `bind_call` site; leaves the
    `precondition` and the `raises` equation. -/
syntax "cil_loop_outcome_raise" term:max term:max " at " ident "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_loop_outcome_raise $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.loop_outcome_call_raises $holds $input
      (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl)
      (by cil_checked_side [$[$facts:term],*]) ?precondition ?raises
    cil_name_obligations $holds))

end CIL.Safety
