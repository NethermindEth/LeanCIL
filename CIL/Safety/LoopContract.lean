import CIL.Safety.LoopAutomation
import CIL.Safety.MethodContract

/-!
# Loop termination and calls in loops

The induction principle for loop termination (an invariant with a decreasing measure) and
the rules that cross a call inside a loop through the callee's `MethodContract`, plus the
tactics `cil_loop_advance` and `cil_loop_call` that apply them to fetched instructions.
-/

namespace CIL.Safety

/-- An invariant and a decreasing measure give termination; each iteration may assume it for
    every smaller invariant state. -/
theorem loop_terminates_induction {α : Type} (program : CIL.Program) (method : Nat)
    (args : List Value) (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat)
    (post : Memory → List Value → Prop)
    (progress : ∀ state, invariant state →
      (∀ next, invariant next → measure next < measure state →
        LoopTerminates program method args post (configuration next)) →
      LoopTerminates program method args post (configuration state))
    (state : α) (valid : invariant state) :
    LoopTerminates program method args post (configuration state) := by
  generalize rank : measure state = n
  induction n using Nat.strongRecOn generalizing state with
  | ind n ih =>
    exact progress state valid fun next preserved decreases =>
      ih (measure next) (by omega) next preserved rfl

/-- A loop path crosses a fetched call through the callee's contract, never its body or
    fuel. -/
theorem loop_terminates_call {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      LoopTerminates program method args post ⟨pc + 1, frame, values ++ rest, final⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  run_call_of_contract holds input methodFound instructionFound stepped encoded permitted
    continuation

/-- `loop_terminates_call` that also hands the continuation the callee's `WellFormed` and
    static world. -/
theorem loop_terminates_call_formed {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (formed : memory.WellFormed)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) →
      final.WellFormed →
      StaticWorldPreserved program memory final →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      LoopTerminates program method args post ⟨pc + 1, frame, values ++ rest, final⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  run_call_of_contract_formed holds input methodFound instructionFound stepped encoded permitted
    formed continuation

#print axioms loop_terminates_induction
#print axioms loop_terminates_call
#print axioms loop_terminates_call_formed

/-- Step a `LoopTerminates` goal through non-call, non-return instructions until one does not
    apply. -/
syntax "cil_loop_advance" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_loop_advance [$facts:term,*]) =>
    cilWithNormalisedFacts facts.getElems fun facts prepared =>
    `(tactic| repeat first
      | (simp only [$[$facts:term],*])
      | (apply CIL.Safety.loop_terminates_next
         · cil_lookup [$[$facts:term],*]
         · cil_lookup [$[$facts:term],*]
         · cil_checked_step_normalized [$[$prepared:term],*]))

/-- Apply a contract at the fetched loop call or a `bind_call` site; leaves `pre`, then the
    continuation. -/

syntax "cil_loop_call" term:max term:max (" at " ident)? "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_loop_call $holds $input [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.loop_terminates_call $holds $input
      (by cil_lookup [$[$facts:term],*])
      (by cil_lookup [$[$facts:term],*])
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_))
  | `(tactic| cil_loop_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.loop_terminates_call $holds $input
      (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_))

end CIL.Safety
