import CIL.Safety.BufferContents
import CIL.Safety.MethodContract

/-!
# Side conditions of a loop's element writes

A loop outline that writes through `Unsafe.Add` of a reference argument needs three facts at the
iteration's memory: write authority over the element, the index below `2 ^ 31` and the element
within the footprint. `cil_loop_obligation` proves each from the hypotheses the iteration holds,
with the author's invariant, precondition and footprint unfolded, so the author writes only those
definitions. A callee's contract proof uses it the same way at a throw its precondition rules
out. While a definition is still `sorry` it leaves an ordinary hole; once all are written, a fact
it cannot prove is an error at that fact, never a silent admission.
-/

namespace CIL.Safety

open Lean Meta Elab Tactic

/-- An element in the room after an initialized prefix may be written on its own. -/
theorem Filled.element_writable {m : Memory} {base : Reference} {width : Nat}
    {xs : List (BitVec (8 * width))} {room index : Nat} (filled : Filled m base width xs room)
    (low : xs.length ≤ index) (high : index < xs.length + room) :
    Writable m (base.element width index) width 0 1 :=
  filled.2.sub low (by omega)

/-- An element of a writable run may be written on its own. -/
theorem Writable.element_writable {m : Memory} {base : Reference} {width start count index : Nat}
    (writable : Writable m base width start count) (low : start ≤ index)
    (high : index < start + count) : Writable m (base.element width index) width 0 1 :=
  writable.sub low (by omega)

#print axioms Filled.element_writable
#print axioms Writable.element_writable

/-- Replace each conjunction among the hypotheses by its parts. -/
private partial def splitConjunctions (goal : MVarId) : MetaM MVarId := goal.withContext do
  for hypothesis in (← getLCtx) do
    if hypothesis.isImplementationDetail then continue
    if (← whnfR (← instantiateMVars hypothesis.type)).isAppOfArity ``And 2 then
      let subgoals ← goal.cases hypothesis.fvarId
      let some split := subgoals[0]? | return goal
      return ← splitConjunctions split.mvarId
  return goal

/-- Prove a side condition the specification implies from the hypotheses with `definitions`
    unfolded: a contradiction among them, such as a callee's throw its precondition excludes, an
    index bound by `omega`, footprint membership by `simp [Within]` and `omega`, and write
    authority from a `Filled` or `Writable` fact covering the element. -/
syntax (name := loopObligation) "cil_loop_obligation " "[" ident,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_loop_obligation [$definitions,*]) => do
    let names ← definitions.getElems.mapM fun definition =>
      realizeGlobalConstNoOverloadWithInfo definition.raw
    let unfolded ← definitions.getElems.mapM fun definition =>
      `(Lean.Parser.Tactic.simpLemma| $definition:ident)
    let unwritten ← names.anyM fun name => do
      return (← getConstInfo name).value?.any (·.hasSorry)
    let goal ← getMainGoal
    let saved ← saveState
    try
      evalTactic (← `(tactic| (try simp only [$unfolded,*] at *)))
      replaceMainGoal [← splitConjunctions (← getMainGoal)]
      -- A signed comparison of small words is the unsigned one `omega` reads.
      evalTactic (← `(tactic| (try simp (disch := omega) only [BitVec.toInt_eq_toNat_of_lt] at *)))
      -- `omega` comes first: `contradiction` can exceed the recursion depth deciding a
      -- comparison of large literals, which `first` does not catch.
      evalTactic (← `(tactic| first
        | omega
        | contradiction
        | (simp [Within] <;> omega)
        | (refine Filled.element_writable ‹_› ?_ ?_ <;> (try simp) <;> omega)
        | (refine Writable.element_writable ‹_› ?_ ?_ <;> (try simp) <;> omega)))
      unless (← getUnsolvedGoals).isEmpty do throwError "goals remain"
    catch _ =>
      saved.restore
      if unwritten then
        -- The author has yet to write what the fact follows from, so it stays a hole.
        goal.admit (synthetic := false)
        replaceMainGoal []
      else
        goal.withContext do
          throwError "cil_loop_obligation could not prove{indentExpr (← goal.getType)}\n\
            from the hypotheses with {names.toList} unfolded; replace it with a proof"

end CIL.Safety
