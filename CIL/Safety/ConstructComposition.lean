import CIL.Safety.FuelLemmas
import CIL.Safety.LiveValues

/-!
# Composing a constructor with its caller

The `newobj` counterpart of `CallComposition`: a caller proof uses a constructor's separately
proved `invoke` result. The constructor returns nothing; the caller resumes with the value
loaded from the temporary the constructor initialized.
-/

namespace CIL.Safety

/-- A constructor must return void, and its full initialized value must be
    loaded successfully before the caller resumes with that value. -/
theorem run_construct_of_invoke {program : CIL.Program} {fuel method pc callee : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest values : List Value}
    {frame constructedFrame : Frame} {temporary : Reference} {kind : CIL.LocalKind} {value : Value}
    {memory updated childResult result : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.construct callee arguments rest constructedFrame temporary kind updated))
    (child : invoke program fuel callee arguments updated = .ok (childResult, []))
    (loaded : loadLocal childResult (.bytes kind temporary) = .ok value)
    (continuation : run program fuel method (pc + 1) args constructedFrame (value :: rest)
      childResult = .ok (result, values)) :
    run program (fuel + 1) method pc args frame stack memory = .ok (result, values) := by
  cases hb : program[callee]? with
  | none => simp [invoke, hb] at child
  | some childBody =>
    cases ha : arguments.mapM (checkedValue updated) with
    | error fault => simp [invoke, hb, ha, Except.mapError, Bind.bind, Except.bind] at child
    | ok checked =>
      have same := (checkedValues_valid _ _ _ ha).1
      subst checked
      cases he : enterFrame childBody arguments updated with
      | error fault => simp [invoke, hb, ha, he, Except.mapError, Bind.bind, Except.bind] at child
      | ok entered =>
        obtain ⟨childFrame, childMemory⟩ := entered
        simp only [invoke, hb, ha, he, Except.mapError, Bind.bind, Except.bind] at child
        simp only [run, methodFound, instructionFound, stepped, hb, he, child,
          loaded, localWidth, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false,
          continuation, Except.mapError, Bind.bind, Except.bind]

/-- Independently sufficient budgets combine without requiring equal proof fuel. -/
theorem run_construct_exists {program : CIL.Program} {method pc callee : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest values : List Value}
    {frame constructedFrame : Frame} {temporary : Reference} {kind : CIL.LocalKind} {value : Value}
    {memory updated childResult result : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.construct callee arguments rest constructedFrame temporary kind updated))
    (child : ∃ fuel, invoke program fuel callee arguments updated = .ok (childResult, []))
    (loaded : loadLocal childResult (.bytes kind temporary) = .ok value)
    (continuation : ∃ fuel, run program fuel method (pc + 1) args constructedFrame (value :: rest)
      childResult = .ok (result, values)) :
    ∃ fuel, run program fuel method pc args frame stack memory = .ok (result, values) := by
  obtain ⟨childFuel, child⟩ := child
  obtain ⟨parentFuel, continuation⟩ := continuation
  have hc := invoke_mono program childFuel parentFuel callee arguments updated
    (.ok (childResult, [])) trivial child
  have hp := run_mono program parentFuel childFuel method (pc + 1) args constructedFrame
    (value :: rest) childResult (.ok (result, values)) trivial continuation
  rw [Nat.add_comm parentFuel childFuel] at hp
  exact ⟨childFuel + parentFuel + 1,
    run_construct_of_invoke methodFound instructionFound stepped hc loaded hp⟩

#print axioms run_construct_of_invoke
#print axioms run_construct_exists

end CIL.Safety
