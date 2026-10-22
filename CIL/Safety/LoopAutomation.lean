import CIL.Safety.Loops
import CIL.Safety.SymbolicExecution

namespace CIL.Safety

/-- Locate an invariant cutpoint by instruction shape. Missing matches point past
    the body and cannot satisfy the checked fetch obligations below. -/
def instructionLocation (body : CIL.Method) (predicate : CIL.Op → Bool) : Nat :=
  body.code.findIdx predicate

/-- A finite checked path whose cost is inferred while composing its instructions. -/
def LoopReaches (program : CIL.Program) (method : Nat) (args : List Value)
    (source target : LoopState) : Prop :=
  ∃ cost, LoopSegment program method args source target cost

theorem loop_reaches_refl {program : CIL.Program} {method : Nat} {args : List Value}
    {state : LoopState} : LoopReaches program method args state state :=
  ⟨0, fun _ => rfl⟩

theorem loop_reaches_next {program : CIL.Program} {method pc next : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {target : LoopState}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next next values nextFrame updated))
    (rest : LoopReaches program method args ⟨next, nextFrame, values, updated⟩ target) :
    LoopReaches program method args ⟨pc, frame, stack, memory⟩ target := by
  obtain ⟨cost, segment⟩ := rest
  refine ⟨cost + 1, ?_⟩
  intro fuel
  change run program (fuel + (cost + 1)) method pc args frame stack memory = _
  rw [← Nat.add_assoc, run_next found instruction stepped]
  exact segment fuel

theorem loop_terminates_next {program : CIL.Program} {method pc next : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next next values nextFrame updated))
    (rest : LoopTerminates program method args post ⟨next, nextFrame, values, updated⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  run_next_exists post found instruction stepped rest

theorem loop_terminates_return {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values)
    (satisfied : post (leaveFrame frame updated) values) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  ⟨1, leaveFrame frame updated, values, run_return found instruction stepped checked, satisfied⟩

theorem loop_reaches_terminates {program : CIL.Program} {method : Nat} {args : List Value}
    {source target : LoopState} {post : Memory → List Value → Prop}
    (path : LoopReaches program method args source target)
    (finished : LoopTerminates program method args post target) :
    LoopTerminates program method args post source := by
  obtain ⟨cost, segment⟩ := path
  obtain ⟨fuel, final, values, executed, satisfied⟩ := finished
  exact ⟨fuel + cost, final, values, (segment fuel).trans executed, satisfied⟩

#print axioms loop_reaches_next
#print axioms loop_terminates_return
#print axioms loop_reaches_terminates

/-- Compose actual fetched instructions until the requested invariant state.
    Fuel is inferred from the path, including NOPs and unconditional branches. -/
macro "cil_loop_steps" "[" facts:term,* "]" : tactic =>
  `(tactic| repeat first
    | (simp only [$[$facts:term],*])
    | exact CIL.Safety.loop_reaches_refl
    | (apply CIL.Safety.loop_reaches_next
       · cil_lookup [$[$facts:term],*]
       · cil_lookup [$[$facts:term],*]
       · cil_checked_step [CIL.truth, $[$facts:term],*]))

/-- Establish an exit path and its postcondition without choosing a fuel bound. -/
macro "cil_loop_finish" "[" facts:term,* "]" : tactic =>
  `(tactic| repeat first
    | (simp only [$[$facts:term],*])
    | (apply CIL.Safety.loop_terminates_return (op := .ret _)
       · cil_lookup [$[$facts:term],*]
       · cil_lookup [$[$facts:term],*]
       · cil_checked_step [CIL.truth, $[$facts:term],*]
       · rfl
       · simp [$[$facts:term],*])
    | (apply CIL.Safety.loop_terminates_next
       · cil_lookup [$[$facts:term],*]
       · cil_lookup [$[$facts:term],*]
       · cil_checked_step [CIL.truth, $[$facts:term],*]))

end CIL.Safety
