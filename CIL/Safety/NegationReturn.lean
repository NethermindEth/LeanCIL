import CIL.Safety.StepComposition

namespace CIL.Safety

/-- Execute Boolean negation from its actual constant/equality/return suffix. -/
theorem run_negation_return (program : CIL.Program) (method pc : Nat) (body : CIL.Method)
    (lookup : program[method]? = some body)
    (constant : body.code[pc]? = some (.const32 0))
    (equality : body.code[pc + 1]? = some .eq)
    (returned : body.code[pc + 1 + 1]? = some .ret)
    (returns : body.returnsValue = true)
    (args : List Value) (frame : Frame) (memory : Memory) (flag : BitVec 32) :
    run program 3 method pc args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if flag = 0 then 1 else 0))]) := by
  rw [run_next lookup constant (by rfl), run_next lookup equality (by rfl)]
  apply run_return lookup returned
  · change (if 1 = (if body.returnsValue then 1 else 0) then _ else _) = _
    rw [returns]
    rfl
  · rfl
#print axioms run_negation_return
end CIL.Safety
