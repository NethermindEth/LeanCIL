import Lean
import CIL.Safety.Equations
import CIL.StepEquations

namespace Tests.InterpreterEquations
open Lean

-- A consumer macro naming a reserved equation lemma, which a quotation cannot generate itself.
macro "unfold_dispatch" : tactic => `(tactic| rw [CIL.step.eq_def])

example (returns : Bool) (pc : Nat) (args stack : List CIL.Value) (frame : Nat) (memory : CIL.Memory) :
    CIL.step .nop returns pc args frame stack memory = CIL.step .nop returns pc args frame stack memory := by
  unfold_dispatch

-- Each lemma must come from its shared module; one generated here would mean importers rebuild it.
run_cmd do
  let env ← getEnv
  for (name, owner) in [
      (`CIL.step.eq_def, `CIL.Safety.Execution), (`CIL.Safety.step.eq_def, `CIL.Safety.Execution),
      (`CIL.step.eq_1, `CIL.StepEquations),
      (`CIL.Safety.step.eq_1, `CIL.Safety.Equations), (`CIL.Safety.instruction.eq_1, `CIL.Safety.Equations),
      (`CIL.Safety.instruction.eq_def, `CIL.Safety.Equations),
      (`CIL.Safety.memoryInstruction.eq_1, `CIL.Safety.Equations),
      (`CIL.Safety.memoryInstruction.eq_def, `CIL.Safety.Equations),
      (`CIL.Safety.staticInstruction.eq_1, `CIL.Safety.Equations),
      (`CIL.Safety.staticInstruction.eq_def, `CIL.Safety.Equations),
      (`CIL.Safety.pureArity.eq_1, `CIL.Safety.Equations), (`CIL.Safety.pureArity.eq_def, `CIL.Safety.Equations),
      (`CIL.Safety.scalars.eq_1, `CIL.Safety.Equations), (`CIL.Safety.scalars.eq_def, `CIL.Safety.Equations),
      (`CIL.binary.eq_1, `CIL.Safety.Equations), (`CIL.binary.eq_def, `CIL.Safety.Equations),
      (`CIL.unary.eq_1, `CIL.Safety.Equations), (`CIL.unary.eq_def, `CIL.Safety.Equations)] do
    let some index := env.getModuleIdxFor? name | throwError "{name} is not stored by an import"
    let stored := env.header.moduleNames[index.toNat]!
    unless stored == owner do throwError "{name} is stored by {stored}, expected {owner}"

end Tests.InterpreterEquations
