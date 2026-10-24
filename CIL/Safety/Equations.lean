import CIL.Safety.Execution

/-!
# Shared interpreter equations

Forces Lean to generate the equation lemmas of the checked interpreter's dispatchers in one
module. Stepping tactics and contracts downstream unfold `step` and its helpers many times;
importing this file lets them reuse one copy of each equation instead of regenerating it.
Nothing here is meant to be referenced by name.
-/

namespace CIL.Safety

/-- Generates the equations of the interpreter's smaller dispatchers once, so importers that
    unfold them reuse these instead of each building a copy. -/
private theorem interpreter_equations_generated : True := by
  have := @step.eq_1
  have := @instruction.eq_1
  have := @instruction.eq_def
  have := @memoryInstruction.eq_1
  have := @memoryInstruction.eq_def
  have := @staticInstruction.eq_1
  have := @staticInstruction.eq_def
  have := @pureArity.eq_1
  have := @pureArity.eq_def
  have := @scalars.eq_1
  have := @scalars.eq_def
  have := @CIL.binary.eq_1
  have := @CIL.binary.eq_def
  have := @CIL.unary.eq_1
  have := @CIL.unary.eq_def
  trivial

end CIL.Safety
