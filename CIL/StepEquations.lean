import CIL.Semantics

/-!
# Shared step equations

Forces Lean to generate the equation lemmas of `CIL.step` in one module, so downstream
modules import them instead of regenerating them.
-/

namespace CIL

/-- Generates the per-opcode equations of `step` once (about 20 MB), so importers that unfold
    the dispatcher reuse them instead of each building a copy. -/
private theorem step_equations_generated : True := by
  have := @step.eq_1
  trivial

end CIL
