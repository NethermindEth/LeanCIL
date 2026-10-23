import Lean

-- `CIL.Safety.step` equations, one per dispatcher arm, so a step rewrites without unfolding the dispatcher.
register_simp_attr cil_step
register_simp_attr cil_guard
