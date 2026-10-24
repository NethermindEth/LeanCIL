import Lean

/-!
# Step simp sets

Two simp attributes used by the stepping tactics. They are registered in their own file
because a simp attribute cannot be used in the module that declares it.
-/

-- `CIL.Safety.step` equations, one per dispatcher arm, so a step rewrites without
-- unfolding the dispatcher.
register_simp_attr cil_step
-- Closed-form facts for the checks `step` makes before dispatch (unspecified bits, operand
-- counts), so stepping can decide them by simp.
register_simp_attr cil_guard
