import Lean

/-!
# Step simp sets

Simp attributes used by the stepping tactics. They are registered in their own file
because a simp attribute cannot be used in the module that declares it.
-/

-- `CIL.Safety.step` equations, one per dispatcher arm, so a step rewrites without
-- unfolding the dispatcher.
register_simp_attr cil_step
-- Per-shape `CIL.Safety.step` equations past `instruction`, kept apart from `cil_step` so a
-- caller's fact about `instruction` can still be tried before they rewrite past it.
register_simp_attr cil_instruction_step
-- Closed-form facts for the checks `step` makes before dispatch (unspecified bits, operand
-- counts), so stepping can decide them by simp.
register_simp_attr cil_guard
-- `FeatureProfile.evaluate` equations, one per `Feature` constructor, so facts are normalised
-- to the field a known feature test steps to.
register_simp_attr cil_feature
-- Successful checked values and typed homes normalize without expanding instruction dispatch.
register_simp_attr cil_checked
-- Definitions that `bind_entry` and `bind_cutpoint` generate for a proof, such as loop states,
-- entry frames and slot facts; the loop tactics use the set in scope as facts.
register_simp_attr cil_loop_unfold
