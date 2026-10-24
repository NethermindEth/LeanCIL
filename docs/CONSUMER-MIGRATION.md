# Consumer migration

Changes to `Method`, `Embeds`, `BodyRefines`, `enterFrame`, `step` and `invoke`
affect the public proof API. PRs changing them should describe the migration,
provide equations for the previous default case where it remains sound, and
report the pinned consumer check separately from upstream tests.

## Vector128 locals and unspecified lanes

Opaque Vector128 locals are selected only when a method's reachable extracted
code creates unspecified lanes with `CreateScalarUnsafe(ulong)`. Other methods,
including methods whose unsafe branch was pruned by the profile, retain byte
homes. Address-taken locals always retain byte homes. The translation certificate
checks this selection; editing the emitted metadata cannot opt a method into a
different frame model.

An unsafe value cannot be written into a byte home. It must stay in an eligible
opaque local until a supported operation consumes its known lanes. Returns,
calls and caller-visible stores still reject unspecified lanes.

For bodies with `opaqueVectorLocals = []`:

- `makeSelectedLocals_nil` restores the `makeLocals` equation.
- `enterFrame_of_no_opaque` exposes the previous byte-home entry equation.
- `frameSetupFits_of_no_opaque` restores the three original frame-setup premises.
- `selectedKindsFit_nil` discharges the new selected-kind obligation.

`word_frame_setup`, `numeric_frame_setup` and `unknown_frame_setup` require the
explicit empty-opaque premise before their memory argument. Supply the body's
checked metadata equality; do not assume arbitrary bodies have no opaque locals.
For `Embeds` and `BodyRefines`, supply the `opaqueVectorLocals` equality alongside
the other metadata equalities. Prefer named record fields to anonymous positional
constructors so additions identify the missing field directly.

`StepComposition` re-exports `GuardNormalization`. Use `simp only [cil_guard]`
to normalize guards on known scalar/reference/vector constructors without
evaluating their BitVec payloads. Use the `cil_step` equations for instruction
reasoning. In custom dispatch tactics, inspect the operation before trying step
lemmas for other operations; unifying an unrelated step equation may unfold
large symbolic stacks. No global heartbeat increase or weakened safety condition
is part of this migration.

The runtime-profile migration is separate: see [RUNTIME-PROFILES](RUNTIME-PROFILES.md).
Changing a feature profile can change the selected code and requires fresh
compiled-method certificates even when the supporting library builds.
