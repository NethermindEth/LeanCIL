# Consumer migration

Changes to `Method`, `Embeds`, `BodyRefines`, `enterFrame`, `step` and `invoke`
affect the public proof API. PRs changing them should describe the migration,
provide equations for the previous default case where it remains sound, and
report the pinned consumer check separately from upstream tests.

The advisory `Consumer compatibility` workflow checks out an immutable int256
revision, substitutes the committed LeanCIL candidate as its Lake dependency,
builds its extraction-independent library, and verifies Add/ARM64 AdvSimd and
Subtract/x64 SSE4.2. Its summary distinguishes library builds from compiled
certificates. Update the consumer revision through a reviewed PR when adopting
API migrations. Logs are diagnostic evidence; the workflow does not publish
portable trusted consumer artifacts.

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

## Checked method boundaries

`step_newAggregate`, `step_newVector256` and `run_newAggregate_of_contract`
also require `arguments.any Value.hasUnspecified = false`, with an automatic proof for concrete arguments. For abstract arguments, prove this from the
actual argument encodings. The `checkedValue` and `numericValue` premises alone
allow partially specified internal vectors and therefore cannot justify it.
Generic consumer forwarding lemmas must carry the corresponding known-argument
premise; concrete integer and managed-reference callers discharge it by reduction.
The caller's arithmetic and memory contracts do not need to change.

The runtime-profile migration is separate: see [RUNTIME-PROFILES](RUNTIME-PROFILES.md).
Changing a feature profile can change the selected code and requires fresh
compiled-method certificates even when the supporting library builds.

## Consumer CI coverage

The pinned int256 workflow builds its full supporting Lean library and certifies
four selected gates: Add/ARM64 AdvSimd, Subtract/x64 SSE4.2, Multiply/scalar and
LeUInt256UInt256/scalar. This covers SIMD byte homes, embedding and comparison,
not the full gate registry; the job summary reports the pinned registry's size.
Failures show red; keep this advisory check out of required branch-protection
checks. The summary records elapsed library update/build time and the baseline
revision, runner and run ID. Hosted-runner timings vary, so this is diagnostic
rather than a performance threshold.

The immutable consumer pin currently names the unmerged int256#141 head. Advance
it to the merged revision after that PR lands.