# Consumer migration

Changes to `Method`, `Embeds`, `BodyRefines`, `enterFrame`, `step` and `invoke`
affect the public proof API. PRs changing them should describe the migration,
provide equations for the previous default case where it remains sound, and
cover supported consumer APIs with self-contained regression fixtures.

The advisory `Consumer compatibility` workflow runs daily at 04:37 UTC against
LeanCIL main, or manually against a selected ref. It does not run on pull requests
or pushes. Downstream int256 proofs therefore do not determine the status of
LeanCIL's normal PR checks. int256's own CI should verify its proofs against its
pinned LeanCIL version.

The compatibility workflow checks out an immutable int256
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
reasoning. A `.memory` step now rewrites to `formValue`, `loadValue`, `storeValue`
or `add`, so state memory facts at that level; facts about `memoryInstruction`
or `staticInstruction` still apply, through a slower retry in `cil_checked_step`,
`cil_checked_steps`, `cil_contract_steps` and the loop tactics; a hand-written step
or `cil_checked_step_equations` call with such a fact must
`rw [CIL.Safety.step_memory_eq]` first, and for a `memoryInstruction` fact also unfold
`CIL.Safety.staticInstruction`, or restate it at the per-shape level. Through
`cil_checked_step_equations`, an `add`, `spanItem`, `copyBlock` or `initBlock` step
needs `CIL.Safety.referenceAt_address` passed (or use `cil_checked_step`). A `referenceAt r = .ok a`
fact about a symbolic `ManagedReference` applies. A `.feature` step
pushes the profile field, such as `body.profile.avx2`, which is the canonical
fact form. Those checked-step tactics normalize a fact stated through
`FeatureProfile.evaluate` or on a method's profile projection (local, proof term, global theorem
or quantified over every feature) to it; elsewhere, including `simp only [cil_step, facts]` and
`cil_checked_step_equations`, state it on the field or run
`simp only [CIL.Safety.reduceMethodProfile, cil_feature] at h` first; a fact about a
symbolic feature `body.profile.evaluate f` applies as stated. In custom dispatch tactics,
inspect the operation before trying step lemmas for other operations; unifying an unrelated step equation may unfold
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
Failures show red in the scheduled or manually dispatched run; keep this advisory
check out of required branch-protection checks. The summary records elapsed
library update/build time. Hosted-runner timings vary, so this is diagnostic
rather than a performance threshold.

The immutable consumer pin currently names the unmerged int256#141 head. Advance
it to the merged revision after that PR lands.
