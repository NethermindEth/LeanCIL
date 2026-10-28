# Evidence harness reuse

## Consistent Release builds

The suite runner builds file-app fixtures in Release with its analyzer properties. Nested
file-app runs use those same options instead of implicitly selecting Debug and compiling
a second output. They still perform the normal incremental build, so changed sources rebuild;
only explicitly prepared fixtures use `--no-build`. Explicit configuration options remain
unchanged, and authenticated shared fixtures retain their source and output validation.
The runner declares the analyzer properties in its file-app header too, so a plain Release
launch and its self-build use identical settings. This avoids rebuilding a running apphost,
which Windows locks, while retaining the analyzer-enabled build.

A Windows probe including the real `Verification.cs`, prebuilt in Release, took 1.77 s with
the previous implicit Debug run and 1.10 s with the matching Release run. The latter reused
the existing Release assembly and emitted no compilation warnings; the former compiled a
separate Debug assembly. This measures one nested launch, not a whole-suite speedup.
`BuildReuse.cs` checks nested Release execution, argument forwarding, source mutation rebuilds
and explicit Debug overrides. `PreparedFixtures.cs` retains authenticated-output and
source-invalidation coverage.

## Generated-batch controls

Generated positive batches use the authenticated native auditor for declaration replay through
the existing `ReplayCheckedModules` helper. The target remains exactly `PositiveBatch`;
every safe, total declaration is checked, and the toolchain checker remains the fallback if
native replay rejects or cannot confirm the exact target set. The library manifest authenticates
the auditor before fixture compilation. Neither imported initializers nor source commands run
during native replay.

Two alternating Windows replay comparisons on the same captured GenericEvidence batch measured
12.34 / 12.08 s with the toolchain checker and 3.06 / 3.08 s with native replay. This is a
replay-only result, excluding compilation and library preparation; it does not predict a whole
Evidence-job saving. The captured `.olean` SHA256 was
`fd8863719258344669794fa0a9a631fa448c1a564e74f2657924eaecd622e845`.

The complete updated GenericEvidence fixture passed in 40.01 s with its current positive
batch replay taking 2.29 s. The generated/rejected harness controls passed in 19.80 s;
their unchecked declaration failed native replay and then failed the pinned toolchain-checker
fallback with the required declaration type mismatch. The ordinary invalid proof still fails
during compilation. The final C# analyzer builds and all 17 selector checks passed.

The generated-batch failure controls live in `RejectedEvidenceTests.cs`, alongside the
rejection-harness controls. They reuse its otherwise-valid theorem instead of checking a full
generic extraction twice. A valid first case still cannot hide an invalid second case. The
ordinary false proof must fail with `decide` / `is false`; the unchecked forged declaration
must compile and then fail independent `leanchecker` replay with a declaration type mismatch.
Generic extraction positives and all metadata mutations remain unchanged.

The focused existing script and analyzer rebuilds passed. The two moved controls took 6.07 s
locally, including independent replay. Rechecking the two captured original generic probes
against the same authenticated library took 6.82 s (2.15 s for the false proof; 4.67 s for
compilation and forged-declaration replay). The observed saving is small, about 0.75 s; this
primarily consolidates harness coverage. This is not a whole-suite comparison; CI runs the
broader suite.

## Feature-flow mutation obligations

`FeatureEvidence` and `SpanTables` check only the feature-flow obligation in their
negative fixtures, instead of re-proving every unchanged validator and instruction lookup
equation. All six feature mutations and three forged span receivers remain. Feature
rejections require `FeatureFlowValid` and `is false`, so an unrelated failure cannot
stand in for the intended rejection.

The original positive certificate is still checked in full. A narrowed positive control
retains the declarations and exact obligation type and checks them against the original
theorem, using the same helper as generic evidence. Span controls accompany the existing
consumer proofs and their independent kernel replay. A folded span instruction without a
recognizable instruction theorem is an error, rather than silently dropping its mutation.

Complete Windows fixture runs against the same warm certified library, with proof-success
reuse disabled, measured the following. Both variants were explicitly rebuilt before using
`dotnet run --no-build`; timings exclude the C# build and library preparation but include
all positive controls, extraction, runtime comparisons and required consumer replay.

| Fixture | Original | Bounded obligations |
| --- | ---: | ---: |
| FeatureEvidence | 28.91 s | 26.96 s |
| SpanTables | 24.33 s | 21.90 s |

The combined saving is 4.38 s (8.2%) for these two fixtures, not the entire evidence suite.
Both complete fixtures and their final C# analyzer rebuilds passed. The full generated
feature mutation batch shrank from 102,193 to 64,315 bytes; no mutation was removed.
