# Consumer harness compilation reuse

`Tests/ConsumerVerification.cs` previously launched six separate .NET file apps. Each compiled
its own copy of shared verifier code before running its assertions. The six checks are now
included in the parent executable and dispatched through `--check` in separate processes.
Environment changes, private caches and fingerprint worker processes remain isolated. No proof,
mutation, expected rejection, independent replay or cache-invalidation assertion was removed.

On Windows, an otherwise quiet comparison against `2bfe18e` rebuilt the parent and six child
apps in 15.38 seconds total. Rebuilding the combined executable took 2.13 seconds, removing
13.25 seconds of setup work (seven compiler invocations become one). Both used
`dotnet build -t:Rebuild -c Release -p:EnforceCodeStyleInBuild=true
-p:GenerateDocumentationFile=true -p:WarningsAsErrors=IDE0005` with separate output directories.
This measures harness compilation only, not the complete Core job or Lean proof speed.

All six dispatched checks passed: source resolution, both support-union orders, certificate
reuse and corruption, extraction components, canonical fingerprint reuse, and certified base
fingerprints. The certificate check used a warm authenticated library, as CI does: a first
cold library build has a temporary path which changes on the next invocation and invalidates
the test's otherwise-unchanged generated package configuration. No assertion was relaxed for
that cold setup. The original certificate harness also passed against the warm library.

Local build measurements and validation logs are under `artifacts/core-compile/`; the paired
build measurements are in `paired/timings.json`. See [validation commands](../VALIDATION.md)
for running an individual consumer check.

## Replay import overhead investigation

A native probe instrumented `CIL.Replay.withReplayedModules` around target loading,
`Lean.importModulesCore`, `Lean.finalizeImport`, declaration replay and region cleanup.
Three quiet Windows runs of a single `rfl` theorem importing `CIL` measured:

| Operation | Range |
| --- | ---: |
| Read target module | 0–1 ms |
| Import dependencies | 992–1,036 ms |
| Finalize imported environment | 246–254 ms |
| Replay target declaration | 52–53 ms |
| Cleanup and report | 166–169 ms |
| Total | 1,461–1,510 ms |

An existing `JointA` fixture with only implicit `Init` imports took 366–400 ms.
These are diagnostic targets, not representative averages of the 65 Core replay calls.
The experiment isolates substantial fixed import cost even when the checked proof is trivial.
It does not establish that actual consumer proof checking is negligible.

No replay implementation change was retained. Joint replay already shares imports across
its exact target set, and fused auditing already reuses that replayed environment where
eligible. Faster dependency traversal would not remove this dominant import cost.
A future shared-base worker would need to preserve per-request import visibility, exclude
every target from its trusted imported base, bind all imported bytes and retire environments
before those bytes can change. Reusing an environment merely because module names match
would be incorrect. Narrower consumer imports can reduce work without that architecture,
but require fixture-specific checks that tactic behavior and rejection coverage are unchanged.

The follow-up source review found Core's hot consumer fixtures already import `CIL.Semantics`
or specific proof modules. Generated extraction uses `Translation`, `SymbolicExecution` and
`Safety.Execution`. The remaining umbrella imports in the inspected harnesses belong to a
non-elaborated parser fixture and an Evidence control. No narrower-import change was retained.
