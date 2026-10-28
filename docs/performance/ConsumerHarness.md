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
