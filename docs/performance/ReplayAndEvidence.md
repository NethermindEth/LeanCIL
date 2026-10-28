# Replay environments and evidence checks

## Published-interface validation

The auditor validates eligible published interfaces in the kernel-replayed environment,
using the complete target declaration-owner map. This includes private, unused and
auxiliary declarations. Ambiguous ownership, untargeted imported interfaces and requests
needing source metadata use the imported-metadata path.

`CIL.Replay.withReplayedModules` supplies the target-owner map as the final callback
argument. Interface validation uses it to enumerate declarations. Artifact binding,
independent kernel checking and fallback diagnostics apply to both audit paths.
`JointReplay` compares their verdicts for private declarations, unused forbidden axioms,
namespace spoofing, module-system visibility and equation auxiliaries.

A Windows comparison used the same compiled interface and alternated three pairs:

| Operation | Runs (seconds) | Median |
| --- | --- | --- |
| Separate replay and audit | 3.028, 3.107, 2.945 | 3.028 |
| Replayed interface audit | 1.485, 1.378, 1.401 | 1.401 |

The combined operation saves 1.63 seconds (54%) for this interface. This is a local
operation-level measurement, excluding CI setup and contention. The core synthetic
consumer fixtures do not publish interfaces, so it does not measure their runtime.

## Evidence process reuse and control isolation

The generic evidence fixture checks exact external identities in its positive batch,
including independent kernel replay. Identity mutations, primitive-array mutations and
memory-span mutations use isolated rejection batches. Each rejection case restores its
own command environment and must produce its expected diagnostic. Batching these cases
avoids four separate Lean process/import startups.

A paired Windows measurement of the generic evidence workload used separately compiled
fixture binaries: separate identity checks took 38.057 seconds and batched identity checks
took 33.712 seconds, a saving of 4.345 seconds (11.4%). These timings exclude the
control-isolation regression cases described below.

Narrowed positive controls use a fresh namespace and reject explicit references to the
original extraction namespace. This prevents missing declarations from resolving to the
original extraction. Lean checks the narrowed definitions and obligation types, while
reusing the original proof witness. Mutations never reuse those witnesses. Regressions
cover missing or changed definitions and dependencies on removed theorems.
