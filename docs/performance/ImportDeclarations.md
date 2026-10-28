# Imported contract declaration discovery

`interfaceDeclarations` uses Lean's staged constant map to find current-file declarations.
Imported declarations occupy the first map and declarations added in the current module
occupy the second. A current-file query therefore traverses local declarations rather than
all imported declarations. Imported-module queries retain the existing module catalogs.

The complete scan remains available when the constant map is still in its first stage or
when the current module deliberately reuses an imported module's name. Ownership checks
remain unchanged. `Tests/ContractClosure.lean` compares the result against a full environment
traversal for empty, imported, current, mixed, missing and repeated module selections; it
also checks the colliding-name fallback using a small imported environment.

The measured contract-closure regression has 215,384 imported declarations and 20 local
declarations. This removes two scans of the imported declarations from that regression.
It does not remove interface compilation, independent replay, closure audits, mutation
fixtures or malicious elaborator rejection tests from the Imports suite.

Run `lake env lean --profile Tests/ContractClosure.lean` with the corresponding compiled
`CIL.Interface.Closure` module for each revision. These are focused test timings, not a
prediction for the full Imports job.

## Windows measurements

On the Ryzen 9 9950X with Lean 4.35.0, alternating runs of the same regression and
compiled dependencies took 9.35s / 10.66s before and 4.80s / 6.40s after (44% lower mean).
These runs include the added collision regression on both versions. Other Lean builds and
compression benchmarks were stopped; a short unrelated .NET selector check overlapped the
window, so the exact percentage remains approximate. Instrumented current-module selection
fell from roughly 2.2–2.8s per query to 3ms. The complete test still performs an independent
full-environment traversal to check equivalence, and that reference work is intentionally
retained.

The modified module compiles and passes independent `leanchecker` replay. The focused
regression passes before and after. No whole-suite speedup is claimed from these timings;
the corresponding CI stage previously took 27.1s within a 272.6s Imports suite.
