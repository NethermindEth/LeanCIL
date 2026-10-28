# Reusing checked span extraction in contract fixtures

`Tests/MemorySpans.cs` compiles the complete `SliceRead` and `SliceWrite` extraction sources
for their contract imports, including each concrete execution theorem.
The later positive batch contains only the remaining `Existing`
fixture. Both independent evidence mutations still run against the original extraction,
and both functional contract proofs and unsupported-signature checks remain unchanged.
The positive batch uses `replay: false`; mutations share an isolated rejection batch.

On an isolated Windows checkout at `16b79a4`, the complete fixture improved from
25.81 s to 22.34 s (about 13%). Both runs passed every positive and negative check.
Both used the same authenticated CIL library, compiled C# programs, and prebuilt extractor
and example assembly. C# build time was excluded. The final rebuild enabled code-style
analysis and documentation generation; no IDE0005 diagnostics were reported.

An Apple M4 source-level comparison isolated the removed work: two original extraction
checks plus the three-case positive batch took 6.95 s; compiling the two complete sources
and the remaining case took 4.72 s. This measures the affected Lean invocations, not the
whole fixture. No different CI runners are compared and no whole-job saving is claimed.
