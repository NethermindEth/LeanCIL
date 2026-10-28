# Scalar evidence regression proof work

The scalar evidence fixtures repeat signature, span, and instruction metadata across
nearby positive and negative cases. Eleven bounded conjunctions now check those related
cases together, allowing a single kernel decision to reuse their common reductions.
All 58 grouped propositions retain their original statements. Four other kernel-decided
examples and the remaining fixtures stay separate. A token comparison verified that all
62 original kernel-decided example propositions still occur unchanged in the file.

The groups are named private theorems with axiom audits. They contain at most twelve
original cases each. No validator, extraction claim, or rejection condition changes.

Measurements used the same compiled dependencies from commit `16b79a4`, Lean 4.35.0,
and an isolated Apple M4 checkout. No other benchmark ran concurrently.

| Scalar evidence check | Original | Grouped |
| --- | ---: | ---: |
| Compile to `.olean` | 7.70 s | 5.20 s |
| Independent `leanchecker` replay | 0.74 s | 2.41 s |
| Combined | 8.44 s | 7.61 s |

The final source repeated at 5.25 s compilation and 2.39 s replay. Compilation improves
by about 32%; including independent replay, the improvement is about 10%. The named
grouped theorems increase replay work relative to the original anonymous examples, so
the compile-only saving must not be presented as the combined saving. Both checks pass,
with no `sorryAx` in the compilation log. These are local measurements, not a claim
about the whole Evidence job or a comparison between different CI runners.

Two investigations produced no retained change. Replacing generic specialization
reflexivity proofs with kernel decisions measured 10.03 s versus 9.93 s on the same
positive batch. A serial MemorySpans profile took 4.53 s, with no individual declaration
above 0.11 s. Serial profiler durations were used for attribution only; overlapping
asynchronous profiler durations must not be added together.
