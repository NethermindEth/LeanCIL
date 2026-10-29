# Proof automation regression coverage

## Proof automation

The checked proof APIs share execution traces, frame-setup effects and instruction contracts. Their
validity fields retain the required well-formedness and input validity hypotheses. See [Writing
checked proofs](PROOFS.md) for API locations and examples.

`Tests.Automation` checks an eight-instruction arithmetic method with symbolic inputs and arbitrary
caller memory, using `cil_checked_steps`. Its instruction sequence is `arg, arg, const32, shl, add,
const32, gtu, ret`; the theorem's axiom assertion permits only `propext` and `Quot.sound`. The same
module checks both paths of a symbolic branch using a supplied truth hypothesis, and verifies that
failed candidate summaries do not escape their transaction. Memory and static dispatch facts retain
abstract bitcast results in inferred stacks; a conjunction-wrapped store fact exercises the generic
dispatch fallback.

`Tests.FeatureExecution`, imported by `Tests.Automation`, checks enabled and disabled symbolic
features from caller facts, plus a concrete feature reduced to its profile field. All three
proofs use checked invocation and the shared feature evaluator.

`Tests.StoreFacts` checks symbolic carry and borrow stores whose write facts state `a + b + c`, `a -
b - c` and the flag words in source form, through both `cil_checked_steps` and `cil_contract_steps`.
A wrong stored value, address or source memory leaves the run stuck at that store, with the exact
unsolved goal asserted.

`Tests.Segment` composes the UInt256 Add Vector128 eight-op reference prefix and Multiply AVX2 input
stages at positions 44–56. Formation, checked loads and stores, intrinsic availability and exact
permutation semantics remain premises. Two actual vector writes frame all other numeric snapshots
using separated homes. Negative cases reject aliased homes, hidden indirect writes, changed endpoint
states, fuel costs and mismatched composition positions or assertions, and placements from a
different body or end boundary. Every new theorem is kernel checked with its axiom set reported.
`Tests.CodeAt` steps a segment of an abstract body at a symbolic start from the lookups its `CodeAt`
placement yields, with the error asserted when stepping has no placement, hands that segment theorem
the middle of a larger placed region, closes a concrete placement by `rfl` and refutes a shifted one
and one running past the code. It composes adjacent placements and splits them back with `cons_iff`,
`take` and `drop`, including past the segment's end, and recovers the positional `leading ++ segment
++ tail` form from a nonempty placement alone, proving the bound `exists_eq_append` needs by placing
the empty segment past the end of a body.

`Tests.MethodEmbedding` checks transport of checked executions to actual method bodies with mapped
program counters, and with trailing dead reference and span locals dropped, beside kept opaque
vector locals too. It checks empty and unmodeled span slots, both mutabilities and every supported
width, and rejects unsupported widths and scalar span initializers. It rejects numeric dead locals,
in the kernel and in the tactic, and non-trailing ones, and still reports a changed live instruction
under dead locals; `Tests.OutcomeEmbedding` checks transport of named exceptions and outcome
contracts, the relocated fault pc, and that changed throws, unsupported execution and fuel
exhaustion do not transfer. `Tests.AggregateSetup` and `Tests.Semantics` cover frame setup and
interpreter behavior. `Tests.RetainedNumericLocals` keeps dead numeric declarations before and after
a live local, transfers exact-memory executions and named exceptions through nested allocating
calls, and checks that deleting a numeric local changes the allocation watermark and fails ordinary
embedding. `Tests.AllocationRenaming` checks private allocation holes, extending identity maps,
relocated numeric homes and distinct activation labels. `Tests.AllocationExecutionRenaming` uses the
concrete allocation-refinement API to transfer scalar results, caller-memory prefixes, a complete
method contract and named exceptions through nested calls followed by dynamic allocation, including
a child that reads its initialized numeric local and nonzero private homes before, between and after
retained declarations. A generic theorem covers every `InitializerFits` kind/value and arbitrary
well-formed caller memory with bounded statics; a concrete checked read observes the private
initializer's bytes. It independently checks different source/target allocation counters and rejects
changed retained initializers, wrong initializer kinds, overflowing bytes, aggregate lengths,
unspecified vectors, invalid spans, unchanged local operands, changed call targets and an exhausted
stack quota. Allocation-renaming proofs reuse checked step equations, and IntegerMath groups
boundary proofs without changing their final statements. See the measured compilation and proof-work
reductions in [Proof work measurements](performance/ProofWork.md). The extracted-loop suite checks
universal countdown termination, NOP/reordered variants, runtime comparisons,
incorrect/nondecreasing loop rejection, a counted loop composed through its helper's contract and
reused for a reimplemented helper, a loop that returns or propagates its helper's named exception, a
buffer fill proved as a sequence property, feature selection, infinite-loop fuel exhaustion,
backward switch and malformed-input rejection.

`Tests.LoopOutcome` derives the normal-only loop induction, loop call and `Ensures` as the `none`
instances of the outcome rules, and proves that unsupported execution, invalid state, fuel
exhaustion, normal return and a different exception never satisfy an expected loop exception.

`Tests.ContractConsequence` derives public method and outcome contracts from proved internal ones
without re-executing the callee, composes callers through the derived contracts, and proves that an
unjustified stronger postcondition, a weaker precondition, a smaller footprint and a changed
exception type each fail both the refinement premises and the derived contract on a concrete input.
Its forwarders inherit their callees' contracts through `MethodContract.Holds.forward` and
`forward_out`: `Sum`, `SumSwapped` and `AddFrom` pass `AddTo` its arguments in order, swapped and
reversed; `SumDiscard` inherits `AddFlag`'s contract with an uninitialized out local, and `CopyTo`
inherits `AddFrom`'s with a zeroed local, a callee region footprint inside its own and an `Apart`
fact from the local's freshness; `IsZeroForward`, `IsZeroIgnoring` and `IsZeroSecond` re-narrow
`IsZero`'s boolean, the last two skipping an argument; and `IsSetForward` passes a boolean through a
narrowed load. Rejected are a body whose loads differ, a selection that passes one argument twice, a
result or load outside the narrow range, and two false contracts: `IsZeroSecond` as if it loaded its
first argument, and `IsZeroIgnoring` with a dangling unused argument.

`Tests.InvocationCertificates` builds invocation certificates from a computed invocation and from a
computed run, keeps them through a certified contract and its refinement, proves a caller whose
postcondition is the visited-state clause of its callee's certificate, through a certified callee
and through a callee without a precondition, and refutes a contract from the returned values of a
computed run. `Tests.ValidCallTransport` carries `ValidCall` through writes, frame entry, memory
kept below a watermark and a call confined apart from the inputs, and shows that a confined call
over an input can revoke its read authority.

`Tests.ConfinedFootprints` checks footprint coverage and preservation through `Confined`.
`Tests.LocalSnapshots` keeps vector, int32, byte and narrow locals known across stores, overwrites,
writes elsewhere and confined calls, and steps a load from a snapshot fact. `Tests.BufferContents`
checks typed buffer contents: fills and in-place transforms of any length, unchanged neighbouring
bytes and sibling slices of one allocation, a producer that extends its prefix while its room stays
unreadable, empty buffers at invalid and sentinel positions, and rejection of uninitialized,
past-end, overlapping, unjoined and stale contents.

`Tests.ProfileContract` proves a contract for a method that tests AVX2 once, under x86-64-v3, and
carries it to x86-64-v4, to v3 without 256-bit acceleration and to every profile with AVX2 on. A
raising method's outcome contract carries over too, in outcome, CLR-named and descriptor-indexed
forms, with agreement decided from the flags the program reads. The baseline profile, with AVX2 off,
fails both the agreement check and the contract, and turning off one of the four flags an AVX-512 DQ
multiply needs fails the check.

`Tests.InstructionEquations` checks that `cil_instruction_equations` states one equation per pc of a
body over two feature flags and a callee index, keeping each feature test as an `if`, and of bodies
with no parameters, with implicit and hypothesis parameters, and composed with `++` and
`List.replicate`; that `cil_lookup` fetches through them from a sealed body; that facts or literal
flags decide the test, in lookups and in a checked run; and that a run proved over the flags binds
two profiles. A body whose length depends on a flag, at its first pc or a later one, is rejected
with nothing declared.

`Tests.InterpreterEquations` checks that each shared equation lemma is stored by its LeanCIL module
rather than rebuilt by the importer, and that a tactic macro naming `CIL.step.eq_def` elaborates.

`Tests.SimdLanes` checks the SIMD lane lemmas as a multi-limb routine uses them: the carry and
borrow cascades built from intrinsic comparison masks reproduce 256-bit sums and differences for
every input. The 512-bit forms cover all eight lane carry-ins and the outgoing carry or borrow;
boundary fixtures propagate across all eight lanes and reject an unshifted generate mask. Broadcast
all-ones and operand-swapped AVX-512 greater-than sources feed the same 256-bit cascade. Tests
include a carry across an all-ones lane where a single repair hop is wrong, and 128-bit sums and
differences follow from their lane carries. Each intrinsic equation (lane add, multiply, equal,
unsigned and signed compare, `MoveMask`, shifts by immediate and by vector count, permute, sum and
even-lane multiply) rewrites a packed or symbolic operand to its lane values, the bitwise lane
projections cover a mask blend, and concrete 256-bit values are checked by kernel evaluation. A
method steps through a shift and an even-lane multiply with those lemmas as facts.

Run the focused Lean targets and extracted-loop suite with:

```sh
lake build CIL Tests.Automation Tests.MethodEmbedding Tests.RetainedNumericLocals Tests.AllocationRenaming Tests.AllocationExecutionRenaming Tests.OutcomeEmbedding Tests.AggregateSetup Tests.Semantics Tests.InterpreterEquations Tests.MethodIdentity Tests.StructuralLabels Tests.DebugNames Tests.MethodContract Tests.ConstructContract Tests.OutcomeContract Tests.Imports Tests.LoopOutcome Tests.ContractConsequence Tests.InvocationCertificates Tests.ValidCallTransport Tests.ConfinedFootprints Tests.LocalSnapshots Tests.BufferContents Tests.Linking Tests.StoreFacts Tests.ProfileContract Tests.InstructionEquations Tests.CodeAt Tests.Segment Tests.SimdLanes
dotnet run --file scripts/Test.cs -- --suite loops
```

The loop suite builds a fresh verification library and performs kernel replay as part of
extracted-loop verification. Use the full test command at the top of this document for the complete
verification suite.

When changing proof tactics or shared contracts, measure fresh elaboration of the library and its
consumers, compiled artifact size, CPU time, peak process memory and kernel replay separately.
Compile identical consumer sources against both revisions and alternate serial runs with prebuilt
dependencies on the same machine. A smaller compiled proof alone does not establish a speed or
memory improvement. Preserve the kernel replay, axiom audits and negative regressions.

## Store view reuse

Stores reuse existing read permissions when they already cover the written range, including coverage
spread across multiple views. The `write_run_equivalent` theorem proves that replacing the previous
always-prepending write preserves any subsequent checked execution: returned values, exact faults,
allocation state, bytes and permissions. `Memory.Equivalent.run` and `.invoke` cover branches,
calls, constructors and frame cleanup.

Run `dotnet run --file scripts/BenchmarkViews.cs -- --stores 128 --repetitions 3` to compare kernel
reduction against the previous write implementation. The defaults are 64 stores and 3 repetitions;
results and per-run logs go to `artifacts/ViewBenchmark`. In a local Windows run with Lean 4.35.0,
128 alternating stores retained 1 view instead of 129; median elapsed time was 5.6 seconds versus
17.7 seconds. These timings include process startup and shared-machine activity; view counts are
checked by kernel reduction.

