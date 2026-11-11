# Proof automation regression coverage

<!-- audience: maintainers -->

This page lists, per Lean test module, what the regressions for the proof tactics, contracts,
memory facts and binding check. Read it to find the module that pins a behavior before changing a
tactic or a shared lemma. [Writing checked proofs](PROOFS.md) documents the API these modules
exercise.

## Proof automation

The checked proof APIs share execution traces, frame-setup effects and instruction contracts. Their
validity fields keep the required well-formedness and input validity hypotheses. Checked stepping
rewrites feature and return instructions before using the general dispatcher, and child invocation
matching skips duplicate facts and incompatible literal fuel budgets for abstract programs. The
library and tactic regressions kernel-check the resulting proofs.

### Stepping

- `Tests.Automation` steps an eight-instruction arithmetic method (`arg, arg, const32, shl, add,
  const32, gtu, ret`) with symbolic inputs and arbitrary caller memory using `cil_checked_steps`;
  its axiom assertion permits only `propext` and `Quot.sound`. It checks both paths of a symbolic
  branch from a supplied truth hypothesis, and that failed candidate summaries do not escape their
  transaction. Memory and static dispatch facts keep abstract bitcast results in inferred stacks;
  a conjunction-wrapped store fact exercises the generic dispatch fallback.
- `Tests.FeatureExecution`, imported by `Tests.Automation`, checks enabled and disabled symbolic
  features from caller facts and a concrete feature reduced to its profile field. All three proofs
  use checked invocation and the shared feature evaluator.
- `Tests.StoreFacts` checks symbolic carry and borrow stores whose write facts state `a + b + c`,
  `a - b - c` and the flag words in source form, through both `cil_checked_steps` and
  `cil_contract_steps`. A wrong stored value, address or source memory leaves the run stuck at that
  store, with the exact unsolved goal asserted. It also counts exactly 12
  `trace.CIL.factNormalize` events for a 27-instruction run.
- `Tests.AggregateSetup` and `Tests.Semantics` cover frame setup and interpreter behavior.
- `Tests.InterpreterEquations` checks that each shared equation lemma is stored by its LeanCIL
  module, not rebuilt by the importer, and that a tactic macro naming `CIL.step.eq_def`
  elaborates.
- `Tests.InstructionEquations` checks that `cil_instruction_equations` states one equation per pc
  of a body over two feature flags and a callee index, keeping each feature test as an `if`, and of
  bodies with no parameters, with implicit and hypothesis parameters, and composed with `++` and
  `List.replicate`; that `cil_lookup` fetches through them from a sealed body; that facts or
  literal flags decide the test, in lookups and in a checked run; and that a run proved over the
  flags binds two profiles. A body whose length depends on a flag, at its first pc or a later one,
  is rejected with nothing declared.

### Segments and placement

- `Tests.Segment` composes a 256-bit Add Vector128 eight-op reference prefix and Multiply AVX2
  input stages at positions 44 to 56. Formation, checked loads and stores, intrinsic availability
  and exact permutation semantics are premises. Two vector writes frame all other numeric
  snapshots using separated homes. It rejects aliased homes, hidden indirect writes, changed
  endpoint states, fuel costs and mismatched composition positions or assertions, and placements
  from a different body or end boundary. Each theorem's axiom set is reported.
- `Tests.CodeAt` steps a segment of an abstract body at a symbolic start from the lookups its
  `CodeAt` placement yields, with the error asserted when stepping has no placement. It hands that
  segment theorem the middle of a larger placed region, closes a concrete placement by `rfl` and
  refutes a shifted one and one running past the code. It composes adjacent placements and splits
  them back with `cons_iff`, `take` and `drop`, including past the segment's end, and recovers the
  positional `leading ++ segment ++ tail` form from a nonempty placement alone, proving the bound
  `exists_eq_append` needs by placing the empty segment past the end of a body.

### Embedding and allocation renaming

- `Tests.MethodEmbedding` checks transport of checked executions to actual method bodies with
  mapped program counters, with trailing dead reference and span locals dropped, and beside kept
  opaque vector locals. It checks empty and unmodeled span slots, both mutabilities and every
  supported width. It rejects unsupported widths, scalar span initializers, numeric dead locals
  (in the kernel and in the tactic) and non-trailing dead locals, and reports a changed live
  instruction under dead locals.
- `Tests.OutcomeEmbedding` checks transport of named exceptions and outcome contracts and the
  relocated fault pc, and that changed throws, unsupported execution and fuel exhaustion do not
  transfer.
- `Tests.RetainedNumericLocals` keeps dead numeric declarations before and after a live local,
  transfers exact-memory executions and named exceptions through nested allocating calls, and
  checks that deleting a numeric local changes the allocation watermark and fails ordinary
  embedding.
- `Tests.AllocationRenaming` checks private allocation holes, extending identity maps, relocated
  numeric homes and distinct activation labels.
- `Tests.AllocationExecutionRenaming` uses the concrete allocation-refinement API to transfer
  scalar results, caller-memory prefixes, a complete method contract and named exceptions through
  nested calls followed by dynamic allocation, including a child that reads its initialized
  numeric local and nonzero private homes before, between and after retained declarations. A
  generic theorem covers every `InitializerFits` kind/value and arbitrary well-formed caller
  memory with bounded statics; a concrete checked read observes the private initializer's bytes.
  It checks different source/target allocation counters and rejects changed retained
  initializers, wrong initializer kinds, overflowing bytes, aggregate lengths, unspecified
  vectors, invalid spans, unchanged local operands, changed call targets and an exhausted stack
  quota. Its proofs reuse checked step equations;
  [proof work measurements](performance/ProofWork.md) shows how to time a module and gives
  reference figures.

### Loops

- The `loops` suite checks universal countdown termination, NOP and reordered variants, runtime
  comparisons, rejection of incorrect and nondecreasing loops, a counted loop composed through its
  helper's contract and reused for a reimplemented helper, a loop that returns or propagates its
  helper's named exception, a buffer fill proved as a sequence property, feature selection,
  infinite-loop fuel exhaustion, backward switch and malformed-input rejection.
- `Tests.LoopOutcome` derives the normal-only loop induction, loop call and `Ensures` as the
  `none` instances of the outcome rules, and proves that unsupported execution, invalid state, fuel
  exhaustion, normal return and a different exception never satisfy an expected loop exception.
- `Tests.LoopScaffold` proves a countdown and a span fold over symbolic memory through their
  `LoopFrame`s, naming no frame or span fact, and shows for each that a constant measure fails at
  the decrease goal and an invariant that is not preserved fails at its preservation goal.
- `Tests.LoopFrames` keeps a one-local loop frame, its index load included, across a write to the
  caller's buffer and a call confined to it. A store through the index local's own address and a
  callee whose footprint covers that home are both in the frame's footprint, yet neither the write
  nor the call lemma elaborates on them, since each needs the write in caller storage; the store
  does change the local, so its remembered value is refuted. A two-local frame generated by
  `bind_entry ... allocating` keeps the first local across a store to the second, and the write
  lemma rejects a write through the second's home, which breaks its snapshot. A countdown bound by
  signature through `bind_method` is entered over its body name, cut with the binder form of
  `bind_cutpoint ... matching`, and proved to return zero, so frame setup must unfold the bound
  name to the extracted method. The caller-fact lemmas carry a formed reference, an `Unsafe.Add`
  result and a span's validity and slice from the caller's memory to a frame's, and reject a fact
  about another memory; a slice of a span apart from an entry stays apart, and a stored word
  extends a filled run only right after it, so a word past the next one is refused. A span fold
  that stores its total before each load of the span steps through `cil_loop_recurse` alone, so
  the span's validity reaches the memory a word local's store produces.
- `Tests.LoopDiagnostics` proves a loop over a struct local that calls a method, passing no facts
  to the loop tactics: the gathered frame facts read the struct's fields by value and by address,
  and the call is crossed by its contract.
  - Each loop tactic failure names its pc and instruction: a contract applied before the call, a
    call reached by `cil_loop_steps`, a store with no frame fact at its memory and a path back to
    the cutpoint in another state.
  - A field store outside the layout or of the wrong kind, and a by-value read of a field narrower
    than its value, do not elaborate.
  - A second loop over an int local stamps a caller buffer through a helper whose contract writes
    one word, with no frame lemma, memory or store named: the walk takes the local's stores,
    carries the `Unsafe.Add` result and write authority, and crosses the call with the frame after
    it. Without the `Unsafe.Add` fact the walk stops at the add, naming that fact; a narrowing
    local store stops the walk; without the index bound the call names the footprint side
    condition; an unformed argument names the argument check; and a contract input whose arguments
    differ from the stack names both.
  - At a return `cil_loop_finish` closes the results and confinement and hands back the rest of
    the postcondition.
  - The proofs select what the tactics leave by its obligation tag, so a dropped or renamed tag
    fails the build: `invariant` and `measure` after `cil_loop_recurse`,
    `precondition.stampMethod` for a named callee's open precondition, the third conjunct's
    `postcondition.part3` when the exit facts close the first two, and the numbered invariant
    parts and `measure` of a three-condition head hypothesis. A loop tactic run on that
    precondition names it, and a mistyped `case` is Lean's error, checked to offer the open tags
    whatever its wording.

### Consumer stepping regressions

These proofs check consumer-facing stepping and reduction behavior. They use the public tactics
with symbolic values and memory; they do not replace the checked interpreter with
consumer-specific execution rules.

| Case | Regression |
| --- | --- |
| Supplied store/load facts take priority over generic equations | `Tests.Automation.step_facts_first`, `applied_step_facts_first` |
| Zero, nonzero and literal branch conditions | `Tests.Automation.branch_from_zero`, `branch_from_nonzero`, `literal_branch` |
| Memory operations use their own equations | `Tests.Automation.asRef_fact_stack`, `load128_fact_stack`, `add_fact_stack` |
| Profile facts decide instruction lookup | `Tests.Automation.feature_op_checked`, `Tests.MethodContract.feature_op_contract_steps` |
| Intrinsic evaluation facts normalize the next stack | `Tests.Automation.evaluated_then_stored`, `evaluated_by_applied_hypothesis` |
| Signed, unsigned and loaded-limb comparisons | `Tests.MethodContract.loaded_signed_branch`, `loaded_unsigned_branch`, `loaded_limb_branch` |
| Signed/unsigned widening and both argument orders | `Tests.MethodContract.ordered_widening` |

Each comparison proof has a 2,000-heartbeat budget. The widening proof handles all eight
combinations of signed conversion, scalar position and reversed arguments in 12,000 heartbeats,
using one `cil_contract_steps 3` invocation per case. Its arbitrary continuation preserves the
actual widened stack and memory; it does not merely check that some execution exists. These
budgets detect elaboration regressions independently of machine speed; they are not wall-clock
benchmarks. `ordered_widening_returns` composes that prefix with a concrete suffix which discards
both operands and returns zero, proving that the continuation premise is satisfiable for every
case. The widened value is checked by the prefix theorem.

### Contracts and composition

- `Tests.MethodContract` proves a caller from two contracts without unfolding either callee.
  `Tests/MethodContract.cs` verifies that proof unedited against a build whose helpers are
  reimplemented and renumbered, then refutes each contract with a concrete run on builds with an
  arithmetic or an aliasing bug.
- `Tests.ConstructContract` constructs a 16-byte and a 32-byte struct and reads a field of each
  from the constructors' contracts alone, covers a constructor that assigns one of two fields, and
  rejects a contract without write authority over its storage, a constructor writing outside its
  footprint and an 8-byte readback at a 16-byte site. `Tests/ConstructContract.cs` verifies it
  against a build writing the fields in the opposite order and refutes the contract on a build
  storing a wrong field.
- `Tests.OutcomeContract` proves every outcome of a two-level chain from the callees' contracts.
  `Tests/OutcomeContract.cs` verifies it against the compiled build and refutes the callee's
  contract on builds with an off-by-one threshold or a different exception type.
- `Tests.RuntimeExceptions` proves every mapped CLR exception, refutes wrong names and proves
  unsigned division and remainder by zero for every dividend and caller memory;
  `Tests/RuntimeExceptions.cs` checks each against its compiled C# method.
- `Tests.ContractConsequence` derives public method and outcome contracts from proved internal
  ones without re-executing the callee, composes callers through the derived contracts, and proves
  that an unjustified stronger postcondition, a weaker precondition, a smaller footprint and a
  changed exception type each fail both the refinement premises and the derived contract on a
  concrete input. Its forwarders inherit their callees' contracts through
  `MethodContract.Holds.forward` and `forward_out`:
  - `Sum`, `SumSwapped` and `AddFrom` pass `AddTo` its arguments in order, swapped and reversed.
  - `SumDiscard` inherits `AddFlag`'s contract with an uninitialized out local, and `CopyTo`
    inherits `AddFrom`'s with a zeroed local, a callee region footprint inside its own and an
    `Apart` fact from the local's freshness.
  - `IsZeroForward`, `IsZeroIgnoring` and `IsZeroSecond` re-narrow `IsZero`'s boolean, the last
    two skipping an argument; `IsSetForward` passes a boolean through a narrowed load.
  - Rejected are a body whose loads differ, a selection that passes one argument twice, a result
    or load outside the narrow range, and two false contracts: `IsZeroSecond` as if it loaded its
    first argument, and `IsZeroIgnoring` with a dangling unused argument.
- `Tests.InvocationCertificates` builds invocation certificates from a computed invocation and
  from a computed run, keeps them through a certified contract and its refinement, proves a caller
  whose postcondition is the visited-state clause of its callee's certificate, through a certified
  callee and through a callee without a precondition, and refutes a contract from the returned
  values of a computed run.
- `Tests.ValidCallTransport` carries `ValidCall` through writes, frame entry, memory kept below a
  watermark and a call confined apart from the inputs, and shows that a confined call over an
  input can revoke its read authority.
- `Tests.Imports` proves `Root` against an imported `AddTo`, discharges it for one appended
  implementation, shows the unlinked program faults at the import's call, and composes an imported
  raising `Percent`.
- `Tests.Linking` links an `AddTo` library whose entry calls its own relocated `Sum` helper and a
  `Percent` library whose raise reaches `Root` through two relocated calls.
- `Tests.ProfileContract` proves a contract for a method that tests AVX2 once, under x86-64-v3,
  and carries it to x86-64-v4, to v3 without 256-bit acceleration and to every profile with AVX2
  on. A raising method's outcome contract carries over too, in outcome, CLR-named and
  descriptor-indexed forms, with agreement decided from the flags the program reads. The baseline
  profile, with AVX2 off, fails both the agreement check and the contract, and turning off one of
  the four flags an AVX-512 DQ multiply needs fails the check.

### Memory facts

- `Tests.ConfinedFootprints` checks footprint coverage and preservation through `Confined`.
- `Tests.LocalSnapshots` keeps vector, int32, byte and narrow locals known across stores,
  overwrites, writes elsewhere and confined calls, and steps a load from a snapshot fact.
- `Tests.BufferContents` checks typed buffer contents: fills and in-place transforms of any
  length, unchanged neighbouring bytes and sibling slices of one allocation, a producer that
  extends its prefix while its room stays unreadable, empty buffers at invalid and sentinel
  positions, and rejection of uninitialized, past-end, overlapping, unjoined and stale contents.
  It also composes two calls' `MemoryBelow` facts and refutes that composition without the first
  call's watermark growth.
- `Tests.AggregateFields` checks the struct field laws on a 12-byte word-and-int layout, steps a
  field store and a later load through a remembered struct local, and keeps a remembered struct
  local exact beside a word local. An overlapping explicit layout passes `Valid` but fails
  `Disjoint`, its store changes the neighbouring field, and neither the layout law nor the
  snapshot store elaborates on it; a store that straddles both fields changes both values and is
  apart from neither.
- `Tests.MemorySpanExecution` checks the `Vector128` byte loads and stores at an offset, across
  the end of an allocation and through a readonly reference.

### SIMD lanes

`Tests.SimdLanes` checks the SIMD lane lemmas as a multi-limb routine uses them:

- The carry and borrow cascades built from intrinsic comparison masks reproduce 256-bit sums and
  differences for every input. The 512-bit forms cover all eight lane carry-ins and the outgoing
  carry or borrow; boundary fixtures propagate across all eight lanes and reject an unshifted
  generate mask. Broadcast all-ones and operand-swapped AVX-512 greater-than sources feed the same
  256-bit cascade. One case carries across an all-ones lane where a single repair hop is wrong,
  and 128-bit sums and differences follow from their lane carries.
- Each intrinsic equation (lane add, multiply, equal, unsigned and signed compare, `MoveMask`,
  shifts by immediate and by vector count, permute, sum and even-lane multiply) rewrites a packed
  or symbolic operand to its lane values, the bitwise lane projections cover a mask blend, and
  concrete 256-bit values are checked by kernel evaluation. A method steps through a shift and an
  even-lane multiply with those lemmas as facts.
- The byte shuffle is pinned on concrete vectors for bit-7 zeroing, half isolation and 32-byte
  reversal, which mutants that ignore bit 7 or cross halves fail.
- The AES round steps reproduce round 1 of the FIPS-197 example cipher, which a reversed
  ShiftRows, an unreduced MixColumns and an AESE that adds its key after SubBytes fail.
- REV64, the two-table quadword permutation, signed lane comparison and 32-bit lane creation are
  pinned on vectors that a whole-vector byte reversal, a bit-3 table select, an unsigned
  comparison and a reversed lane order fail.

### Running these checks

Build the focused Lean targets and run the extracted-loop suite with:

```sh
lake build CIL Tests.Automation Tests.MethodEmbedding Tests.RetainedNumericLocals Tests.AllocationRenaming Tests.AllocationExecutionRenaming Tests.OutcomeEmbedding Tests.AggregateSetup Tests.Semantics Tests.InterpreterEquations Tests.MethodIdentity Tests.StructuralLabels Tests.DebugNames Tests.MethodContract Tests.ConstructContract Tests.OutcomeContract Tests.Imports Tests.LoopOutcome Tests.ContractConsequence Tests.InvocationCertificates Tests.ValidCallTransport Tests.ConfinedFootprints Tests.LocalSnapshots Tests.AggregateFields Tests.LoopFrames Tests.LoopDiagnostics Tests.BufferContents Tests.Linking Tests.StoreFacts Tests.ProfileContract Tests.InstructionEquations Tests.CodeAt Tests.Segment Tests.SimdLanes
dotnet run --file scripts/Test.cs -- --suite loops
```

The `loops` suite builds a fresh verification library and performs kernel replay as part of
extracted-loop verification. [Validation](VALIDATION.md) lists every suite and the full command.

When changing proof tactics or shared contracts:

- Measure fresh elaboration of the library and its consumers, compiled artifact size, CPU time,
  peak process memory and kernel replay separately.
- Compile identical consumer sources against both revisions and alternate serial runs with
  prebuilt dependencies on the same machine.
- Do not take a smaller compiled proof alone as a speed or memory improvement.
- Keep the kernel replay, axiom audits and negative regressions.

## Binding and transport

These checks back [binding and transport](PROOFS-BINDING.md).

- `Tests.MethodBinding` proves a body binding with `cil_body` and pins the diagnostic for a
  differing instruction, a differing local, an index past the program and a `Method = Method`
  goal.
- `Tests.MethodIdentity` covers the signature diagnostics, and `Tests/MethodIdentity.cs` verifies
  one unedited proof against two builds with different method numbering.
- `Tests.StructuralLabels` covers the label diagnostics, and `Tests/StructuralLabels.cs` verifies
  one unedited proof against a build with a statement inserted before both loops.
- `Tests.DebugNames` covers local-name scoping and both diagnostics. `Tests/DebugNames.cs` checks
  byte-identical extraction, an unedited proof across an inserted local, and each message with and
  without a PDB. `Tests/ConsumerSymbols.cs` covers consumer packages, batches and PDB-only
  changes.
- `Tests.RegionRun` moves a suffix after inline code to the same suffix after a helper call, one
  pc earlier, and combines `CIL.Embedding.BodyRefines.of_relocated_suffix` with `run_congr_region`
  for a 100-instruction suffix with a symbolic feature profile and callee index, including
  conditional, switch and wrapped native branch targets, at the default heartbeat limit.
- `Tests.ProfileEmbedding` binds one template and one open theorem to three valid profiles,
  including shifted branch targets, without restating the template body for each profile. It
  rejects unresolved flags, incorrect flag and callee values, and a changed branch target.
- `Tests/ProfileTemplates.cs` compiles a real AVX2/SSE4.2 dispatch helper and checks one shared
  proof from `Tests/ProfileTemplatesProof.lean` against three profiles. A fourth extraction
  changes the managed callee numbering through a wrapper entry point. The suite replays the
  generated equations, extraction certificates, bindings and consumer proofs in the kernel, and
  rejects changed flag values, callees, branch targets, instruction equations, stale extraction
  source and incompatible profile-dependent parameter homes.

## Store view reuse

A store reuses existing read permissions when they already cover the written range, including
coverage spread across multiple views. `write_run_equivalent` proves that this write and one that
always prepends a view give the same subsequent checked execution: returned values, exact faults,
allocation state, bytes and permissions. `Memory.Equivalent.run` and `.invoke` cover branches,
calls, constructors and frame cleanup.

`dotnet run --file scripts/BenchmarkViews.cs -- --stores 128 --repetitions 3` compares kernel
reduction of the two writes. The defaults are 64 stores and 3 repetitions; results and per-run
logs go to `artifacts/ViewBenchmark`. For 128 alternating stores the reusing write keeps 1 view
where the prepending write keeps 129; the view counts are checked by kernel reduction. Elapsed
times include process startup and shared-machine activity.
