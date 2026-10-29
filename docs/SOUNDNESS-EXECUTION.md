# Execution model and preservation guarantees

## What is defined and proved

`CIL.Safety.run` and `CIL.Safety.invoke` execute methods over allocation-aware memory.
Value-only instructions delegate to `CIL.step`. Memory operations and frame transitions use
checked rules; unknown instructions cannot fall through to unchecked accesses.

Successful execution excludes model faults on its path. Under their stated initial premises,
the library proves well-formedness, allocation extension, live values, frame ownership and expiry,
caller-memory preservation and static-world consistency. `InvocationCertificate` packages these
properties with execution. Valid initial storage, references and authority are caller obligations.

| Claim | Required evidence | Limit |
| --- | --- | --- |
| Total correctness | `Ensures`: precondition, terminating checked invocation, postcondition | A concrete-input theorem is not universal correctness. |
| Loop termination | Invariant preservation, decreasing natural measure, checked iteration segments | Control-flow validation and fuel exhaustion do not prove termination. |
| Helper composition | Proved `MethodContract` or `OutcomeContract`, with its premises satisfied | Existential helper fuel does not eliminate contract obligations. |
| Named exception | Actual `.thrown E` execution, or the explicit `RaisesCLR` mapping | Unsupported instructions, invalid state, fuel exhaustion and general memory faults are not witnesses. |
| Buffer contents | Checked write/readback, sequence predicates and confinement | Readability and write authority are separate. |

`RaisesCLR` and `OutcomeContract.HoldsCLR` also name arithmetic overflow and divide-by-zero.
Handlers, exception-object identity, unwinding and post-throw memory are outside the model.
Outcome loop rules require preservation and decrease only for continuing iterations; exits must
establish the specified normal or exceptional outcome from the initial state.

[Countdown](../Examples/Proofs/Countdown.lean) proves termination and zero return for all uint inputs
under its empty-memory precondition. [FillWords](../Examples/Proofs/FillWords.lean) proves a fill for
every admitted count, final sequence contents and confinement. Neither is a runtime cost claim.

### Allocation and access

Memory tracks identity, layout, lifetime, initialized bytes, permissions and end sentinels.
Identities are never recycled. End pointers grant no byte access. Aliases share backing bytes;
readonly references restrict writes through that view, not writes through other authorized aliases.

`localloc` storage belongs to the current frame and expires at return. Return checks reject
escaping references and spans. The raw `localsinit` bit selects zeroed or unreadable initial bytes.
A zero-size request returns null. Nonempty reservations round to 16 bytes and charge
`Memory.stackLimit`: default zero, at most 65,536 bytes per activation. A positive quota requires
a deployment premise; it excludes ordinary frames, calls and probing overhead and does not prove
physical stack availability. Quota failure is a model fault, not automatically a CLR exception.
The conventions assume the admitted .NET 10
[x64](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/jit/codegenxarch.cpp) and
[ARM64](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/jit/codegenarm64.cpp) implementations.
Heap-array lifetime and resource assumptions are in [runtime storage](SOUNDNESS-RUNTIME.md).

## Aggregate storage

Aggregates are reference-free byte snapshots with initialization masks. Homes allocate their
validated size; stores reject size mismatches. Fields use validated offsets and types. Loads
do not invent initialized values. Sequential/explicit layouts are bounded by 65,536 bytes;
explicit overlap follows byte semantics. Layout proofs validate emitted bounds and consistency,
not CLR correspondence. See [layout assumptions](SOUNDNESS-RUNTIME.md#sequential-struct-layout).

## Method-body embedding

`MethodEmbeds` checks execution metadata, static descriptors and live instructions under a PC map.
Entry, branch/call targets and resumable fallthroughs must match. Expected `.unsupported` locations
constrain no actual code and cannot occur on a successful expected path. Even a live inserted `nop`
is outside this exact relation. `cil_embed` computes a candidate map; the kernel checks every field.

`ProgramRefines` transfers successful runs with the same fuel and final memory. Outcome variants
transfer named throws with relocated PCs, preserving method and exception. They do not transfer
fuel exhaustion, unsupported-operation, invalid-state, memory or arithmetic faults.

### Dead locals

| Relation | Preconditions | Guarantee and limit |
| --- | --- | --- |
| `MethodEmbedsDeadLocals` | Trailing null/unmodeled reference or bounded span slots; matching retained local/kind lengths; no parameter homes; opaque slots stay retained | Same memory, results and named throws. No invocation-certificate transfer or general `ProgramRefines` composition. |
| `AllocationRefinement` | Checked local renaming/initializers; ordinary frames without opaque/vector/parameter argument homes; well-formed memory and bounded statics | Scalar results and caller-prefix preservation; named throws require valid arguments. Fresh identities/counters and arbitrary reference-valued postconditions need not match. |

Allocation refinement proves the complete dispatcher simulation with injective retained-allocation
and activation mappings. Extra private homes lie outside the mapped image. Contract transport also
requires scalar result encoding and postcondition stability under the caller-prefix relation;
confinement follows from execution. See [binding and transport](PROOFS-BINDING.md).

## Shared proof contracts and reduction

`RunTrace`, `FrameSetup` and instruction contracts expose proved execution and preservation facts.
Checked stepping, `rfl`, simplification and optional proved summaries produce kernel-checked terms.
Failed summaries install no declarations. A `VC` does not discover invariants or specifications.
[Loop scaffolding](PROOFS-BINDING.md#generate-loop-entry-and-cutpoint-scaffolding) supplies checked
setup equations; invariant preservation, termination and specification remain proof obligations.
