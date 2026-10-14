# Adopting LeanCIL

A consuming Lean project can pin the `leancil` package to a specific commit and import its `CIL.*` modules. Use the Lean version in `lean-toolchain`.

## Component boundaries

| Component | LeanCIL provides | The consuming project provides |
| --- | --- | --- |
| CIL execution | Instructions, scalar/vector semantics, calls, branches and finite execution | Selected assembly and entry signature |
| Memory safety | Allocation, initialization, access, lifetime, aliasing and frame proofs | Initial memory, valid caller permissions and input representation |
| Aggregate storage | Byte snapshots, explicit layout validation, field offsets/widths and round-trip proofs | Bridges from domain representations to bytes |
| Verification | Total-correctness predicates, finite execution conditions, symbolic stepping and checked summaries | Mathematical specification and method correctness proof |
| Runtime features | Capability validity, intrinsic semantics and generic profile equivalence | Supported execution configurations and coverage policy |
| Tooling | CIL extraction, fresh proof sessions, theorem audits and artifact identity | Build orchestration and application-specific reporting |

## Aggregate APIs

`Value.aggregate bytes` represents a general reference-free aggregate snapshot. `LocalKind.aggregate size` carries its physical byte size as a `Fin (2^64)`. The snapshot must contain exactly that many bytes.

The checked interpreter supports:

- `loadAggregate size`, `storeAggregate size`, `initAggregate size`.
- `fieldAt offset width`, `fieldAddress offset`, `setFieldAt offset width`.
- Aggregate local loads/stores and by-value snapshots through ordinary local/argument instructions.

The extractor emits validated `AggregateLayout` definitions. Fields use byte offsets, so their order and widths need not be uniform. Explicit overlaps follow the byte-memory semantics.

Fixed-vector helpers remain separate: `vectorArg`, `vectorLocal`, their address/store variants, `lane`, `laneAddress`, `setLane`, `newVector256`, `readVectorHome` and `writeVectorHome`. Their fixed sizes describe vector storage; use the generic aggregate APIs for structs.

## Integration steps

1. Pin a tested LeanCIL commit and align the Lean toolchain.
2. Import reusable modules from `CIL`; keep domain arithmetic, representation, contracts and method coverage in the consumer.
3. Select the compiled assembly by short name or full identity, and supply a unique method selector (C# aliases and an omitted return type are supported). Artifacts record the canonical Cecil signature; ambiguous selectors report every matching signature. Generated `Extracted.methodN` definitions follow the discovered call graph; avoid assigning contracts based only on helper names.
4. Prove the input representation and memory preconditions. Aggregate/vector representation bridges are explicit proof obligations.
5. State the method specification independently of its implementation. Use `CIL.Safety.Ensures` for total correctness with checked memory execution.
6. Prove helper summaries against the generated instructions before using them in symbolic execution.
7. Select hardware profiles explicitly. Reuse proofs across profiles only with the generic profile-agreement theorems.
8. Bind the final named theorem to the compiled assembly using the verification driver, and retain negative and stale-artifact regressions.

## Extension points

General value constructors, address-taking of by-value aggregate arguments, nested/reference-bearing layouts, exception handling, managed object construction and concurrency need additional semantics and proofs before extraction can accept them. Unsupported features currently fail explicitly.

## Extraction inventory

| Classification | Components | Treatment |
| --- | --- | --- |
| Reused | Scalar instruction semantics, execution/fuel lemmas, symbolic execution, SIMD instruction models | Preserved definitions and proofs under `CIL.*` |
| Reused | Allocation, access, initialization, lifetime, live-state and certificate infrastructure in `CIL/Safety` | Preserved generic proof architecture |
| Generalised | Values, local storage, checked instruction memory, frame initialization and their supporting proofs | Aggregate byte snapshots and validated layout sizes replace fixed struct assumptions |
| Generalised | Extractor identity, signatures, types, fields, reachability and Lean emission | Configurable assembly/entry selection; validated explicit layouts; unsupported metadata fails |
| Split | Aggregate memory helpers | General byte-memory operations retained; fixed homes explicitly named as vector operations; domain-specific word constructors excluded |
| Split | Feature availability and profile equivalence | Runtime capability validity and generic agreement retained; application method-profile tables excluded |
| Split | Verification orchestration | Fresh proof sessions, named theorem audits and artifact identity retained in reusable C# tooling; production workflows excluded |
| Excluded | Domain mathematical contracts, limb arithmetic, storage representation, method proofs, specialized summaries, manifests and coverage policies | Belong to the consuming application |

The new aggregate instructions are supported by the allocation-aware interpreter. Existing proofs targeting the earlier interpreter require an explicit migration; no automatic equivalence claim is made. Fixed aggregate helper names have become vector helper names as listed above. Generic memory lemmas now live in `CIL`; consumers must update qualified references and recheck their proofs. Application integration has not been performed or validated.
