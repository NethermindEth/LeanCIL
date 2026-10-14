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

## Narrow integer API changes

- `NarrowKind` records signed/unsigned eight- and sixteen-bit storage. Newly extracted narrow locals use `LocalKind.narrow`; the older restricted `LocalKind.byte` remains available for existing handwritten models.
- `Op.arg`, `Op.local`, `Op.setLocal` and `Op.ret` have optional narrow annotations, defaulting to `none`. Existing constructor expressions retain their previous meanings; pattern matches must account for the additional argument. Extracted annotations are derived from validated signatures and local metadata.
- `Op.fieldAt` and `Safety.loadValue` have an additional signedness argument, defaulting to `false`. Two-byte fields are now admitted. Checked-read and access-requirement lemmas cover either signedness.
- `load_numeric_local`, `store_load_numeric_local` and `step_load_numeric_local` return `localResult kind value`, which includes truncation and extension for narrow homes. It reduces to the original value for existing non-narrow kinds. Consumers proving identity readback for narrow storage must establish that the value is already in the representable range.
- Argument-equivalence premises now quantify over the narrow annotation as well as the argument index.
- Unary arithmetic uses `CIL.unary`, alongside `CIL.binary`; proofs that explicitly unfold instruction internals may need to unfold this helper. Regenerate extraction artifacts and rerun proofs when adopting this version.

## Primitive memory and switch additions

- `Op.loadScalar width signed` and `Op.storeScalar width` add checked integer-reference access for widths 1, 2, 4 and 8. The earlier `.load64` / `.store64` constructors remain unchanged. The pure interpreter rejects the new memory operations; use `CIL.Safety.invoke` for their execution proofs.
- Primitive integer `ldobj` / `stobj` now emit these scalar operations. Primitive `initobj` reuses the checked zero-fill operation `initAggregate` with the validated integer width; its semantics do not require an aggregate operand.
- `Op.switch targets` adds unsigned `i32` jump-table dispatch to both execution models. Consumers matching exhaustively on `Op` must handle the new constructors.
- `sizeof` emits `const32` using validated type metadata. No runtime type inference or new layout oracle is introduced. Regenerate artifacts and recheck consuming proofs after upgrading.

## Integer division and remainder

- `Op.divide signed remainder` represents four CIL encodings. `CIL.IntegerArithmetic` provides the checked bit-vector and scalar operations; the original pure interpreter exposes their successes through `Option`.
- `ExecutionFault.arithmetic` carries `ArithmeticFault.divideByZero`, `.overflow` or `.invalidOperands`. Consumers matching faults or instructions exhaustively must handle the new constructors. Successful scalar results still pass the existing value checks and safety invariants.
- Regenerate artifacts: reachable division is now supported, with arithmetic failures distinguished from unsupported instructions. The generic unsupported-instruction fixture now uses array allocation.

## Checked arithmetic

- `Op.checkedArithmetic kind signed` models checked addition, subtraction and multiplication. `CheckedBinaryKind` selects the operation; `checkedBits` and `checkedValues` compute an integer result before applying signed or unsigned bounds.
- Overflow uses the same located `.arithmetic .overflow` fault as division. Regenerate artifacts and update exhaustive instruction matches; no exception-handler support is implied.
