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

## Updating existing proofs

Pin a tested revision, rebuild dependencies, and recheck consumer proofs against
it. Use `cil_checked_steps`, `cil_loop_steps` and `cil_loop_finish` for checked
instruction composition; their shared step helper handles definitional
reduction and instruction-equation selection.

For handwritten proofs that repeatedly simplify `run` or the complete `step`
dispatcher, use the composition lemmas in `CIL.Safety.StepComposition` and
`CIL.Safety.CallComposition`, or the checked tactics. Keep branch and memory
hypotheses explicit. Framework invariant proofs can reuse `RunTrace`,
`FrameSetup` and the instruction/step contracts instead of repeating the same
case analysis. See [Writing checked proofs](PROOFS.md) for examples and API locations.

Measure consumer elaboration and kernel replay after upgrading as well as
library artifact size; moving work out of an imported proof can expose repeated
work in its callers. See [proof automation validation](VALIDATION-PROOFS.md#proof-automation)
for the regression coverage.

Lean stores a definition's equation lemmas in the first module that unfolds it,
so every import chain that unfolds the interpreter rebuilds them. Import
`CIL.Safety.Equations` (checked dispatchers, `CIL.binary` and `CIL.unary`) and,
when unfolding the full `CIL.step` dispatcher, `CIL.StepEquations` (about
20 MB) to reuse one copy. `CIL.Safety.SymbolicExecution` imports both, since the
checked-step fallback unfolds `CIL.step`. `CIL.Safety.Execution` provides `CIL.step.eq_def` and
`CIL.Safety.step.eq_def`, which tactic macros cannot generate themselves.

## Extension points

Loops are now extractable: reachable branch and switch backedges use fixed-point feature reachability and stack-join validation. Recursive calls remain unsupported. Regenerate artifacts when upgrading. `CIL.Safety.Loops` provides `LoopState`, `LoopSegment`, `LoopTerminates` and `loop_terminates`; `CIL.Verification.ensures_of_loop` connects successful loop execution and frame setup to total correctness. Proofs supply their own invariant and decreasing measure. The existing instruction-count `executionBound` remains only a candidate budget and is generally insufficient for input-dependent loops.

Reference-bearing layouts, exception handling, managed object construction and concurrency need additional semantics and proofs before extraction can accept them. Unsupported features currently fail explicitly.

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

- `Op.loadScalar width signed` and `Op.storeScalar width` add checked integer-reference access for widths 1, 2, 4 and 8. The earlier `.load64` / `.store64` constructors remain unchanged. Use `CIL.Safety.invoke` for their execution proofs.
- Primitive integer `ldobj` / `stobj` now emit these scalar operations. Primitive `initobj` reuses the checked zero-fill operation `initAggregate` with the validated integer width; its semantics do not require an aggregate operand.
- `Op.switch targets` adds unsigned `i32` jump-table dispatch to both execution models. Consumers matching exhaustively on `Op` must handle the new constructors.
- `sizeof` emits `const32` using validated type metadata. No runtime type inference or new layout oracle is introduced. Regenerate artifacts and recheck consuming proofs after upgrading.

## Integer division and remainder

- `Op.divide signed remainder` represents four CIL encodings. `CIL.IntegerArithmetic` provides the checked bit-vector and scalar operations; `CIL.Safety.invoke` propagates checked results and arithmetic faults.
- `ExecutionFault.arithmetic` carries `ArithmeticFault.divideByZero`, `.overflow` or `.invalidOperands`. Consumers matching faults or instructions exhaustively must handle the new constructors. Successful scalar results still pass the existing value checks and safety invariants.
- Regenerate artifacts: reachable division is now supported, with arithmetic failures distinguished from unsupported instructions. The generic unsupported-instruction fixture now uses array allocation.

## Checked arithmetic

- `Op.checkedArithmetic kind signed` models checked addition, subtraction and multiplication. `CheckedBinaryKind` selects the operation; `checkedBits` and `checkedValues` compute an integer result before applying signed or unsigned bounds.
- Overflow uses the same located `.arithmetic .overflow` fault as division. Regenerate artifacts and update exhaustive instruction matches; no exception-handler support is implied.

## Checked integer conversions

- `Op.checkedConvert width signed unsignedInput` represents the 20 integer checked-conversion encodings. `convertInteger` rejects unsupported widths and operands, checks mathematical bounds, and returns an extended `i32` for 8-/16-bit destinations.
- Native destination encodings use the validated profile width (currently 64). Floating-point input and pointer/reference conversions remain unsupported. Regenerate artifacts and handle the new instruction constructor in exhaustive matches.

## Native integers

- Validated `System.IntPtr` / `System.UIntPtr` signatures, locals and fields use the existing 64-bit scalar and checked storage representation. Primitive type widths, typed memory instructions and `sizeof` admit these tokens under the existing 64-bit profile restriction.
- `conv.i`, `ldind.i` and `stind.i` reuse signed widening and checked eight-byte memory operations. No integer-address dereference or pointer storage is introduced.
- `Op.nativeBinary operation` marks mixed native/int32 arithmetic and comparisons found by control-flow stack-type analysis. `CIL.NativeEvaluation` widens the int32 operand and preserves the original operation's faults or branch target. Consumers matching instructions exhaustively must handle this constructor; use the checked interpreter for these operations.
- Stack joins with incompatible tracked types and native/int64 operand mixtures are rejected explicitly. Regenerate extraction artifacts to include native operand annotations.

## Parameter storage

- `Method.parameterHomes` records the parameter index and storage kind for each assigned or addressed parameter. Extraction maps these parameters to additional private slots after the declared locals. Instruction offsets remain unchanged; `ldarg`, `starg` and `ldarga` share the same home.
- `makeParameterHomes` allocates and initializes these slots on entry. Their allocation IDs join the frame's owned storage and expire on return. Byref parameters use reference roots; taking their address remains unsupported.
- Frame well-formedness, allocation ownership, caller-memory preservation, reference validity, static-world preservation and setup progress include parameter homes.
- `FrameSetupFits` now includes parameter type compatibility. `enterFrame_succeeds` additionally requires valid argument values; invocation already checks this. The specialized numeric/word/unknown frame setup lemmas require `body.parameterHomes = []`.
- Regenerate artifacts to obtain parameter-home metadata and its simplification theorem. Proofs unfolding frame setup may need `makeParameterHomes` in their simplification list.

## Sequential layouts

- `MetadataValidation.AggregateLayout` computes a validated size and field offsets for explicit or sequential primitive-field structs. `Layout` retains its size-returning API; `FieldOffset` is the shared offset lookup used by emission and instruction translation.
- Sequential fields normally have no metadata `FieldOffset`; consumers must use validated computed offsets instead of reading `FieldDefinition.Offset` directly.
- Aggregate bytes, memory instructions and Lean layout bounds theorems are unchanged. Regenerate artifacts for the expanded metadata subset.
- Inline arrays, auto layout, reference fields and floating-point fields remain unsupported. Interop marshalling layouts are not used to infer managed offsets.

### Nested layouts

`AggregateInfo` now retains alignment as well as size and offsets. Recursive layout validation admits nested reference-free structs, rejects cycles and caps nesting depth at 128. `FieldSize` handles primitive, enum and aggregate fields.

`FieldLayout` adds an `aggregate` flag: scalar fields retain the width restriction to 1/2/4/8 bytes, while aggregate fields require a positive width. Every field remains bounded by its containing layout. Update positional field constructors to include this flag, or use named structure fields. Emission includes bounds theorems for reachable nested layouts.

`Op.aggregateFieldAt` and `Op.setAggregateFieldAt` perform checked nested snapshots and stores. Downstream exhaustive opcode matches must handle them. The scalar field instructions retain their previous meaning. Regenerate extraction artifacts before verifying consumers.

### Typed object copies

`CIL.Op.copyObject size` is a new instruction constructor. Downstream exhaustive matches must handle it; checked execution uses existing allocation-aware reads and writes. `CIL.Safety.copyObject_writes_snapshot` provides a generic byte-copy postcondition. Extraction computes the width from validated type metadata; no application-specific copy summaries are required.

### Struct instance calls

`MethodArguments` centralizes CIL argument indexing: struct instance methods receive a managed-reference `this` at index zero, followed by declared parameters. Assigned/addressed parameter homes and native operand analysis use the same indexing for every encoding. Existing Lean argument and call semantics remain unchanged.

Direct `call` instructions may target admitted same-assembly struct instance methods and constructors. Constructor calls require a void result and valid struct storage supplied by the caller. The separate `newobj` path below constructs a new value rather than invoking a constructor on existing storage. Class instances, virtual dispatch and generic declaring types remain unsupported.

### Portable scalar helpers

`Intrinsic.scalar` adds a portable runtime family; downstream exhaustive matches over `Intrinsic` must handle it. Its semantics live in `CIL.ScalarIntrinsics`. Availability and required-feature checks classify this family as profile-independent. The extractor accepts selected exact .NET 10 `System.Runtime` and `System.Memory` signatures; it does not admit arbitrary external calls.

### Struct construction

`Op.newAggregate constructor argc size` constructs an admitted struct through the checked interpreter. Extraction follows the constructor dependency and derives the size from validated layout metadata. Consumers with exhaustive instruction matches must handle the new constructor.

`FrameAction.construct` now carries a `LocalKind` between the temporary reference and memory. Constructor continuation proofs use `loadLocal` and return a `CIL.Safety.Value`; update uses of `ConstructComposition` accordingly. Existing vector construction supplies `.vector256`, while generic struct construction supplies `.aggregate size`. The generic lifetime, allocation, frame-ownership and static-world invariants cover both paths.
## Generic method specialization

Reachable generic methods on admitted non-generic declaring types now produce closed CIL bodies. Artifact manifests record the original definition, metadata token and concrete type arguments; regenerate artifacts with the updated extractor. CIL execution APIs and theorem namespaces are unchanged. Select a non-generic entry whose compiled calls provide the required instantiations.

## Loop facts from the context

`cil_loop_steps`, `cil_loop_finish` and `cil_loop_continue` take an optional fact list and add
the facts the proof context determines (see [loop verification
conditions](PROOFS-STEPPING.md#loop-verification-conditions)). A step equation in the context is
now used whenever its instruction is reached, so a run that stopped at such an instruction to be
crossed by hand continues past it: drop the manual `loop_reaches_next` and the second
`cil_loop_steps`, as `FillWords` does. The `simplifying` form of `bind_entry` gives `entry.frame`
only the binders its layout mentions, such as `entry.frame memory view`; drop the proof arguments
from its uses. `bind_cutpoint` accepts its frame, stack and memory without parentheses.
