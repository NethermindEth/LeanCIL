# Extraction and contract evidence

## Independently checked extraction evidence

`TranslationValid rawLayouts computedLayouts methodEvidence imports program` checks one record
per emitted method in program order. The verifier kernel-replays and structurally audits
`Extracted.translation_valid`; an unrelated theorem, non-theorem or different program/import table
cannot substitute for it.

| Evidence | Independently checked relation | Remaining assumption or limit |
| --- | --- | --- |
| Layouts | Recompute layouts from raw fields, packing and size; check required use sites and bounds | Faithful metadata/serialization and runtime layout correspondence |
| Specialization | Substitute closed method/owner arguments through signatures, locals, operands and calls; preserve control flow | Faithful raw definitions and admitted constraints |
| Feature flow | Entry, transfers, joins, required successors, reachable mask and feature-dependent operations | No complete concrete CLI simulation for every opcode |
| Scalar flow | Complete stack kinds, raw maximum stack, joins/backedges, call arguments/results, homes and returns | Unknown types remain opaque; decoding is not proved |
| Scalar translations | Exact literal values, arithmetic, comparisons, conversion flags and branch targets | Other operations require specialized checks or retain stack-effect fallback |
| Managed/imported calls | Target slot, scoped identity, full signature, argument count, receiver and result | An import slot does not prove its implementation contract |
| Constrained calls | Resolve serialized interface/override declarations to the emitted closed direct target | Complete metadata serialization; no general vtable/boxing model |
| Static values | Checked execution yields emitted bytes without circular reads of the values being justified | Initializer recognition and deployment initialization/immutability |

Exact scalar matching covers integer literals, wrapping/checked add/subtract/multiply, signed and
unsigned divide/remainder, bitwise operations, shifts, negation, integer comparisons, admitted integer
conversions and all short/long compare-and-branch encodings. Literal ranges and high-bit-set int64
values, conversion width/signedness/checkedness and exact branch targets cannot pass by stack effect
alone. Non-covered raw opcodes cannot emit these scalar operations, except feature-bound type-test
words and size constants bound to exact primitive/vector widths or validated layouts.

Mixed native/int32 operations require the exact `nativeBinary` wrapper; homogeneous operands forbid
it. Native/int64 arithmetic mixtures are rejected. The 64-bit representation interchange at homes
and returns does not justify arithmetic interchange. Native shift counts use their low 32 bits;
the normalization theorem does not establish behavior on arbitrary CLI implementations.
See [runtime assumptions](SOUNDNESS-RUNTIME.md#runtime-assumptions).

### Folded instruction patterns

A fold applies only to its recognized raw sequence with checked entry edges. Different compiler
output can lose admission without invalidating a theorem over an already admitted program.

| Pattern | Required binding | Limit |
| --- | --- | --- |
| Closed `typeof` equality/inequality calls and reference-comparison branches | Exact type handles, runtime helper identities, substituted types, result and selected target; all encoded targets validated and no branch into the interior | Forwarding/scoped identity ambiguities, decorated names and arbitrary runtime `System.Type` use remain unsupported. Reference comparison relies on [CoreCLR runtime type equality](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Type.cs) and [GetTypeFromHandle](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/System.Private.CoreLib/src/System/Type.CoreCLR.cs). |
| `throw new E(...)` | Allowlisted type/constructor, permitted literal/null arguments and final throw; no branch into the interior | No exception-object identity, observable constructor effects, handlers or resource-exhaustion model. |
| `ldnull; throw` | Adjacent operand-free null load and throw, bound to `System.NullReferenceException`; no branch into the throw | No general exception-object evaluation or handlers. |
| Single-use span receiver | Exact local uses and permitted Length/Item receiver sequence; protected entry edges | No escaping or aliased receiver addresses. |
| In-place span constructor | Exact receiver/argument positions, constructor identity, element layout/width and capability | Unrecognized argument expressions and interior branch entries are rejected. |

The [compiler corpus](COMPILER-COVERAGE.md) checks admission changes, not compiler correctness or
every possible folded pattern. The runtime-call inventory does not count these folds.
[OPCODES](OPCODES.md) records the admitted forms. Metadata decoding, raw-input fidelity, static-data
serialization and runtime-helper correspondence remain trusted even when evidence validates.

## Negative evidence

Direct Lean mutations exercise validators independently of hashes/regeneration: scalar meanings,
stack kinds/joins, layouts, homes, generic substitution, pruning, call slots and folds. Positive
controls establish that fixtures reach the intended obligation. See [validation](VALIDATION-COVERAGE.md).
Wrong-addition has an execution witness and an all-successful-fuel refutation; bounds/lifetime
examples use `invoke_fault_refutes_success`. A failed positive proof or resource exhaustion alone
is not a semantic counterexample.

## Caller proofs and published library contracts

Ordinary caller theorems are conditional:
`forall linked, Links Extracted.program linked -> Extracted.ImportsHold linked -> claim linked`.
Canonical predicates and scoped identity/profile pins bind assumptions to selected interfaces.
Deployment must supply the exact implementation bytes and an implementation satisfying those
contracts. A false or unsatisfiable imported contract can make a caller theorem vacuous.

Every supplied interface module is kernel-replayed. The canonical contract-closure audit includes
definition values, theorem/inductive types, constructors and computational recursor rules. It
rejects custom axioms, sorry, unsafe/partial declarations, free variables and missing opaque values.
Normalization removes binder names/metadata, normalizes universe binders and stops at pinned
framework/toolchain identities.

Ordinary caller verification accepts the implementation-to-contract assertion from published
certification; it does not reprove the implementation. Sidecar/DLL hashes identify bytes, not
publisher authenticity. Theorem/statement digests are provenance records. `--force-full-verify`
rechecks reachable proof bundles and composes them with the caller. Those sources execute Lean
elaborator code with verifier privileges; untrusted bundles need isolated, read-only, network-free
execution. See [full verification](FULL_VERIFICATION.md).

Initialization premises are bound by assembly, type and profile, checked against extraction and
propagated through dependencies into reports. They identify assumptions, not evidence that a CLR
initializer ran. Constructor-derived exported field values and forced-full initialization premises
are unsupported. Reference-only authoring checks do not issue deployment certificates.

## Typed import metadata

`LayoutProjectionValid` and `ImportedLayoutsValid` bind closed generic identities and admitted byref
aggregate layouts: raw catalog, selected entries, nested reindexing, computed layouts, uniqueness
and signature coverage. Extraction also compares the pinned DLL metadata. These checks do not
verify Cecil or remove runtime assumptions. See [typed imports](TYPED-IMPORTS.md).

## Reference observations

Truth tests and equality check formation/lifetime without reading bytes or granting authority.
Same-allocation equality uses offsets. Different-allocation interiors are distinct; comparisons
involving end pointers across allocations are unsupported because adjacent addresses may coincide.
Pointer difference and unsigned ordering require a single live allocation and assume a contiguous,
non-wrapping runtime address interval. Native displacement arithmetic retains provenance and readonly
restrictions; no ordering between allocation bases is inferred.

Object `ldnull` has a distinct scalar-flow kind. Its bounded truth/equality tests do not justify
object storage, parameters/results or comparisons with managed references. The raw literal,
comparison operation and branch target remain exactly checked.

## Exception documentation lint

`lint-exceptions` reports structural potential sites. XML prose is untrusted and not independently
bound to the DLL build. A missing site does not establish exception impossibility. Lint checks no
proof, changes no precondition and issues no verification receipt.
