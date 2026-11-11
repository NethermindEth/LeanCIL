# Soundness boundary

A verified theorem holds for the extracted program in LeanCIL's formal semantics, under
exactly the theorem's hypotheses. It does not prove that those hypotheses hold in a deployment,
that the specification expresses the intended requirement, or that the CLR implements the model.
A concrete-input theorem is not a universal method contract.

## Trusted components and deployment assumptions

| Component or assumption | Trusted claim | Evidence and limits |
| --- | --- | --- |
| Lean kernel and foundations | Lean 4.35.0 checks proof terms correctly; admitted foundational axioms are `propext`, `Quot.sound` and `Classical.choice`. | [Theorem audit](SOUNDNESS-VERIFICATION.md#theorem-audit); [toolchain pin](../lean-toolchain) |
| CIL and memory semantics | The definitions correspond to the admitted CLR behavior. This correspondence is reviewed; it is not proved against a CLR implementation. | [Execution guarantees](SOUNDNESS-EXECUTION.md#definitions-and-proved-properties); [checked execution](../CIL/Safety/Execution.lean); [specification baseline](SOUNDNESS-SPEC.md) |
| Metadata decoding and extraction | Mono.Cecil and the extractor faithfully decode and serialize the assembly; checks cover only their stated translation families. | [Independent translation evidence](SOUNDNESS-EVIDENCE.md#independently-checked-extraction-evidence); [opcode coverage](OPCODES.md) |
| Referenced assemblies | Each `--reference` DLL is a trusted input exactly like the selected assembly: pinned by identity, MVID and SHA-256 in `identity.json`, and decoded by the same Cecil and extractor code. Lean checks which assembly each body came from; `check` hashes the bytes. | [Pinned referenced assemblies](SOUNDNESS-EVIDENCE.md#pinned-referenced-assemblies); [CLI](CLI.md#extract-from-referenced-assemblies) |
| Runtime helpers and intrinsics | Each admitted external method implements the modeled behavior on the selected runtime and architecture. | [Runtime assumptions](SOUNDNESS-RUNTIME.md#runtime-assumptions); [intrinsic inventory](SIMD.md); [argument guards](SOUNDNESS-RUNTIME.md#argument-guards); [runtime bindings](../Extractor/RuntimeModels.cs) |
| Deployment profile | The actual runtime version, architecture, endianness and feature availability satisfy the selected profile. | [Runtime profiles](RUNTIME-PROFILES.md); [profile validation](../CIL/Features.lean) |
| Initial memory and authority | Caller-supplied allocations, live references, byte contents, initialization and access authority accurately describe reality, and each string literal the caller binds names the object `ldstr` loads for that text. | [Argument storage](SOUNDNESS-RUNTIME.md#argument-storage); [memory model](../CIL/Safety/Memory.lean) |
| Class instances | A caller-supplied object reference names one live instance of the runtime type its allocation records, and CLR reference identity is allocation identity: the garbage collector neither merges, splits nor reuses an instance a proof can still observe, and frees an instance only once nothing can reach it. Each field of an instance holds the bytes the model's field layout gives it, at whatever address CoreCLR actually uses, and each class-typed field the instance last stored into it, whatever address the collector moves that instance to, and no other thread reads or writes an instance reachable from the arguments, or one the method creates, during the call. Every caller-supplied object, of an admitted class or one outside the model, records its complete chain of base classes under the extractor's type names. A caller-supplied array of class references records its actual element class, which the covariance check of `stelem.ref` relies on, and each of its elements the reference the CLR holds there; that element class is a class and is never an interface, since only class element types are admitted. A value-array field of a caller-supplied instance holds null or the origin of the whole runtime array: offset 0 of a heap allocation exactly as long as that array of the field's element type. | [Class instances](SOUNDNESS-RUNTIME.md#class-instances); [arrays of class references](SOUNDNESS-RUNTIME.md#arrays-of-class-references); [value-array fields](SOUNDNESS-RUNTIME.md#value-array-fields); [heap objects](../CIL/Safety/HeapObjects.lean) |
| Resource availability | The runtime can allocate the modeled heap arrays, can allocate every class instance and array of class references a successful run creates (`Memory.heapBudget` bytes in the model's object layout, charged without reclaim), and provides justified stack capacity, including for the frames of acyclic call chains. Model success does not exclude real resource exhaustion; an instance or array over budget is the model fault `allocationFailure` and is never a CLR `OutOfMemoryException`. | [Array and runtime limits](SOUNDNESS-RUNTIME.md#runtime-assumptions); [stack allocation](SOUNDNESS-EXECUTION.md#definitions-and-proved-properties) |
| Static initialization | Explicit initialization assumptions hold, and admitted readonly storage is not mutated by unmodeled code. | [Static-value assumptions](SOUNDNESS-RUNTIME.md#runtime-assumptions); [static evidence](../CIL/Extraction/StaticValues.lean) |
| Verifier and artifact binding | The verifier, filesystem, SHA-256, process execution and toolchain selection bind the checked theorem to the intended input bytes. | [Artifact integrity](SOUNDNESS-VERIFICATION.md#artifact-integrity); [verifier](../scripts/Verification.cs) |
| Imported contracts | The selected implementation, interface pins and contract hypotheses are the ones used by the caller. | [Published contracts](SOUNDNESS-EVIDENCE.md#caller-proofs-and-published-library-contracts); [full implementation verification](FULL_VERIFICATION.md) |
| Specification | The chosen theorem, quantifiers and preconditions express the property the user needs. | [Writing proofs](PROOFS.md); [contract interfaces](CONTRACT-INTERFACES.md) |

## Verification guarantees

The normal verifier regenerates and checks extraction identity, compiles the proof, replays it
through the kernel, and audits the theorem's dependencies. Unexpected axioms, missing evidence,
failed builds and exhausted proof resources are failures. Hash equality establishes identity,
not semantic correctness. Cached artifacts require independent authenticated provenance.
A certified library that CI reuses is trusted because our own CI produced it and kernel-replayed
every module, and its bytes match the manifest digest that run logged. It is replayed again unless
GitHub metadata shows the producer ran reviewed code: a push on main, or a PR into main that left
the workflow, scripts and build files as its base had them.
A library built in the current run, or downloaded with a release, is replayed.
On a machine with no whole library cached, a single-file proof may be checked against a closure
entry instead: only the framework modules its imports reach, each replayed, under a key and
receipt that name exactly those modules. The certificate records that key and the module list,
the entry holds no other framework source, and nothing but single-file verification reads it;
see [stage progress](CLI.md#stage-progress).

Checked execution tracks allocation identity, lifetime, bounds, permissions, initialization and
alignment. Its successful executions satisfy the proved preservation properties. Named runtime
exceptions are distinct from unsupported instructions, invalid states and fuel exhaustion.
An expected-exception proof cannot use these model failures as its witness.

A virtual call dispatches over a closed world: its table lists every class of the extraction's
assemblies that derives from the slot's class, each with the body the CLR would select. Lean
re-resolves every entry from the decoded class catalog and checks that no catalog class is missing.
An instance of any other class, such as one loaded from an assembly outside the extraction, is
the model failure `outsideDispatchTable`, so a theorem that concludes a return or a named
exception has ruled such receivers out. No deployment assumption is needed for this premise:
the caller's hypothesis about the receiver's runtime type must exclude them, or the proof fails.
See [virtual dispatch](SOUNDNESS-EXECUTION.md#virtual-dispatch).

Extraction reads compiled CIL; it does not prove that the source compiler preserves a source-level
specification. JIT correctness, hardware correctness, concurrent interference, GC internals and
arbitrary runtime versions remain outside the guarantee.

## Detailed evidence

The [runtime-call catalog and compiler corpus](COMPILER-COVERAGE.md) make changes to the
admitted API surface and compiler-sensitive patterns visible. Their finite probe domain does
not establish correspondence with the CLR.

- [Specification baseline](SOUNDNESS-SPEC.md): ECMA-335 (2012) plus the tracked augments.
- [Execution and preservation](SOUNDNESS-EXECUTION.md): frames, allocation, embeddings and composition.
- [Runtime and storage](SOUNDNESS-RUNTIME.md): external models, layout and deployment assumptions.
- [Extraction and contracts](SOUNDNESS-EVIDENCE.md): independently checked evidence and imported proofs.
- [Verification and integrity](SOUNDNESS-VERIFICATION.md): kernel audit, authenticated artifacts and reuse.
