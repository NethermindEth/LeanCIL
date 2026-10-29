# Soundness boundary

A verified theorem holds for the extracted program in LeanCIL's formal semantics, under
exactly the theorem's hypotheses. It does not prove that those hypotheses hold in a deployment,
that the specification expresses the intended requirement, or that the CLR implements the model.
A concrete-input theorem is not a universal method contract.

## Trusted components and deployment assumptions

| Component or assumption | What remains trusted | Evidence and limits |
| --- | --- | --- |
| Lean kernel and foundations | Lean 4.35.0 checks proof terms correctly; admitted foundational axioms are `propext`, `Quot.sound` and `Classical.choice`. | [Theorem audit](SOUNDNESS-VERIFICATION.md#theorem-audit); [toolchain pin](../lean-toolchain) |
| CIL and memory semantics | The definitions correspond to the admitted CLR behavior. This correspondence is reviewed, not proved against a CLR implementation. | [Execution guarantees](SOUNDNESS-EXECUTION.md#what-is-defined-and-proved); [checked execution](../CIL/Safety/Execution.lean) |
| Metadata decoding and extraction | Mono.Cecil and the extractor faithfully decode and serialize the assembly; checks cover only their stated translation families. | [Independent translation evidence](SOUNDNESS-EVIDENCE.md#independently-checked-extraction-evidence); [opcode coverage](OPCODES.md) |
| Runtime helpers and intrinsics | Each admitted external method implements the modeled behavior on the selected runtime and architecture. | [Runtime assumptions](SOUNDNESS-RUNTIME.md#runtime-assumptions); [intrinsic inventory](SIMD.md); [runtime bindings](../Extractor/RuntimeModels.cs) |
| Deployment profile | The actual runtime version, architecture, endianness and feature availability satisfy the selected profile. | [Runtime profiles](RUNTIME-PROFILES.md); [profile validation](../CIL/Features.lean) |
| Initial memory and authority | Caller-supplied allocations, live references, byte contents, initialization and access authority accurately describe reality. | [Argument storage](SOUNDNESS-RUNTIME.md#argument-storage); [memory model](../CIL/Safety/Memory.lean) |
| Resource availability | The runtime can allocate the modeled heap arrays and provide justified stack capacity. Model success does not exclude real resource exhaustion. | [Array and runtime limits](SOUNDNESS-RUNTIME.md#runtime-assumptions); [stack allocation](SOUNDNESS-EXECUTION.md#what-is-defined-and-proved) |
| Static initialization | Explicit initialization assumptions hold, and admitted readonly storage is not mutated by unmodeled code. | [Static-value assumptions](SOUNDNESS-RUNTIME.md#runtime-assumptions); [static evidence](../CIL/Extraction/StaticValues.lean) |
| Verifier and artifact binding | The verifier, filesystem, SHA-256, process execution and toolchain selection bind the checked theorem to the intended input bytes. | [Artifact integrity](SOUNDNESS-VERIFICATION.md#artifact-integrity); [verifier](../scripts/Verification.cs) |
| Imported contracts | The selected implementation, interface pins and contract hypotheses are the ones used by the caller. | [Published contracts](SOUNDNESS-EVIDENCE.md#caller-proofs-and-published-library-contracts); [full implementation verification](FULL_VERIFICATION.md) |
| Specification | The chosen theorem, quantifiers and preconditions express the property the user needs. | [Writing proofs](PROOFS.md); [contract interfaces](CONTRACT-INTERFACES.md) |

## What verification establishes

The normal verifier regenerates and checks extraction identity, compiles the proof, replays it
through the kernel, and audits the theorem's dependencies. Unexpected axioms, missing evidence,
failed builds and exhausted proof resources are failures. Hash equality establishes identity,
not semantic correctness. Cached artifacts require independent authenticated provenance.

Checked execution tracks allocation identity, lifetime, bounds, permissions, initialization and
alignment. Its successful executions satisfy the proved preservation properties. Named runtime
exceptions are distinct from unsupported instructions, invalid states and fuel exhaustion.
An expected-exception proof cannot use these model failures as its witness.

The standalone `CIL.invoke` interpreter does not establish checked-memory properties. Until its
consumers are consolidated, memory-safety claims must use `CIL.Safety.invoke` explicitly.

Extraction reads compiled CIL; it does not prove that the source compiler preserves a source-level
specification. JIT correctness, hardware correctness, concurrent interference, GC internals and
arbitrary runtime versions remain outside the guarantee.

## Detailed evidence

- [Execution and preservation](SOUNDNESS-EXECUTION.md): frames, allocation, embeddings and composition.
- [Runtime and storage](SOUNDNESS-RUNTIME.md): external models, layout and deployment assumptions.
- [Extraction and contracts](SOUNDNESS-EVIDENCE.md): independently checked evidence and imported proofs.
- [Verification and integrity](SOUNDNESS-VERIFICATION.md): kernel audit, authenticated artifacts and reuse.
