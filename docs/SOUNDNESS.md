# Soundness boundary

## What is defined and proved

`CIL.Semantics` defines a functional byte-memory execution model, with wrapping bit-vector arithmetic, instruction-level failure, calls and explicit finite fuel. Its memory addresses do not themselves certify physical allocations. Its successful execution theorem is not a memory-safety certificate.

`CIL.Safety.Memory` adds allocation identities, storage kinds, layouts, live/dead state, initialized bytes, read/write views, end sentinels and managed references. Allocation identities increase and are never recycled. `CIL.Safety.Execution` checks every memory/reference instruction and frame transition. It uses the arithmetic interpreter only through the existing value-only whitelist. Unknown operations cannot fall through to unchecked memory operations.

Successful checked execution excludes the model's faults on the executed path. Library theorems establish well-formedness preservation, allocation extension, frame ownership, expiration, caller-memory preservation, valid live values, static-world consistency and running/returned-state invariants. `InvocationCertificate` records successful execution plus these state properties under its stated initial-state premises. Premises such as valid views, well-formed input memory and valid initial references are obligations on callers, not facts inferred from an arbitrary DLL.

`Ensures` describes total correctness of a specified method over a user-supplied precondition and postcondition. A `VC` is a finite execution condition, not a decision procedure that automatically finds loop invariants or arithmetic specifications. The symbolic-execution tactic follows actual generated instructions and optional **proved** summaries. Failed summary elaboration restores the Lean environment and continues raw execution.

## Aggregate generalisation

The checked interpreter represents general reference-free aggregates as byte lists. A local's physical size is a bounded `LocalKind.aggregate` size; initialization allocates that exact size. `localNumber` rejects snapshots of the wrong length. Generic load/store/init operations carry their byte size, and generic field instructions carry validated byte offsets and scalar widths. They use the same access and lifetime machinery as scalar/vector memory.

The extractor admits explicit layouts with a positive declared size, no reference fields, and supported fields wholly inside that size. It imposes a resource limit of 65,536 bytes per aggregate. It does not infer four fields, an 8-byte field width, implicit CLR padding or a 32-byte total. Overlapping explicit fields remain possible and follow the byte-memory semantics. Generated `AggregateLayout.Valid` theorems check the emitted layout bounds in Lean. Metadata-to-Lean correspondence remains part of the extractor trust boundary.

Fixed 256-bit snapshot-home operations use **vector** names to distinguish them from general aggregates. Lane operations are explicitly vector-lane operations. They do not stand for arbitrary struct layouts. The pure interpreter intentionally returns failure for the new general aggregate operations; use the checked interpreter for those operations. Arbitrary value constructors, address-taking of by-value aggregate parameters and nested/reference-bearing field layouts are not yet exposed by extraction.

## Runtime assumptions

The supported runtime convention is 64-bit, little-endian .NET 10, with fixed hardware capability flags throughout execution. ISA-specific instructions require their declared features; portable vector operations use the supplied software semantics. A selected profile describes runtime-visible availability, including runtime/OS disabling, not merely physical CPU features.

The model assumes admitted `initobj` operations and zero-initialized local storage clear the entire declared reference-free byte layout, including padding. This target-runtime storage assumption is not proved against a JIT. Unknown locals remain uninitialized until written.

Small integers use `i32` on the evaluation stack. `sbyte` and `short` loads sign-extend; byte/Boolean and `ushort`/`char` loads zero-extend. Narrow stores truncate. Extracted argument loads and returns carry narrow type annotations so method boundaries apply the same normalization, including when a caller omits an explicit conversion. Field instructions retain signedness as well as their validated width. These rules follow the CLI small-integer storage model; they do not introduce floating-point conversions, native-integer signatures or arbitrary indirect loads/stores. The older sequential `methodBlock` helper explicitly rejects annotated narrow argument/return instructions; use `CIL.Safety.invoke` for verification.

Ordinary reference-free accesses use alignment 1, for the modeled CoreCLR x64/ARM64 normal-memory convention. This is not a proof of the portable CLI natural-alignment rule. Aligned APIs, volatile/atomic instructions, device memory, concurrency, GC relocation internals and arbitrary object headers are outside the extracted subset. The memory model's relocation results concern allocation-relative references, not a verified garbage collector.

Primitive indirect loads/stores and integer `ldobj`/`stobj` use those same access checks and one-, two-, four- or eight-byte storage. They accept managed references, not numeric addresses or aggregate snapshots. Narrow stores truncate; loads extend according to the opcode or validated type token. Integer `initobj` zeroes and initializes exactly that storage width. `sizeof` emits a constant from validated integer widths or explicit aggregate layout metadata, under the same layout correspondence assumption as aggregate memory operations; it is not a model of arbitrary runtime type layout.

`switch` uses unsigned `i32` indexing, with out-of-range indices falling through. Reachability includes every target and the fallthrough, conservatively even for a constant index. Reachable backedges are rejected, and switch-only dependencies and unsupported arms receive the normal validation. These rules follow the [CLI switch operation](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.switch); they do not add loops or exception-region transfers.

Static data is immutable, extraction-bound RVA storage with field identities retained separately from contents. Static initializers that could execute unmodelled code are rejected. Unsafe reference arithmetic wraps at the modeled native width and retains allocation provenance; every resulting reference must pass formation checks. A valid end sentinel grants no access permission.

## Trusted computing base

- Lean 4.35.0's kernel and its standard foundations. Allowed audited axioms are `propext`, `Quot.sound`, and `Classical.choice` only.
- The definitions faithfully representing the intended supported CIL/runtime behaviour. Their correspondence to .NET is a reviewed modelling assumption, not a formal CLR implementation proof.
- Mono.Cecil, the .NET runtime running the extractor, metadata/signature validation, instruction translation and source emission.
- The verifier, filesystem, SHA-256 implementation, elan/toolchain selection and process execution, for binding the compiled assembly to the generated definitions and checked theorem.
- The user's specification and interpretation of its quantifiers/preconditions. A theorem about one concrete input is not a universal contract.

The C# compiler/JIT is not assumed to prove a source-level contract. Extraction reads the compiler's actual output, but executing that output on a real runtime still relies on the runtime correspondence assumptions above. Hardware and platform implementation correctness are not proved here.

No `sorry`, `admit`, new axioms, native proof evaluation, or unchecked correctness summaries are used in the delivered proofs. `rfl` and `decide` generate kernel-checkable proofs. A failed build, unexpected diagnostic, resource exhaustion or missing audit is a verification failure, not a successful negative semantic test.

## Artifact integrity

The extractor reads assembly bytes without loading/executing the assembly. It checks the requested assembly name or full identity, target framework, Release configuration, method/type metadata, supported layouts, reachable call graph, feature configuration and instructions. Method selectors resolve against all matching metadata methods before validation, including unsupported candidates. C# aliases and omitted return types change only selection; ambiguity is rejected with full candidate signatures, and the manifest stores the resolved canonical entry signature. Short assembly names are matched exactly against the assembly metadata name; a supplied full identity must match in full. It emits the assembly SHA-256, MVID, full metadata identity and instructions together with generated-source and extractor-binary hashes.

The verification driver builds a fresh copy of all handwritten Lean sources without copying compiled artifacts. The installed `leancil verify` command uses the Lean sources bundled with the tool and the same verification implementation as the repository scripts. Library builds use temporary directories; generated code and proofs use an explicit isolated Lean module root. Within one process the driver may reuse that session only while source hashes remain identical. Every generated program and proof uses a separate fresh module directory. A named theorem must be kernel checked and its transitive axioms audited. A report is written only after a second identity/source check. A failed proof attempt removes the previous report at its output path.

The repository script's `--check` checks the report's selected theorem, proof/framework/tool inputs, generated artifact and assembly identity. It does not rerun the kernel and is not a cryptographic signature against a party able to forge the entire report and toolchain. `leancil check` checks extraction artifacts only. `leancil verify` always reruns verification using the selected proof and theorem. `verification.json` stores that selection separately from results, survives failed proofs and is hashed into the report's inputs. An older report can supply the initial selection during migration; neither settings nor an earlier report are proof evidence. The displayed statement is the selected theorem's Lean-printed type from the audit, not a generated English claim of correctness.

`leancil list` is metadata discovery only. It includes methods whose types or instructions the verifier does not support. Listing a signature does not bypass extraction validation or establish any correctness property.

## Negative evidence

The wrong-addition fixture has a finite execution witness plus a uniqueness theorem refuting the requested output at every successful fuel. Out-of-bounds and dangling-reference examples have classified semantic faults plus `invoke_fault_refutes_success`, ruling out success for every fuel. These proofs explain rejection independently of the tactic diagnostic produced when a positive contract fails.
