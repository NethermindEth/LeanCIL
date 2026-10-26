# Soundness boundary

`scripts/PrepareLibrary.cs <output> --extend <base> <trusted-manifest-sha256>` can add CIL
source modules to an authenticated base without changing its certified compiled declarations.
Every existing source and configuration file must match, and the base identity must match the
current platform and Lean tools. Added sources must not shadow any compiled module. The producer
copies and authenticates the old artifacts, binds all added source bytes in a new manifest, and
checks source stability before publication. The digest must come independently from a trusted
producer; self-rehashing corrupted artifacts cannot renew it.

The extension certifies no new declarations. When a proof imports an added helper, ordinary
compilation, kernel replay and theorem auditing still apply. Changes or removals of existing
sources require normal fresh preparation. This is not a general incremental build or an assertion
that arbitrary elaborator dependencies can be inferred from module imports.

External-call metadata identities are serialized as their UTF-8 bytes. Generated proofs check
the validity of bounded chunks and compose them with `ByteArray.IsValidUTF8.append`; the kernel
also checks that the concatenation is exactly the emitted byte array. Every existing signature
and instruction validator consumes that unchanged identity. As with other raw metadata fields,
correspondence between the serialized bytes and the assembly remains an extractor assumption.
The former redundant `externalIdentityNBytes_eq` and `externalIdentityN_eq` literal equalities
are replaced by `externalIdentityNBytes_valid` and shared `externalIdentityChunkN_valid` proofs.

Consumer batches may factor regenerated extraction source into content-named header and method
modules. This is a deterministic transformation in the trusted verifier implementation, not a
proved Lean source-equivalence theorem. The exact input hash is checked again before staging;
all staged sources and compiled artifacts participate in the existing stability checks. Lean
still validates the full program and call connections, and the compiled certificate is audited.
Only unchanged components with an authenticated source/import closure and unchanged artifact
bytes can reuse an earlier kernel replay. A matching module name alone never authorizes reuse.

`leancil resolve-imports` is untrusted location selection outside extraction.
deps.json, NuGet assets, the RID graph and the LeanCilContracts attribute only
choose the sidecar and DLL paths passed to `extract`, which never reads them.
Extraction hashes the files it is given against the independent implementation
and interface pins, so a wrong selection can only fail, never certify other bytes.

## What is defined and proved

Dynamic stack allocation uses the existing allocation-relative memory model. Each successful
nonempty `localloc` creates a fresh frame-owned allocation, grants access to exactly its byte
extent and charges its size rounded to 16 bytes against the activation's resource quota.
`Memory.stackLimit` defaults to zero and admits at most 65,536 bytes per activation. A proof
using a positive quota must justify that deployment assumption; this quota excludes the
runtime's ordinary frame, call and probing overhead and does not establish available physical
thread-stack space. The model reports `stackAllocationFailure` when the quota is insufficient.
That resource failure is not automatically a named CLR exception, nor does a successful model
execution prove that the runtime cannot exhaust its physical stack.

The emitted initialization flag must match the raw method's `localsinit` bit. Without it, new
bytes remain unreadable until written; with it, the payload is zero-initialized. A zero-byte
request returns null without reserving storage. Frame exit expires all dynamic allocations,
and the existing return checks reject escaped references and spans. Pointer values retain
allocation provenance; numeric address fabrication remains unsupported. Memory equivalence
now also requires equal stack quotas, and frame records track the charged dynamic bytes.

These initialization and lifetime rules follow the
[CLI localloc specification](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.localloc?view=net-10.0).
Zero-size null results and 16-byte reservation rounding follow the .NET 10.0.0 CoreCLR
[x64](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/jit/codegenxarch.cpp)
and [ARM64](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/jit/codegenarm64.cpp)
implementations. This source correspondence is an explicit runtime assumption, not a proof
of the JIT or of resource availability on every deployment.

Concrete constrained struct calls retain their original prefix and interface slot in raw
specialization evidence. A mandatory Lean validator independently resolves the slot from the
serialized type, interface, method and explicit-override declarations, then checks the emitted
direct-call target and signature. Faithful metadata decoding and complete serialization of those
declarations remain trusted. The admitted subset has no runtime vtable lookup or boxing fallback;
this does not prove general CLR dispatch correct.

`CIL.Safety.RuntimeExceptions` adds a fixed naming view of checked execution
faults. `RaisesCLR` and `OutcomeContract.HoldsCLR` name `.thrown exception`
directly, arithmetic overflow as `System.OverflowException`, and integer
divide-by-zero as `System.DivideByZeroException`. They require an actual checked
invocation with that fault. All remaining faults, including invalid operands,
bounds failures, unsupported instructions, invalid state and fuel exhaustion,
map to no named exception. The mapping does not change the interpreter,
`.thrown`, `Raises`, or existing outcome-contract proofs. Handler execution
remains unsupported. The admitted runtime correspondence assumption still
applies; a mapping theorem does not prove a CLR implementation correct.

Intraprocedural cycles are admitted by a worklist analysis. Constant facts at a control-flow join can only weaken to unknown; changed facts revisit successors until a fixed point is reached. Stack heights and tracked stack types must agree at backedges as at other joins. This validation is part of the trusted extractor, not a proof of termination. Recursive managed call graphs remain rejected.

`CIL.Safety.loop_terminates` proves successful finite checked execution from a supplied invariant, a natural-number measure that strictly decreases, and kernel-checked execution segments. Each segment relates the actual interpreter before and after an iteration for every continuation fuel budget. Exit cases must prove the postcondition and successful return; `ensures_of_loop` includes checked frame setup and yields the existing `Ensures` specification. `loop_terminates_induction` instead assumes termination at every invariant state of smaller measure, so an iteration may cross a call through a proved `MethodContract` whose fuel stays existential. `loop_outcome_induction` states the same rule for `LoopOutcome`, which fixes one outcome for the loop: normal return, or exactly `.thrown exception` through `RunRaises`, so unsupported instructions, invalid state and fuel exhaustion never discharge an expected exception. Only continuing iterations carry invariant and measure obligations, and `ensures_outcome_of_loop` lifts the result through frame setup to `EnsuresOutcome`. Neither extraction nor finite fuel exhaustion proves termination. The countdown example proves this for all 32-bit unsigned inputs from its stated empty caller memory; it makes no runtime performance claim for large iteration counts.

Generic-method specialization is checked against independently serialized raw definitions by a Lean structural-substitution validator. Faithful metadata decoding and raw-definition serialization remain trusted. Concrete type arguments must satisfy the admitted constraints and layout rules. Specialization copies the original instruction sequence and offsets, substitutes method type parameters in signatures, locals, type operands and nested generic calls, and preserves branch targets. The ordinary CIL validator and Lean semantics then handle each closed body. It adds no proof axioms or method summaries. Generic declaring types and constraints requiring runtime dispatch remain outside the subset.

Specialization can make `typeof(A) == typeof(B)` (or `!=`) a constant. `CIL.Extraction.foldRoles` recognizes the exact five-instruction encoding from the raw closed body, with the exact `System.Runtime` `GetTypeFromHandle` and `op_Equality`/`op_Inequality` call sites, and `sameRuntimeType` decides the result from the substituted type operands. The feature certificate accepts only `nop` for the operands and the decided word for the comparison, propagates that word for pruning, and rejects any non-fallthrough edge into the last four instructions, so the emitted operands, which push nothing, run only as a whole. Reachable type tokens and `System.Type` calls outside a decided test are rejected. The identity rule is a runtime assumption: identical metadata types denote one runtime type, and types with different full names are distinct. A full name in two scopes may be forwarded to one type, so such pairs, decorated names and `void` (serialized without its scope) are undecided and stay unsupported. This follows the JIT's folding of [`Type.op_Equality`](https://learn.microsoft.com/en-us/dotnet/api/system.type.op_equality) for exact type handles; it is not a proof of the JIT.

`foldRoles` also recognizes `throw new E(...)`: `ldstr`/`ldnull` loads, an exact allowlisted `System.Runtime` exception constructor, then `throw`. `exceptionConstructor` lists the supported exception types with parameterless or one-string constructors, and the two-string overloads of `ArgumentException`, `ArgumentNullException` and `ArgumentOutOfRangeException`. Both extraction and the feature certificate reject other types and constructor signatures; null arguments are admitted only as strings, not as arbitrary constructor parameter types. The feature certificate accepts only `nop` for the loads and `newobj`, and `.throw "E"` for the `throw`, and rejects any non-fallthrough edge past the first instruction, so the raised object is always the one constructed. The checked interpreter fails with `ExecutionFault.thrown "E"` at the `throw`. The model does not run the constructor: resource exhaustion, such as an out-of-memory condition, is not distinguished. Methods with exception handlers are rejected, so nothing observes the exception before execution ends.

`foldRoles` folds `stloc s; ldloca s` for a single-use primitive `ReadOnlySpan<T>` receiver: both emit `nop`, leaving the span value on the stack. The feature certificate checks that the local has exactly those two accesses and that the receiver is followed by `get_Length` or a single load or constant before `get_Item`; branches cannot enter the folded sequence. Other supported span uses retain typed local or parameter storage. Memory-backed views retain allocation identity, element width, bounds and lifetime, and never grant authority or initialize bytes. Readonly views prohibit stores through their element references but do not prevent writable aliases from updating the same allocation. `CreateSpan<T>` over static data requires the start of an immutable allocation whose size is a multiple of the element width; checked indexing stays within that field.

Generated Lean and the identity manifest retain the original generic definition and concrete type arguments; each specialized method retains its original metadata token. Assembly hashing and regeneration-based artifact checks bind this information and the generated instructions to the compiled input. These checks establish artifact consistency, not a formal proof of the extractor's implementation.

Block initialization and copying use allocation-aware byte reads and writes. Nonempty accesses check bounds, lifetime, permissions, alignment and GC-reference exclusion; copying additionally requires initialized source bytes and rejects every overlapping region. The unprefixed block alignment is eight bytes on the admitted target, reduced to 1, 2 or 4 by a validated `unaligned.` prefix. Zero-byte operations access no memory, including when passed null references. This zero-length convention is checked against the admitted runtime; it does not model exception handling or arbitrary pointer addresses.

The block operations follow the [CLI copy](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.cpblk) and [initialization](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.initblk) restrictions. Ordinary prefixed loads and stores retain the existing byte-aligned CoreCLR target convention. Prefix validation is part of the extractor trust boundary: valid operands and followers are required, and branches cannot skip a prefix while targeting its following instruction.

Native integers are represented as 64-bit words only after target-profile validation (64-bit, little-endian). Their storage uses existing checked eight-byte homes and managed references. No native integer can be dereferenced as an arbitrary address. `NativeOperands` tracks evaluation-stack types through the admitted control-flow graph, including backedges: only metadata-proven native/int32 arithmetic and comparisons receive `Op.nativeBinary`, which sign-extends the int32 operand, except that unsigned checked arithmetic zero-extends it. Mixed native/int32 unsigned conditional branches are rejected with an explicit `conv.i`/`conv.u` diagnostic: CoreCLR widens constants differently from arguments in this path, and inlining can change that provenance. Same-width branches remain supported. The wrapper has an explicit scalar-operation allowlist and cannot dispatch memory operations, calls, hardware features or nested wrappers. The legacy pure interpreter rejects the wrapper; native mixed-operation proofs use the checked interpreter.

[Pinned x64 and ARM64 probes](evidence/native/README.md) execute 4,100 cases per architecture on official .NET 10.0.0 binaries: 3,600 admitted cases agree with the mathematical oracle; 500 ambiguous mixed unsigned branches are rejected, including 38 recorded divergences from the old rule. The evidence includes exact CIL, operands, results, runtime and binary hashes, official archive checksums, and pinned public importer source. The binary internal build commit differs from the public release tag, so this does not claim an exact reproducible source-to-binary build or a general proof of runtime equivalence.

Checked integer conversions interpret the input according to the opcode's `.un` flag, then check the mathematical value against the destination bounds. Signed narrow results are sign-extended in their 32-bit stack slot. Native destination widths come from the validated target profile, not the machine performing extraction. Floating-point conversion behaviour is outside this model.

Checked integer addition, subtraction and multiplication compute their result over `Int` before checking the signed or unsigned destination range. Overflow cannot silently wrap into a successful result. The universal extracted addition examples prove natural-number addition whenever the sum fits, and the runtime comparison matrix checks both successes and faults for all six encodings at both widths.

Integer division and remainder use an explicit `ArithmeticFault` result, separate from malformed-state and memory faults. Zero divisors and the signed minimum / -1 pair terminate checked execution with located faults. Signed quotient uses truncation toward zero, not Lean's Euclidean division. Signed remainder uses the corresponding truncating remainder. These faults do not implement managed exception objects, handlers or unwinding.

For signed minimum remainder -1, the model selects the overflowing runtime behaviour documented for Intel platforms in [the opcode reference](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.rem). The regression suite compares the emitted CIL with the executing .NET runtime, including this case. This is an explicit runtime correspondence assumption, not a proof of architecture-independent CLI behaviour; proofs requiring successful execution of that input are not supported.

`CIL.Semantics` defines a functional byte-memory execution model, with wrapping bit-vector arithmetic, instruction-level failure, calls and explicit finite fuel. Its memory addresses do not themselves certify physical allocations. Its successful execution theorem is not a memory-safety certificate.

`CIL.Safety.Memory` adds allocation identities, storage kinds, layouts, live/dead state, initialized bytes, read/write views, end sentinels and managed references. Allocation identities increase and are never recycled. `CIL.Safety.Execution` checks every memory/reference instruction and frame transition. It uses the arithmetic interpreter only through the existing value-only whitelist. Unknown operations cannot fall through to unchecked memory operations.

Successful checked execution excludes the model's faults on the executed path. Library theorems establish well-formedness preservation, allocation extension, frame ownership, expiration, caller-memory preservation, valid live values, static-world consistency and running/returned-state invariants. `InvocationCertificate` records successful execution plus these state properties under its stated initial-state premises. Premises such as valid views, well-formed input memory and valid initial references are obligations on callers, not facts inferred from an arbitrary DLL.

`Ensures` describes total correctness of a specified method over a user-supplied precondition and postcondition. A `VC` is a finite execution condition, not a decision procedure that automatically finds loop invariants or arithmetic specifications. The symbolic-execution tactic follows actual generated instructions and optional **proved** summaries. Failed summary elaboration restores the Lean environment and continues raw execution.

## Aggregate generalisation

The checked interpreter represents general reference-free aggregates as byte lists. A local's physical size is a bounded `LocalKind.aggregate` size; initialization allocates that exact size. `localNumber` rejects snapshots of the wrong length. Generic load/store/init operations carry their byte size, and generic field instructions carry validated byte offsets and scalar widths. They use the same access and lifetime machinery as scalar/vector memory.

The extractor admits explicit layouts with a positive declared size and sequential layouts computed from validated primitive, enum or nested aggregate fields, packing and declared size. Both are reference-free and limited to 65,536 bytes per aggregate; sequential padding follows the runtime rules below. Overlapping explicit fields remain possible and follow the byte-memory semantics. Generated `AggregateLayout.Valid` theorems check the emitted layout bounds in Lean. Metadata-to-Lean correspondence remains part of the extractor trust boundary.

Fixed 256-bit snapshot-home operations use **vector** names to distinguish them from general aggregates. Lane operations are explicitly vector-lane operations. They do not stand for arbitrary struct layouts. The pure interpreter intentionally returns failure for the new general aggregate operations; use the checked interpreter for those operations. Validated reference-free nested layouts and same-assembly value constructors are exposed by extraction; reference-bearing field layouts remain unsupported.

## Method-body embedding

`MethodEmbeds program index expected` (`CIL.Embedding.Basic`) states that method `index` exists and that `Embeds expected actual map` holds for its body `actual` and a pc map `map`; expected pc `p` maps to `map.getD p actual.code.length`, so pcs outside the map go past the end of the actual body. `Embeds` requires equal profile, return shape, locals, local kinds, vector locals and arguments, parameter homes and static descriptor list, that pc 0 maps to pc 0, and, for every live expected pc (any instruction except `.unsupported`):

- the actual instruction at the mapped pc is the expected one with every code target renamed through the map;
- a static address at the mapped pc resolves the same descriptor;
- an instruction that can resume at the next pc (anything except `branch`, `ret`, `throw` and `.unsupported`, and including calls) maps its successor to the next actual pc.

Each condition is a list equality or a Boolean check that the kernel decides by evaluation; no equality instance on `Op` is involved.

`CIL.Safety.run_refines` proves, for programs related by `ProgramRefines` (every method embedded, equal program-wide static descriptors), that a successful `CIL.Safety.run` of the expected program at any pc gives the same result, memory included, for the actual program at the mapped pc with the same fuel. `invoke_refines`, `MethodEmbeds.invoke` and `MethodEmbeds.certificate` transfer successful invocations and `InvocationCertificate`s from `program.set index expected` to `program`; `ProgramRefines.set` composes embeddings of several methods. The step lemma `step_relabel` covers every `Op` constructor.

Thrown exceptions transfer through the same induction. `run_outcome_refines` relates every expected outcome that `Transported` admits, a result or a fault whose kind is `.thrown exception`, to the actual outcome at the mapped pc, with the fault moved by `LocatedFault.relocate`: the method and exception are unchanged and the instruction becomes the pc its own method's map assigns, so an exception propagated from a callee is located in the callee. `run_refines` and `invoke_refines` are its successful instances; `run_raise_refines`, `invoke_raise_refines` and `Embeds.invoke_raise` state the relocated fault, and `Raises.of_refines`, `OutcomeContract.Holds.of_refines`, `MethodEmbeds.raises` and `MethodEmbeds.holds` (`CIL.Safety.Embedding.Outcomes`) transfer `Raises` and both clauses of an outcome contract; `MethodContract.Holds.of_refines` and `MethodEmbeds.method_holds` transfer a normal-return method contract. The step lemma `step_raise` shows that only `throw` raises by itself and that every other throw, such as a span index out of range, comes from a computation both steps share. These theorems depend only on `propext`, `Quot.sound` and `Classical.choice`.

Scope and limits:

- The transfer covers success and named thrown exceptions only. Fuel exhaustion, `.unsupported`, memory, arithmetic and invalid-state faults do not transfer: the actual program may have code or methods where the expected one faults, and the actual body may fault where the expected body is dead. No handler or post-throw memory is modeled.
- Dead expected pcs are unconstrained: an `.unsupported` instruction faults whenever it executes, so a successful expected run never reaches one. Actual pcs outside the image of live expected pcs are unconstrained as well; the simulation never visits them.
- Only the checked interpreter is covered. The base `CIL.run` keys vector homes by pc, so renumbering changes its memory and no such theorem holds for it.
- The relation is syntactic and conservative: an inserted live instruction, even a `nop`, on a reachable path is rejected.

`cil_embed` (`CIL.Embedding.Tactic`) computes the map outside the kernel by aligning live instructions, following fallthroughs and branch targets. The alignment is untrusted: the proof term passes the map to `Embeds.mk` with every field closed by `Eq.refl`, and the kernel checks it against the body reduced from `program[index]?`. A wrong map can only make the kernel reject the proof. Before building the proof, the tactic evaluates the same conditions and reports the first violated one.

### Dead locals

`MethodEmbedsDeadLocals program index expected` relaxes only the local declarations: `EmbedsDeadLocals expected actual map` requires `Embeds expected (actual.withLocalsOf expected) map`, so every other field and the code are checked as above, and that `actual`'s locals and local kinds are `expected`'s followed by trailing locals that are each a `.reference` or `.span width writable` initialized to `.nullRef` or `.unmodeled`, with span widths restricted to 1, 2, 4 or 8 bytes. It also requires `expected`'s kinds and initializers to have equal length, every opaque vector local to lie among the kept locals, and no parameter homes, which the frame places after the locals and the extractor addresses by local count. Frame entry creates such a dead local as a root or span slot without allocating, so `enterFrame_deadLocals` shows that `actual` enters the frame of `actual.withLocalsOf expected` with the dead slots appended, in the same memory with the same allocation identities. `StepAppendLocals` is proved separately for every instruction constructor in `CIL.Safety.Embedding.AppendLocals`; the dispatcher `step_appendLocals` shows that a step that succeeds or throws behaves the same with the padded frame, since every local an instruction reads is below the padding, and `run_padded` lifts it to whole runs. `EmbedsDeadLocals.invoke_outcome` composes this with `invoke_outcome_refines`; `MethodEmbedsDeadLocals.invoke`, `.raises`, `.method_holds`, `.holds` and `EmbedsDeadLocals.invoke_raise` (`CIL.Safety.Embedding.DeadLocals`) are its instances, with the same transfer limits as above. `InvocationCertificate`s are not transferred, since their live state names the frame. There is no `MethodEmbedsDeadLocals.refines`: the padded run is related to the unpadded one directly, not through a `ProgramRefines`, so it does not combine with other replacements through `ProgramRefines.set`. To replace other methods as well, prove their `MethodEmbeds` against `program.set index expected`, the program with the dead-local method already replaced, and chain each `.invoke` with this one's.

Trailing byref, pointer and span dead locals are covered. Span slots retain their element width and mutability, and hold an empty view or an unmodeled value without allocating. Unsupported span widths and nonempty scalar initializers remain rejected by the kernel-checked condition. Numeric and interspersed dead locals are outside this exact-memory embedding: their homes change later allocation identities or local operands. They use the separate allocation refinement below. `cil_embed` proves `MethodEmbedsDeadLocals` goals too and names the violated local condition.
`CIL.Safety.AllocationRefinement` supplies a separate checked simulation for numeric and
interspersed dead declarations. `MethodRenaming` retains local kinds and initializers in order and checks
all relocated local operands while preserving method indices and execution metadata.
Both methods must satisfy `OrdinaryFrame`: no opaque vector locals or vector/parameter
argument homes, bounded layouts and supported span widths. `LocalDeclarations` preserves
each retained initializer and checks inserted values with `InitializerFits`. Their actual
initialization writes affect only fresh private homes outside the mapped allocation image;
null managed slots do not allocate. Invalid kinds, widths and initializer values are rejected. Actual
source entry success supplies successful retained initialization; the target entry is proved.
The initial memory must be well formed and its static bindings bounded by the allocation
counter. These restrictions are premises of the public theorems.

The relation is injective over the source allocation prefix. New paired allocations extend
it without moving existing images, and extra target homes remain private outside that image.
A separate activation relation preserves frame storage kinds and ownership through nested
calls and expiry. `StepRenaming.stepTransport` proves the complete checked dispatcher;
recursive execution extends the relation through every later allocation. The public
`ProgramRenaming.invoke_scalars` and `.invoke_confined` instantiate this theorem and transfer
exact scalar results and `MemoryBelow` claims on the initial caller prefix. `.raises` also
requires valid input arguments and preserves named exceptions. No consumer-supplied step
simulation is assumed. These results do not assert identical final allocation counters,
identical fresh references or arbitrary reference-valued postconditions.

`MethodContract.Holds.of_allocationRenaming` preserves the same contract and footprint.
Its explicit premises require readiness from the original precondition, scalar result
encoding and stability of the original postcondition under the proved caller-prefix
relation. Confinement is transported from actual successful executions, rather than
assumed for the renamed result.

## Shared proof contracts and reduction

`RunTrace` exposes the four successful control-flow cases of checked execution.
`FrameSetup` composes setup effects, while `InstructionContract`,
`StaticInstructionContract` and `StepContract` combine effects and conditional
value-validity results. Their constructors and theorems are kernel checked;
clients retain the original well-formedness and validity hypotheses. Sharing
these proofs changes neither the interpreter definitions nor the trusted base.

Checked symbolic execution composes proved instruction equations. Its `rfl`
path uses definitional equality checked by the kernel; equation rewriting and
simplification also produce checked proof terms. Return candidates are limited
to fetched return instructions, and fact-dependent steps retain their explicit
hypotheses. These tactics cannot turn an unresolved obligation or failed
candidate into a correctness certificate. See [the proof guide](PROOFS.md) for
their use and [validation coverage](VALIDATION.md#proof-automation).
Compiled artifact size and elaboration speed do not change
the theorem's logical guarantee.

## Runtime assumptions

The supported runtime convention is 64-bit, little-endian .NET 10, with fixed hardware capability flags throughout execution. ISA-specific instructions require their declared features; portable vector operations use the supplied software semantics. A selected profile describes runtime-visible availability, including runtime/OS disabling, not merely physical CPU features.

The model assumes admitted `initobj` operations and zero-initialized local storage clear the entire declared reference-free byte layout, including padding. This target-runtime storage assumption is not proved against a JIT. Unknown locals remain uninitialized until written.

`Vector128.CreateScalarUnsafe(ulong)` leaves the upper lane unspecified. The checked value `v128Low64 low` stands for every 128-bit vector whose lane 0 is `low` (`CIL.Vector128Represents`). `checkedIntrinsic` sends any operand list holding one to `CIL.evalUnspecifiedIntrinsic`, which admits exactly four consumers and rejects every other intrinsic: `Vector128.As*` reinterpretation (the result stays unspecified), `GetElement` at index 0, and the count operand of `Avx2.ShiftLeftLogical`/`ShiftRightLogical`, which reads lane 0 alone. `CIL.Safety.checkedIntrinsic_unspecified` proves that every successful checked evaluation agrees with the ISA result on every concretisation of its operands. Every other instruction rejects such operands before running: `observerCount` and `MemoryOp.argumentCount` name the operands each op reads, with no default case, and stores, bitcasts, byte homes and argument homes reject them as well. Only internal forwarders pass them on (`dup`, `pop`, opaque local stores and loads). Returns, ordinary call arguments and constructor arguments reject them before exposing a result or entering another method. Stores to caller-visible memory also reject them. Contracts cannot certify a successful boundary crossing with unspecified lanes; consume the known low lane within the method or construct a fully defined vector first. Constructor setup lemmas require both checked values and the absence of unspecified argument bits; concrete arguments discharge the latter automatically. `invoke_return_known` and `step_call_known` state the fully specified return and call-argument guarantees. Unaddressed `Vector128<ulong>` locals are `opaque128` slots only in methods whose reachable code uses `CreateScalarUnsafe`; other methods retain byte homes. This intrinsic is the only producer of unspecified lanes, reinterpretation only preserves them, and method-boundary guards reject incoming unspecified arguments. Thus ordinary callees without a reachable producer cannot obtain unspecified vector values through their arguments. If an external invocation supplies unspecified inputs directly, byte-home stores still reject unspecified bits. `OpaqueLocalsValid` checks the emitted producer and recomputes eligible locals from the raw body (no `ldloca`), so extraction cannot choose the set. Passing an unspecified vector to a private helper in the same assembly is also rejected, even if the helper would read only lane 0; opaque by-value parameter homes are not yet supported. That the JIT never exposes the upper lane through these consumers is a runtime correspondence assumption.

Small integers use `i32` on the evaluation stack. `sbyte` and `short` loads sign-extend; byte/Boolean and `ushort`/`char` loads zero-extend. Narrow stores truncate. Extracted argument loads and returns carry narrow type annotations so method boundaries apply the same normalization, including when a caller omits an explicit conversion. Field instructions retain signedness as well as their validated width. These rules follow the CLI small-integer storage model. The older sequential `methodBlock` helper explicitly rejects annotated narrow argument/return instructions; use `CIL.Safety.invoke` for verification.

Ordinary reference-free accesses use alignment 1, for the modeled CoreCLR x64/ARM64 normal-memory convention. This is not a proof of the portable CLI natural-alignment rule. Aligned APIs, volatile/atomic instructions, device memory, concurrency, GC relocation internals and arbitrary object headers are outside the extracted subset. The memory model's relocation results concern allocation-relative references, not a verified garbage collector.

Primitive indirect loads/stores and integer `ldobj`/`stobj` use those same access checks and one-, two-, four- or eight-byte storage. They accept managed references, not numeric addresses or aggregate snapshots. Narrow stores truncate; loads extend according to the opcode or validated type token. Integer `initobj` zeroes and initializes exactly that storage width. `sizeof` emits a constant from validated integer widths or validated aggregate layout metadata, under the same layout correspondence assumption as aggregate memory operations; it is not a model of arbitrary runtime type layout.

`switch` uses unsigned `i32` indexing, with out-of-range indices falling through. Reachability includes every target and the fallthrough, conservatively even for a constant index. Reachable backedges are validated by the same fixed-point feature and stack analyses as other branches; switch-only dependencies and unsupported arms receive the normal validation. These rules follow the [CLI switch operation](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.switch); they do not establish loop termination or admit exception-region transfers.

A null managed reference is a distinct value, not address zero. `Unsafe.NullRef<T>` produces it and `Unsafe.IsNullRef<T>` compares against it without any access check, as .NET compares the pointer. Every checked memory instruction faults with `nullDereference` on it, before forming a field or lane offset; this models the `NullReferenceException` that the runtime raises for an access through a null byref, under the same runtime correspondence assumption as other faults. The fault is not `thrown`, so an `OutcomeContract` cannot name it as raised; methods with handlers remain rejected, so nothing observes it.

Static data is immutable, extraction-bound RVA storage with field identities retained separately from contents. Static initializers that could execute unmodelled code are rejected.

Supplied one-dimensional primitive integer arrays retain an element type, length and checked
allocation-relative data reference. The runtime correspondence premise must identify these with
the actual array's element type, length and backing bytes; constructing a model view does not
establish that correspondence. Array operations reuse existing allocation, lifetime,
initialization and authority checks. A readonly permission set grants no write authority, while
aliases over the same allocation observe the same bytes. A valid null array raises the named
`System.NullReferenceException`; an out-of-range index on a valid non-null array raises
`System.IndexOutOfRangeException`. Invalid extents, expired storage and missing authority remain
model faults and cannot prove either expected exception. Array allocation, reference elements,
multidimensional arrays and taking the address of an array root are outside this subset.
The scalar certificate checks array opcode families, integer widths, load signedness, native
integer distinctions and typed element tokens against the emitted operations.

For `readonly.; ldelema`, the certificate additionally binds the readonly flag to the
immediately preceding raw prefix and disallows branch entry between the two instructions.
Restricted references keep their tag through argument checks, calls, returns and local stores.
A local holding a restricted reference uses `LocalSlot.readOnlyRoot`; loading it cannot produce
an unrestricted reference. Reads still require initialized readable bytes. Stores through the
restricted view fail even when memory contains write authority, and unsupported reference
adapters cannot strip the tag. This is an access restriction, not an immutability or uniqueness
claim: writes through other authorized aliases remain visible. The subset excludes reference
element arrays and their covariance/type-check behavior.

Generated static identities are unsigned natural numbers from SHA-256 of the
full assembly identity and full field name. The assembly identity text is
`Name, Version=a.b.c.d, Culture=<culture or neutral>, PublicKeyToken=<16 lowercase
hex digits or null>`, followed by `, Retargetable=Yes` for a retargetable name. It
is built from the name's components, not from a metadata library's display string.
The field name is Mono.Cecil's `FieldReference.FullName`,
`<field type> <declaring type>::<name>`. A fixed test vector detects a change to
either text or to the encoding. Each UTF-8 component is preceded by
its byte length as a little-endian 32-bit integer. The hash bytes are interpreted
as one unsigned big-endian number. MVID and method bodies are excluded. No proof
assumes that this hash is injective. Extraction and import checks reject key
collisions. Full verification also proves `linkChecked` for the composed program,
so every linked descriptor is compatible there.
The raw `link` function has no collision guarantee.

`StaticWorldValid descriptors memory` constrains cached contents only for the
listed descriptors. `StaticRegistryValid memory` still requires unique keys,
distinct allocations and live immutable storage for every registry entry.
Thus another assembly's loaded fields do not make a library world false.
Composition joins descriptor lists over one memory whose shared keys name equal
descriptors; it does not merge memories or infer allocation disjointness from key
disjointness. `StaticIdentitiesAbsent` supplies a public first-use premise only.
Repeated calls with loaded fields use a published `StaticWorldValid` precondition.
RVA exports carry a kernel-checked static identity set in their certification.
Import extraction recomputes the selected implementation's reachable static set
at the selected profile. This analysis remains trusted metadata processing, not
a proof of CLR execution or library correctness. Static-value and type-init
assumptions are still rejected by the closed-export producer.

A static readonly integer, enum or reference-free struct field set by its static constructor is admitted only for `ldsfld`, under `--assume-initialized` for its declaring type, and loads as a constant scalar or aggregate. Two parts are trusted: the extractor's recognition that the constructor stores an integer literal, `M(constants)`, or a copy of such a field stored earlier exactly once and unconditionally, and the runtime assumption that nothing writes the field after that store. The extractor rejects other stores in the module and `ldsflda` of the field in the constructor or its same-assembly callees, and never forms the field's address in an extracted method; writes through `Unsafe`, reflection or other unmodelled code are excluded by assumption, as the JIT also treats an initialized `static readonly` field as constant. The value itself is kernel checked: `StaticValuesValid`, part of `TranslationValid`, reruns `M` on its recorded arguments from empty memory, with constructor-initialized sites removed so that no initializer can read a value it justifies, and requires exactly the emitted bytes after storage-width truncation. Direct literal descriptors are checked against their emitted bytes with the same integer-storage rules; recognizing and faithfully decoding the literal expression remains trusted. The per-method shape validator binds scalar load width and signedness to the raw field type, including enum storage. `M` runs under the selected profile, so this also assumes the profile matches the runtime during initialization. Reports list each such field as a caller assumption next to the initialization assumption. Unsafe reference arithmetic wraps at the modeled native width and retains allocation provenance; every resulting reference must pass formation checks. A valid end sentinel grants no access permission.

## Trusted computing base

- Lean 4.35.0's kernel and its standard foundations. Allowed audited axioms are `propext`, `Quot.sound`, and `Classical.choice` only.
- The definitions faithfully representing the intended supported CIL/runtime behaviour. Their correspondence to .NET is a reviewed modelling assumption, not a formal CLR implementation proof.
- Mono.Cecil, the .NET runtime running the extractor, metadata/signature validation, instruction translation and source emission.
- The verifier, filesystem, SHA-256 implementation, elan/toolchain selection and process execution, for binding the compiled assembly to the generated definitions and checked theorem.
- The user's specification and interpretation of its quantifiers/preconditions. A theorem about one concrete input is not a universal contract.

The C# compiler/JIT is not assumed to prove a source-level contract. Extraction reads the compiler's actual output, but executing that output on a real runtime still relies on the runtime correspondence assumptions above. Hardware and platform implementation correctness are not proved here.

No `sorry`, `admit`, new axioms, native proof evaluation, or unchecked correctness summaries are used in the delivered proofs. `rfl` and `decide` generate kernel-checkable proofs; generated evidence uses `decide +kernel`, which reduces the decision procedure in the kernel instead of the elaborator, adds no axioms, and keeps certificates for long method bodies within the default heartbeat budget. A failed build, unexpected diagnostic, resource exhaustion or missing audit is a verification failure, not a successful negative semantic test.

## Independently checked extraction evidence

`CIL.Extraction.TranslationValid` binds one evidence record to every emitted method in program order. Its component validators recompute sequential and explicit layouts from raw fields, packing and declared size; require the complete set of layout-dependent instruction/local/parameter sites; derive parameter homes from reachable raw argument operations; check generic substitution through signatures, locals, operands and nested calls; and bind managed calls to the specialized target table. Method initialization and return shape are checked too.

`TranslationValid rawLayouts computedLayouts methodEvidence imports program` also takes the import table `Extracted.imports`. Import slot `j` is method index `program.length + j`, so it never names an extracted method. A live external call site may emit `.call t c` only as a plain `call` of a non-generic method with `t ≥ program.length`, a slot `imports[t - program.length]` whose identity (assembly scope and full method name) equals the site's, whose parameter count, receiver and result match the site's metadata, and `c` equal to the site's argument count; any other external site must emit a non-call operation, as before. `validated_import_call` states these facts for an accepted call and `validated_call_bound` shows every accepted call targets an index below `program.length + imports.length`. The extractor does not yet resolve imports, so it emits `imports := []` and every external site keeps its runtime model or is rejected. A slot's `closureDigest` and `Extracted.importSignatures` are outside `TranslationValid`: like `signatures`, the signature table only locates a slot for `bind_import`, and nothing yet binds a slot to an implementation or contract.

Feature certificates record abstract incoming states at every original instruction. Lean checks entry state, abstract transfers, all required successors, joins, the reachable mask and emitted feature-dependent operations, including decided type tests. Closure and weakening theorems support the analysis. This is not a full concrete-interpreter simulation theorem for every raw CLI opcode. Raw metadata fidelity, unsupported transformations, static-data serialization and general instruction translation remain part of the trusted boundary.

Scalar certificates additionally record the complete incoming stack of `word32`, `word64`, `native`, `reference`, `nullObject` or `other` kinds at each feature-reachable PC. `ScalarFlowValid` checks the empty entry, code/certificate lengths, raw maximum stack, independently derived raw transfers and exact incoming-stack agreement on every required successor, including joins and backedges. Managed call parameter and result types are bound exactly to the specialized callee's closed signature. Call operands must match the reversed parameter-kind list and a reference receiver where required. External parameter types must match the raw full signature after method and declaring-type argument substitution; unsupported type spellings stay opaque. Local and argument stores must match the declared home kind, with the explicit 64-bit storage rule below. Returns require the declared result representation and no extra stack values; only native/int64 storage interchange is permitted. External result kinds require the recorded runtime type to agree with the return spelling in the full raw method identity; unknown types remain `other` and cannot justify scalar arithmetic or conversions. Only supported integer producers receive an integer kind; unhandled producers, including floating conversions and reference/array loads, remain `other`. This is a type-flow check of the recorded raw input, not a proof that metadata decoding or raw serialization is faithful.

For every reachable covered opcode, `ScalarFlowValid` requires an exact emitted operation before any general stack-effect check can accept it. The covered families are integer literals (`ldc.i4.*`, `ldc.i4.s`, `ldc.i4`, `ldc.i8`), wrapping and checked add/subtract/multiply, signed/unsigned divide and remainder, bitwise operations, shifts, negation, integer comparisons, all admitted checked/unchecked integer conversions, and all twenty short and long compare-and-branch encodings with their exact target. Literal encodings must have their signed operand range and exact bit pattern, including high-bit-set 64-bit words. Conversion width, result signedness, input signedness and checkedness are matched independently. Mixed native/int32 binary and compare-and-branch operands require exactly one `nativeBinary` wrapper; homogeneous operands forbid it, and native/int64 mixtures and non-integer branch operands are rejected. Mixed `bne.un`, `bge.un`, `bgt.un`, `ble.un` and `blt.un` are rejected as in the extractor: on .NET 10 CoreCLR zero-extends an int32 argument there but sign-extends an int32 constant, so inlining changes the outcome. Mixed `clt.un` and `cgt.un` sign-extend for both argument and constant operands, direct and inlined, tiered and fully optimized, on x64 and arm64; this is an observed runtime fact, like the native runtime comparisons, not a proof. The admitted profiles have a 64-bit native width.

A non-covered opcode cannot emit a literal, arithmetic, comparison, conversion, compare-and-branch or `nativeBinary` operation, even with a matching stack effect. The only exceptions are a decided type test's word, which the feature check binds, and size constants: `sizeof` and the exact `System.Runtime` `Unsafe.SizeOf<T>()` site emit the primitive or vector width, or for an aggregate the size that its layout use binds. `ScalarFlowValid.instruction_checked` exposes this per-site obligation from an accepted certificate. Direct Lean regressions tamper with emitted arithmetic, literals, conversion flags, wrappers, branches, stack kinds, joins, managed return widths, size constants and scalar operations emitted at uncovered opcodes, including whole `TranslationValid` rejection cases.

The scalar extension does not verify the whole extractor or establish a concrete CLI-to-model simulation. Non-scalar operations at non-covered opcodes keep their existing specialized checks or stack-effect fallback; runtime models emitted for external calls are outside the scalar certificate. Metadata decoding, faithful raw input and static-data serialization, external runtime-model correspondence, and correspondence between the model and the runtime remain explicit trust assumptions.

The verifier compiles a separate audit importing only `Extracted`, which restates `Extracted.translation_valid` at the exact `TranslationValid rawLayouts computedLayouts methodEvidence imports program` type and prints `Extracted.imports` into the recorded audit, and kernel-replays it. The theorem audit below then requires the compiled `ExtractionAudit.valid` (in batches, each `Extracted.translation_valid`) to be a theorem whose type is that application, compared structurally, and audits its transitive axioms. A missing certificate, an unrelated `True` theorem, a non-theorem declaration or a certificate over a different import table cannot substitute for this check. Malformed-layout, omitted-site, home-redirection, generic-substitution, feature-pruning, forged type-test and whole-program evidence regressions exercise the validators independently of positive example proofs.

## Artifact integrity

The extractor reads assembly bytes without loading/executing the assembly. It checks the requested assembly name or full identity, target framework, Release configuration, method/type metadata, supported layouts, reachable call graph, feature configuration and instructions. Method selectors resolve against all matching metadata methods before validation, including unsupported candidates. C# aliases and omitted return types change only selection; ambiguity is rejected with full candidate signatures, and the manifest stores the resolved canonical entry signature. Short assembly names are matched exactly against the assembly metadata name; a supplied full identity must match in full. It emits the assembly SHA-256, MVID, full metadata identity and instructions together with generated-source and extractor-binary hashes.

The verification driver builds and kernel-replays a source-keyed library before publishing it to a local cache. The key binds CIL sources, build configuration, platform and selected Lean compiler. Cache manifests cover every cached file and are hashed when an entry is published; a receipt that authenticates the manifest lets later runs read the entry in place. Each verification reads the validated base in place as a path dependency of a private session package, so support and proof builds write only inside that session. A supplied certified library is hashed against its trusted manifest digest once per process tree: the validating process exports `LEANCIL_CERTIFIED_LIBRARY_VALIDATED`, and its children check only the manifest digest, library key and source binding. The driver does not re-hash the base or the auditor during a run; a process that can rewrite them could equally replace the verifier or the toolchain, so such writers are outside this model. `--fresh` and CI runs bypass cache reads and writes. Reports record the library key and whether the base was freshly built or reused. The installed `leancil verify` command uses the Lean sources bundled with the tool and the same verification implementation as the repository scripts. Library builds use temporary directories; generated code and proofs use an explicit isolated Lean module root. Within one process the driver may reuse that session only while source hashes remain identical. Every generated program and proof uses a separate fresh module directory. The generated module, proof module and privately built support modules are independently kernel-replayed, so disabling kernel type checking during elaboration cannot manufacture a successful report. Locally cached consumer modules that import `Extracted` are restored only to skip rebuilding: they are always kernel-replayed against the freshly built extraction, which is itself never restored. `Extracted.lean` omits the assembly hash; the extraction integrity check and the report bind the actual assembly. Transitive theorem axioms are audited separately. Reports use schema 3 and require an independently kernel-replayed extraction certificate as well as the selected theorem; older reports must be regenerated. A report is written only after a second identity/source check. A failed proof attempt removes the previous report at its output path.

The repository script's `--check` checks the report's selected theorem, proof/framework/tool inputs, generated artifact and assembly identity. It does not rerun the kernel and is not a cryptographic signature against a party able to forge the entire report and toolchain. `leancil check` checks extraction artifacts only. `leancil verify` always reruns verification using the selected proof and theorem. `verification.json` stores that selection separately from results, survives failed proofs and is hashed into the report's inputs. An older report can supply the initial selection during migration; neither settings nor an earlier report are proof evidence. The displayed statement is the selected theorem's type as the theorem audit prints it, not a generated English claim of correctness. It is printed without the proof's notations, so operators appear as their functions (`HAdd.hAdd`); numerals still print as digits whatever `OfNat` instance they use, so a statement is checked against a stated type only where an audit names one.

`Extracted.signatures` lists each method's emitted metadata signature in program order. It is covered by the generated-source hash and the extraction integrity check, not by `TranslationValid`; `CIL.MethodIdentity` uses it only to choose an index, and every binding it emits is a kernel-checked `rfl` over the same `Extracted.program`.

`Symbols.lean` (`ExtractedSymbols`) holds PDB local names, scopes and sequence points. The PDB is not under the assembly hash, so it is outside the trusted base and never affects `Extracted.lean` or `TranslationValid`. `leancil check` compares it with the regenerated file only when a matching PDB is present. `local_named` only chooses a slot number that the proof then states and the kernel checks against `Extracted.program`; a stale or forged PDB can make a proof fail, not prove a different statement. Verification compiles and kernel-replays the module only for proofs that import it, directly or, in consumer packages, through their own modules, and binds its hash into the proof cache key; consumer support caches never hold its importers.

`leancil list` is metadata discovery only. It includes methods whose types or instructions the verifier does not support. Listing a signature does not bypass extraction validation or establish any correctness property.

Portable consumer support manifests require an independently trusted SHA256 and bind the verifier, framework, toolchain, source snapshot and compiled import closure. Schema 2 fingerprints deserialize every `.olean`, `.olean.server` and `.olean.private` part with the pinned Lean toolchain, remove only the `Lean.Linter.lintLogExt` diagnostic extension, then reserialize with Lean's compactor and hash the result. This extension records linter messages and source locations, not kernel declarations. All constants (including private declarations), import modifiers and other extensions remain covered. Source paths inside definitions are retained. A changed fingerprint invalidates all dependents. The consumer is still built from fresh sources, extraction-dependent modules are replayed, and raw artifact hashes are checked for stability across fingerprinting, replay and theorem audit. Canonical files are temporary fingerprint inputs and are never loaded as proof artifacts.

Canonical normalization receipts may be reused across verifier processes. Each authenticated receipt binds the module name, freshly hashed presence and bytes of every compiled part, the verifier policy, Lean executable, auditor executable and native runtime libraries. Cache misses normalize private copies whose hashes match that snapshot; input and tool identities are checked again before publication. Cached values preserve the exact linter-stripped fingerprints and do not certify source provenance or proof success. Source/import closure checks, raw artifact stability checks, theorem audits and required kernel replay still run. Fresh and disabled-cache requests do not use or publish local receipts.

A prepared certified library can supply the same canonical transformation results in
`canonical-fingerprints.json`, covered by its independently trusted manifest digest and
source/toolchain binding. The producer pins this table before publishing the artifact;
the receiver pins it before executing consumer code. Reuse requires the exact module name,
presence and raw hash of every compiled part, plus the normalization schema, native auditor,
Lean executable and native runtime hashes. These bindings are rechecked after normalization.
The transformation schema is independent of the producer/receiver driver assembly, so the
repository preparation script can supply the packaged verifier without treating their
different binary identities as interchangeable proof policies. Local receipts still bind
the complete verifier binary. Framework fingerprints grant no additional certification or
replay exemption: each consumer's existing source, import and proof checks remain mandatory.


Local consumer support generations are a cache, not part of the trusted base. A restored module is reused only when its local HMAC receipt and every file hash verify, its recorded source hashes and compiled imports match the current snapshot, and Lake leaves its bytes unchanged after the build; otherwise every module is replayed. Each such artifact was kernel-replayed (or restored under the same rules) by an earlier successful verification. The key binds the variables Lean, Lake and elan read, not the whole process environment: an elaborator that reads another variable is not tracked by Lake's own traces either, and its output is still kernel-replayed when first certified. Name such variables in `LEANCIL_CACHE_ENVIRONMENT`, or use `--fresh`.

These receipts also retain compilation outputs for `Extracted` and `ExtractionAudit`, bound
to the exact generated program and audit source through their compiled import closure.
When a consumer proof is rechecked, restored certificates and their extraction-dependent
importers still undergo kernel replay. The certificate and theorem audits, extraction
regeneration, assembly hashes and source-stability checks remain mandatory.

Batch verification shares a source snapshot across requests. Requests with identical generated CIL share a workspace build and kernel replay; other groups may share only certified extraction-independent support. Each request's theorem audit loads only its own proof module's replayed oleans and runs none of their code, so no request's notations or elaborators can affect any printed statement or axiom report. A request fails for any replay failure in its own import closure or in the extraction certificate, and every non-certified module in the workspace is replayed.

For multi-extraction consumer batches, the first workspace prebuilds support found in all
requests' source import closures. This scheduling scan recognizes repeated import commands,
including `public`, `meta`, `import all` and nested comments; ambiguous sources
and unrecognized syntax remain ordinary per-group work. The scan grants no trust.
Every built module enters the compiled import graph and kernel replay, including modules
outside the first proof's closure. Only after replay, theorem audits and source/artifact
stability checks pass are extraction-independent artifacts shared with later workspaces.
The compiled graph excludes indirect imports of `Extracted` and `ExtractedSymbols` even
when their source imports were not recognized by the scheduling scan. Failed optional
support builds do not bypass normal group builds or certify their unfinished outputs.

## Theorem audit

Proof and publisher Lean source is untrusted. Elaborating it runs its code: `elab_rules`, macros, instances, `run_cmd` and, in any module importing it, `initialize`. Audits therefore never elaborate a module whose import closure contains such source, and never read its output. `leancil-audit` (`CIL/OleanAudit.lean`, built with the library before any proof) imports the replayed oleans with `importModules (loadExts := false)`: no environment extension, attribute, elaborator, notation or initializer from them runs, and toolchain modules precede `LEAN_PATH` so none can be shadowed. For each requested theorem it requires a `theorem` declaration, compares its type structurally (after removing metadata, without unfolding or instance resolution) with an expected expression when one is given, computes the axiom closure itself by walking declaration bodies, ignoring the axiom summaries stored in oleans, and reports a `Not (... .Holds ...)` refutation. It writes JSON that the driver checks against the allowed axioms. Request and result formats are documented at the top of the source; constants can also be required to have an exact value.

The audit does not type-check: it is sound only on bytes that kernel replay accepted. The driver hashes every olean of the session library and the proof directory before building the proof, requires the build to leave them unchanged and to add only the proof module's own oleans, replays them, audits, and rehashes the set afterwards; the checker executable is hashed when the library is built and before every run, and each audited module must resolve to the hashed file. This binds the replayed and audited bytes against anything the proof build does while it runs. It does not contain a build that leaves a process behind, which could exchange files between hashing and reading or alter the toolchain, the checker or this driver. Building untrusted source must therefore run isolated: a disposable container or user account, with its process tree ended before verification continues and nothing it could write trusted afterwards.

A namespace request audits every `theorem` that the listed modules declare under given namespace prefixes, by the same kernel-declaration walk, and reports the count; a prefix matching no theorem is an error. `leancil audit-library` builds a Lake package, kernel-replays every module in the import closure of the listed modules (skipping only CIL modules that, with every module they import, are byte-identical to the certified library), audits those replayed oleans and requires them unchanged afterwards. It certifies the replayed bytes, not that the package's build directory was compiled from its current sources.

## Negative evidence

The wrong-addition fixture has a finite execution witness plus a uniqueness theorem refuting the requested output at every successful fuel. Out-of-bounds and dangling-reference examples have classified semantic faults plus `invoke_fault_refutes_success`, ruling out success for every fuel. These proofs explain rejection independently of the tactic diagnostic produced when a positive contract fails.

## Argument storage

The scalar certificate permits interchange between `word64` and `native` only at a metadata-bound 64-bit local home, argument home or return boundary. Both have the checked interpreter representation `i64` on the validated 64-bit target. This representation rule does not permit a mixed native/int64 arithmetic operation, int32 widening, or recovery of numeric width from `other`.

Primitive integer pointer parameters, locals and results carry checked allocation-relative references. Raw `void*` remains opaque except at the supported `System.Runtime` 10 primitive `Span<T>(void*, int32)` and `ReadOnlySpan<T>(void*, int32)` constructors. Their scalar evidence checks the exact declaring type, external signature, parameter/result metadata, element width and mutability against the emitted `spanFromReference` operation. The existing `ReadOnlySpan<byte>` constructor retains its exact `spanCreate` check. Each constructor requires a checked reference and an int32 length; an opaque value or native integer cannot fabricate a reference through this rule. Other pointer element types remain unsupported by extraction.

A raw `stloc` into a validated int32 or narrow integer home with a known `word64` or `native` input is an explicit terminal `invalidState` case. The checked home store rejects every such `i64` input. The certificate therefore requires no successful successor from that store; it does not convert the value or treat later instructions as a successful execution. The rule requires the exact emitted local index. Unknown values, references and missing or different homes cannot use this exception. All covered arithmetic and conversion encodings still require their exact checks, including after the terminal store.


Assigned or addressed parameters receive private frame-owned storage with the declared physical type. Argument loads, assignment and address-taking share that storage; ordinary by-value calls copy values into the callee's home. A byref parameter is a private reference slot: assigning it changes that slot, while writing through it affects the referenced allocation. Addresses of byref slots are explicitly rejected because nested managed-reference storage is outside the model.

Narrow stores truncate and typed loads extend, following the [starg rules](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.starg). The [ldarga operation](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.ldarga) uses the existing allocation-relative reference and access checks. All owned parameter homes expire at return, and returned references are checked after expiration. The original argument list remains available for untouched parameters; extraction redirects every load of a materialized parameter to its home. This mapping and the validated storage metadata are part of the extractor trust boundary.

## Sequential struct layout

Sequential layouts are computed for same-assembly, non-generic value types containing admitted primitive integer, integer-backed enum or nested reference-free aggregate fields. Nested field alignment comes from the validated child layout, capped by the parent packing; it is not inferred from the child byte size. Field order, packing, declared size and the validated 64-bit native width determine offsets and size. Default packing is eight; explicit packing is restricted to the supported powers of two. Inferred sizes include trailing alignment padding, explicit sizes cannot truncate fields, and empty structs occupy at least one byte. Inline arrays, auto layout (other than the [value tuples](#value-tuples) below), reference fields and floating-point fields are rejected transitively. Recursive layouts and nesting beyond 128 active types fail explicitly.

This models managed storage, not interop marshalling. In particular Boolean and Char retain their managed widths. Runtime correspondence follows the admitted [.NET 10 sequential layout implementation](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/classlayoutinfo.cpp), with independent runtime size/offset probes and execution comparisons. Extracted layouts still carry kernel-checked bounds theorems; those theorems validate the emitted layout, not the CLR implementation itself.

## Value tuples

`System.ValueTuple<T1, T2>` from the exact `System.Runtime` 10.0.0.0 reference is the one admitted generic, external value type. Its metadata declares **auto** layout, not sequential: CoreCLR [places auto-layout fields](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/methodtablebuilder.cpp) largest first, so `(uint, ulong)` stores Item2 at offset 0 and Item1 at offset 8. Auto layout coincides with sequential placement only when every field has the same width, so only tuples of two primitive integer type arguments of equal width are admitted; mixed widths, enums, nested aggregates and other arities are rejected. The raw layout records `auto := true`, and Lean's `computeLayout` accepts it only for equal-width primitive fields without explicit offsets, packing or declared size, so the equal-width condition is kernel-checked rather than trusted. The definition is resolved through Cecil and must be ``System.ValueTuple`2`` in `System.Private.CoreLib` with exactly the instance fields `Item1 : T1` and `Item2 : T2`. Field operands are serialized with the instance's type arguments in place of `T1`/`T2`. The ordering rule is a runtime correspondence assumption; `Tests/TupleDivision.cs` probes the running runtime's offsets for both the admitted and the reordered shapes and compares returned tuple bytes. Tuple construction (`newobj` of the external constructor), tuple methods and tuple fields inside other structs remain unsupported.

## Typed copies

`cpobj` uses the validated operand type's byte width and the same checked read/write operations as other memory instructions. A generic theorem, `CIL.Safety.copyObject_writes_snapshot`, proves that every byte in a successful destination copy equals its corresponding source snapshot byte and is initialized. This includes padding in the admitted byte-storage model. Source initialization, permissions, allocation bounds, lifetimes and GC-sensitive intervals remain checked. Identical addresses are allowed; partially overlapping ranges are explicitly unsupported.

Runtime comparisons exercise exact `cpobj` instructions emitted with Cecil, including primitive values, explicit/sequential structs and the admitted vectors. C# assignment commonly emits `ldobj`/`stobj`; the fixtures deliberately test `cpobj` itself. Runtime agreement for the supported type/layout profile, including padding, remains an assumption beyond the Lean operational semantics; these tests are evidence, not a proof of the JIT.

References carry allocation identity and offset, not nominal CLR type tags. Relating a `cpobj` proof to runtime execution assumes that both references designate storage compatible with its validated type token, as required by the [opcode contract](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.cpobj?view=net-10.0). Byte-level access safety alone does not establish that nominal type compatibility.

## Struct instance calls

The extractor admits direct calls to methods on validated reference-free structs. The implicit `this` argument is a managed reference, not an aggregate snapshot; field accesses use existing allocation, permission, initialization and lifetime checks. By-value struct parameters still copy values into their own frame storage. Parameter assignment/addressing accounts for the shifted argument indices.

Direct calls to a void instance constructor are allowed on existing struct storage. Such calls do not allocate an object or bypass initialization checks. `newobj` for admitted structs allocates zero-initialized caller-owned temporary storage, passes a managed-reference `this` to the constructor, requires a void return and reads back a checked aggregate snapshot. Constructor calls propagate arithmetic and memory faults. The temporary remains owned by the caller until frame cleanup; resource exhaustion is not modelled. Zero-initialized fields follow the CIL construction contract; correspondence of padding bytes and physical runtime layout remains a runtime assumption. Class instance methods, indirect/virtual dispatch and generic declaring types remain unsupported.

## Integer enums

Same-assembly, non-generic enums use the storage of their validated underlying integer type: `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long` or `ulong`. The extractor validates the `System.Enum` base identity and the single `value__` instance field before normalizing types for execution. Method signatures retain enum names for artifact identity. Narrow enum loads and returns use the same truncation and sign/zero extension as their underlying integers; enum fields use that integer's size and alignment.

All underlying bit patterns are admitted, including values without a named constant and combinations of flags. This follows the unboxed enum execution model in [ECMA-335, partitions I.8.5.2 and I.12.1](https://ecma-international.org/wp-content/uploads/ECMA-335_6th_edition_june_2012.pdf). This does not add boxing, `System.Enum` instance methods, reflection or external enum dependencies. Metadata validation and its translation to existing Lean integer operations remain part of the extractor trust boundary.

## Portable bit helpers

`CIL.ScalarIntrinsics` defines rotations using Lean bit-vector rotations, population and zero counts by enumerating the value's bits, and endian reversal by reversing bytes. `Intrinsic.scalar` reuses the existing intrinsic dispatch without hardware requirements; profile-equivalence proofs cover this new family. The finite 32-bit count representation gives the .NET rotation count modulo 32/64, including negative `int` values.

Integer logarithms use Lean's natural-number `log2`, including zero mapping to zero. Rounding up constructs the power of two determined by the leading-zero count of the wrapping predecessor; truncation gives zero for zero input and overflow. Power-of-two checks require a single set bit and, for signed operands, a clear sign bit. Native overloads use the admitted 64-bit target. Byte-sized endian reversal preserves the low byte with the declared signed or unsigned extension.

The trust boundary includes correspondence between these definitions and the selected .NET 10 `BitOperations` and `BinaryPrimitives` overloads. Exact signature/scope validation and boundary/runtime comparison tests support that correspondence; they do not verify CoreCLR or a JIT. See the [BitOperations API](https://learn.microsoft.com/en-us/dotnet/api/system.numerics.bitoperations?view=net-10.0) and [ReverseEndianness API](https://learn.microsoft.com/en-us/dotnet/api/system.buffers.binary.binaryprimitives.reverseendianness?view=net-10.0).

## Caller proofs and published library contracts

An imported library contract is a hypothesis of the caller theorem. The theorem
has the form `forall linked, Links Extracted.program linked ->
Extracted.ImportsHold linked -> claim linked`. Generated import conditions use
fully qualified canonical contract predicates. The library's implementation
proofs and full-verification bundle are not needed for this caller check.

The consumer audits the supplied interface sources and their canonical contract
closures. `leancil-audit` computes both from the kernel-replayed interface oleans,
in one walk per root that visits each declaration once. The closure representation includes definition values, theorem and
inductive types, constructor metadata and computational recursor metadata/rules.
It removes binder names and expression metadata, uses de Bruijn indices, and
normalizes universe binders. Imported framework/toolchain module identity defines
the stop boundary. Custom axioms, sorry, unsafe/partial declarations, unbound
variables and missing opaque values are rejected. The ordinary caller theorem
axiom allowlist and kernel replay policy are unchanged.

Every supplied interface module is independently kernel-replayed before its
compiled artifacts enter the accepted snapshot. Published certification does not
exempt interface declarations from this check. Compilation and an axiom audit
alone cannot detect an unchecked declaration inserted by an elaborator. This
replay checks interface source declarations; it does not require a library's
implementation proof or a full-verification bundle.

The implementation-to-contract assertion is accepted from published certification,
as schema-4 reports state. This is separate from the kernel-checked caller
reasoning. Sidecar/DLL hashes establish identity; they do not authenticate a
publisher or prove a library implementation theorem. The supplied certification
theorem, statement and statement digest are provenance records here. Full
implementation verification is a separate producer operation.

Named type-initialization premises are part of the digest-bound export descriptor,
scoped by full assembly identity, type and profile. Export checks bind the exact
list to regenerated extraction through a kernel-checked, structurally audited
equality. Import validation checks local type constructors and exact propagation
from dependency contracts. Caller artifacts and reports retain the inherited
premises. This certifies which runtime assumptions accompany the CIL proof; it
does not model CLR initialization or establish that an initializer ran. Exported
constructor-initialized field values and forced-full initialization premises remain
unsupported.

`--force-full-verify` instead rechecks the library proof and composes it with
the caller theorem. It elaborates the source bundle of every library in the
caller's reachable dependency closure, possibly from different publishers, with
the verifier's privileges. It is sound only when none of those bundles can change
the toolchain, extractor, caller artifacts, other bundles or outputs: run
untrusted bundles in an isolated, read-only environment without network. See
[Independent imported-library verification](FULL_VERIFICATION.md).

Deployment must bind the exact implementation bytes, method/signature/profile
and a library implementation satisfying the published contracts. A false or
unsatisfiable published contract can make the caller theorem vacuous. Retaining
`Links` and `ImportsHold` exposes this condition; it does not prove satisfiability.
A successful report must be read with that deployment obligation. Reference-only
authoring checks do not produce a deployment certificate.

## Exception documentation lint

`lint-exceptions` is a diagnostic experiment. Its potential model sites are
structural observations, not proved exception behavior. XML declarations and
prose are untrusted. A documented exception absent from this limited model is
not evidence that the runtime cannot raise it. Lint does not check proof terms,
alter preconditions or issue a verification receipt. The selected XML bytes
are recorded but are not independently bound to the DLL build.
# Typed import metadata

Format 2 imports bind exact closed generic instances and imported byref struct
layout metadata. `LayoutProjectionValid` checks the signature-scoped raw catalog
against selected artifact entries, including nested reindexing and computed
layout equality. Required `ImportedLayoutsValid` evidence checks published versus
selected raw values, `LayoutsValid`, unique identities and typed signature
coverage. The extractor also compares those values with the selected pinned DLL
metadata. These propositions do not verify Cecil decoding or establish CLR
correspondence beyond the existing admitted layout model. Reference-only
interfaces and caller proof caches gain no new authority. See
[TYPED-IMPORTS.md](TYPED-IMPORTS.md) for the supported subset and rejection rules.

### Reference observations

`brtrue`, `brfalse`, `ceq`, `beq` and `bne.un` observe allocation-relative
references, including readonly views, without reading bytes or granting authority.
Non-null operands must pass formation and lifetime checks. Equality compares offsets
within one allocation and distinguishes interiors of different allocations. A comparison
between different allocations involving an end pointer is unsupported: allocation
identities do not establish whether adjacent runtime addresses coincide.

Bounded `ldnull` emits the existing null-reference value, while scalar evidence tracks
its raw object-null kind separately from managed references. It can be truth-tested,
compared with another object null, duplicated or discarded. It cannot justify object
parameters, locals or results, or a comparison against a managed reference. The scalar
certificate binds the raw null literal, comparison operation and branch target exactly.

Pointer subtraction and unsigned ordering require live, well-formed references. Differences
and orderings additionally require both references to identify the same allocation; no relative
runtime addresses are inferred from different allocation identities. The runtime correspondence
assumes an allocation occupies one contiguous, non-wrapping address interval. Within that
interval, unsigned address order matches offset order and address subtraction cancels its base.
Differences retain their native-width two's-complement representation. Subtracting an int32 or
native byte displacement reuses checked wrapping reference arithmetic and retains readonly
restrictions. None of these observations reads, initializes or grants authority over storage.
