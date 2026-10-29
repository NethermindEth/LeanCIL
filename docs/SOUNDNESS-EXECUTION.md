# Execution model and preservation guarantees

## What is defined and proved

Dynamic stack allocation uses the existing allocation-relative memory model. Each successful
nonempty `localloc` creates a fresh frame-owned allocation, grants access to exactly its byte extent
and charges its size rounded to 16 bytes against the activation's resource quota.
`Memory.stackLimit` defaults to zero and admits at most 65,536 bytes per activation. A proof using a
positive quota must justify that deployment assumption; this quota excludes the runtime's ordinary
frame, call and probing overhead and does not establish available physical thread-stack space. The
model reports `stackAllocationFailure` when the quota is insufficient. That resource failure is not
automatically a named CLR exception, nor does a successful model execution prove that the runtime
cannot exhaust its physical stack.

The emitted initialization flag must match the raw method's `localsinit` bit. Without it, new bytes
remain unreadable until written; with it, the payload is zero-initialized. A zero-byte request
returns null without reserving storage. Frame exit expires all dynamic allocations, and the existing
return checks reject escaped references and spans. Pointer values retain allocation provenance;
numeric address fabrication remains unsupported. Memory equivalence requires equal stack quotas, and
frame records track the charged dynamic bytes.

These initialization and lifetime rules follow the [CLI localloc
specification](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.localloc?view=net-10.0).
Zero-size null results and 16-byte reservation rounding follow the .NET 10.0.0 CoreCLR
[x64](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/jit/codegenxarch.cpp) and
[ARM64](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/jit/codegenarm64.cpp)
implementations. This source correspondence is an explicit runtime assumption, not a proof of the
JIT or of resource availability on every deployment.

Concrete constrained struct calls retain their original prefix and interface slot in raw
specialization evidence. A mandatory Lean validator independently resolves the slot from the
serialized type, interface, method and explicit-override declarations, then checks the emitted
direct-call target, signature and closed generic owner arguments. Explicit overrides bind both the
method token and closed interface identity, distinguishing instantiations with identical signatures.
Faithful metadata decoding and complete serialization of those declarations remain trusted. The
admitted subset has no runtime vtable lookup or boxing fallback; this does not prove general CLR
dispatch correct.

`CIL.Safety.RuntimeExceptions` adds a fixed naming view of checked execution faults. `RaisesCLR` and
`OutcomeContract.HoldsCLR` name `.thrown exception` directly, arithmetic overflow as
`System.OverflowException`, and integer divide-by-zero as `System.DivideByZeroException`. They
require an actual checked invocation with that fault. All remaining faults, including invalid
operands, bounds failures, unsupported instructions, invalid state and fuel exhaustion, map to no
named exception. The mapping does not change the interpreter, `.thrown`, `Raises`, or existing
outcome-contract proofs. Handler execution remains unsupported. The admitted runtime correspondence
assumption still applies; a mapping theorem does not prove a CLR implementation correct.

Intraprocedural cycles are admitted by a worklist analysis. Constant facts at a control-flow join
can only weaken to unknown; changed facts revisit successors until a fixed point is reached. Stack
heights and tracked stack types must agree at backedges as at other joins. This validation is part
of the trusted extractor, not a proof of termination. Recursive managed call graphs remain rejected.

`CIL.Safety.loop_terminates` proves successful finite checked execution from a supplied invariant, a
natural-number measure that strictly decreases, and kernel-checked execution segments. Each segment
relates the actual interpreter before and after an iteration for every continuation fuel budget.
Exit cases must prove the postcondition and successful return; `ensures_of_loop` includes checked
frame setup and yields the existing `Ensures` specification. `loop_terminates_induction` instead
assumes termination at every invariant state of smaller measure, so an iteration may cross a call
through a proved `MethodContract` whose fuel stays existential. `loop_outcome_induction` states the
same rule for `LoopOutcome`, which fixes one outcome for the loop: normal return, or exactly
`.thrown exception` through `RunRaises`, so unsupported instructions, invalid state and fuel
exhaustion never discharge an expected exception. Only continuing iterations carry invariant and
measure obligations, and `ensures_outcome_of_loop` lifts the result through frame setup to
`EnsuresOutcome`. Neither extraction nor finite fuel exhaustion proves termination. The countdown
example proves this for all 32-bit unsigned inputs from its stated empty caller memory; it makes no
runtime performance claim for large iteration counts.

Generic-method specialization is checked against independently serialized raw definitions by a Lean
structural-substitution validator. Faithful metadata decoding and raw-definition serialization
remain trusted. Concrete type arguments must satisfy the admitted constraints and layout rules.
Specialization copies the original instruction sequence and offsets, substitutes method and closed
declaring-type parameters in signatures, locals, type operands and nested generic calls, and
preserves branch targets. The ordinary CIL validator and Lean semantics then handle each closed
body. It adds no proof axioms or method summaries. Static calls on closed same-assembly generic
owners, including nested owners, are admitted. Canonical specialization arguments place method
arguments before owner arguments, with the scoped owner independently bound by the certificate.
Closed same-assembly sequential generic structs admit validated reference-free storage, fields,
direct instance calls and constructors. Their closed owner and substituted field types remain bound
to the original generic definition; unsupported layout forms and constraints requiring unsupported
runtime dispatch remain rejected. Repeated specializations are cached and extraction rejects more
than 256 distinct specializations.

Specialization can make `typeof(A) == typeof(B)` (or `!=`) a constant. `CIL.Extraction.foldRoles`
recognizes the exact five-instruction encoding from the raw closed body, with the exact
`System.Runtime` `GetTypeFromHandle` and `op_Equality`/`op_Inequality` call sites, and
`sameRuntimeType` decides the result from the substituted type operands. The feature certificate
accepts only `nop` for the operands and the decided word for the comparison, propagates that word
for pruning, and rejects any non-fallthrough edge into the last four instructions, so the emitted
operands, which push nothing, run only as a whole. Reachable type tokens and `System.Type` calls
outside a decided test are rejected. The identity rule is a runtime assumption: identical metadata
types denote one runtime type, and types with different full names are distinct. A full name in two
scopes may be forwarded to one type, so such pairs, decorated names and `void` (serialized without
its scope) are undecided and stay unsupported. This follows the JIT's folding of
[`Type.op_Equality`](https://learn.microsoft.com/en-us/dotnet/api/system.type.op_equality) for exact
type handles; it is not a proof of the JIT.

`foldRoles` also recognizes `throw new E(...)`: `ldstr`/`ldnull` loads, an exact allowlisted
`System.Runtime` exception constructor, then `throw`. `exceptionConstructor` lists the supported
exception types with parameterless or one-string constructors, and the two-string overloads of
`ArgumentException`, `ArgumentNullException` and `ArgumentOutOfRangeException`. Both extraction and
the feature certificate reject other types and constructor signatures; null arguments are admitted
only as strings, not as arbitrary constructor parameter types. The feature certificate accepts only
`nop` for the loads and `newobj`, and `.throw "E"` for the `throw`, and rejects any non-fallthrough
edge past the first instruction, so the raised object is always the one constructed. The checked
interpreter fails with `ExecutionFault.thrown "E"` at the `throw`. The model does not run the
constructor: resource exhaustion, such as an out-of-memory condition, is not distinguished. Methods
with exception handlers are rejected, so nothing observes the exception before execution ends.

`foldRoles` folds `stloc s; ldloca s` for a single-use primitive `ReadOnlySpan<T>` receiver: both
emit `nop`, leaving the span value on the stack. The feature certificate checks that the local has
exactly those two accesses and that the receiver is followed by `get_Length` or a single load or
constant before `get_Item`; branches cannot enter the folded sequence. Other supported span uses
retain typed local or parameter storage. Memory-backed views retain allocation identity, element
width, bounds and lifetime, and never grant authority or initialize bytes. Readonly views prohibit
stores through their element references but do not prevent writable aliases from updating the same
allocation. Primitive spans also admit `nint`, `nuint`, `char` and `bool`, using their existing 8-,
2- and 1-byte storage rules. Boolean bytes are not assumed canonical. Array `newobj` constructors
and implicit conversions, plus the array `MemoryExtensions.AsSpan` overloads with zero, one or two
int32 range arguments, form checked views without copying. Null arrays yield empty default views
only for zero start/count; invalid ranges raise `ArgumentOutOfRangeException`. The certificate binds
exact runtime assemblies, signatures, element identity, arity and mutability. In-place span
constructors admit an exact `ldloca` receiver followed by up to three argument loads/constants and
`call .ctor`. The receiver address cannot escape, and branches cannot enter the arguments or
constructor. Arguments execute at their original instructions; the checked constructor initializes
the typed local at the original call instruction, including on reinitialization. More complex
argument expressions and aliased receiver addresses are rejected. `Index`/`Range`, string and
`ArraySegment` overloads are unsupported. `CreateSpan<T>` over static data requires the start of an
immutable allocation whose size is a multiple of the element width; checked indexing stays within
that field.

Generated Lean and the identity manifest retain the original generic definition and concrete type
arguments; each specialized method retains its original metadata token. Assembly hashing and
regeneration-based artifact checks bind this information and the generated instructions to the
compiled input. These checks establish artifact consistency, not a formal proof of the extractor's
implementation.

`MemoryMarshal.AsBytes<T>` and `Cast<TFrom,TTo>` form checked views over supported primitive
integer, enum, validated aggregate or integer-vector storage. They retain the allocation-relative
reference and readonly status, read no bytes, and grant no authority. Cast lengths truncate
incomplete destination elements; a result longer than `Int32.MaxValue` raises `OverflowException`.
The evidence binds the exact generic types, source and destination widths, and runtime overload.
Misaligned views follow the modeled CoreCLR x64/ARM64 normal-memory convention described below; this
does not assert portable support on arbitrary architectures.

Aggregate spans bind element widths to independently computed layouts through mandatory layout-use
evidence. Layout selection uses the validated target architecture, including alignment of vector
fields. Integer-vector spans bind exact admitted type names and widths. Parameters, locals,
reference factories, slicing, reinterpretation and copies retain allocation identity, lifetime and
capability; view formation never initializes bytes. Typed vector loads and stores preserve snapshot
initialization masks. Span copying still requires initialized readable source bytes. `Fill` repeats
the captured aggregate/vector snapshot with a single checked range write, preserving every
initialization bit; an aliased source is captured before any destination write. Unspecified
low-lane-only vector values remain rejected by the existing observer guard. Empty fills need no byte
authority, and nonempty fills need destination write authority but no readable or initialized
destination bytes. `Clear` instead initializes all bytes in the view.

Span `IsEmpty` and `GetPinnableReference`, and admitted array `GetArrayDataReference`, validate the
view without reading storage. Empty spans yield null pinnable references, whereas empty arrays
retain their data reference; null arrays raise `NullReferenceException`. Readonly span references
stay readonly. Exact runtime identities, signatures, element types and operations are checked
independently; these observations grant neither byte access nor alias exclusivity.

The 48 admitted `BinaryPrimitives` signed/unsigned 16-, 32- and 64-bit byte-span read/write
signatures bind endian choice, width, signedness and try behavior in the Lean evidence validator.
Short ordinary operations raise `ArgumentOutOfRangeException`; short try-reads write initialized
zero through the output reference, and short try-writes leave memory unchanged. Successful reads
capture their source before updating an aliased output. Source initialization and destination write
authority remain checked. Correspondence to the named .NET 10 runtime APIs remains a runtime-model
assumption; the certificate checks the translation, not the runtime implementation.

Block initialization and copying use allocation-aware byte reads and writes. Nonempty accesses check
bounds, lifetime, permissions, alignment and GC-reference exclusion; copying additionally requires
initialized source bytes and rejects every overlapping region. The unprefixed block alignment is
eight bytes on the admitted target, reduced to 1, 2 or 4 by a validated `unaligned.` prefix.
Zero-byte operations access no memory, including when passed null references. This zero-length
convention is checked against the admitted runtime; it does not model exception handling or
arbitrary pointer addresses.

The block operations follow the [CLI
copy](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.cpblk) and
[initialization](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.initblk)
restrictions. Ordinary prefixed loads and stores retain the existing byte-aligned CoreCLR target
convention. Prefix validation is part of the extractor trust boundary: valid operands and followers
are required, and branches cannot skip a prefix while targeting its following instruction.

Native integers are represented as 64-bit words only after target-profile validation (64-bit,
little-endian). Their storage uses existing checked eight-byte homes and managed references. No
native integer can be dereferenced as an arbitrary address. `NativeOperands` tracks evaluation-stack
types through the admitted control-flow graph, including backedges: only metadata-proven
native/int32 arithmetic and comparisons receive `Op.nativeBinary`, which sign-extends the int32
operand, except that unsigned checked arithmetic zero-extends it. Mixed native/int32 unsigned
conditional branches are rejected with an explicit `conv.i`/`conv.u` diagnostic: CoreCLR widens
constants differently from arguments in this path, and inlining can change that provenance.
Same-width branches remain supported. The wrapper has an explicit scalar-operation allowlist and
cannot dispatch memory operations, calls, hardware features or nested wrappers. The legacy pure
interpreter rejects the wrapper; native mixed-operation proofs use the checked interpreter.

[Pinned x64 and ARM64 probes](evidence/native/README.md) execute 4,100 cases per architecture on
official .NET 10.0.0 binaries: 3,600 admitted cases agree with the mathematical oracle; 500
ambiguous mixed unsigned branches are rejected, including 38 recorded divergences from the old rule.
The evidence includes exact CIL, operands, results, runtime and binary hashes, official archive
checksums, and pinned public importer source. The binary internal build commit differs from the
public release tag, so this does not claim an exact reproducible source-to-binary build or a general
proof of runtime equivalence.

Checked integer conversions interpret the input according to the opcode's `.un` flag, then check the
mathematical value against the destination bounds. Signed narrow results are sign-extended in their
32-bit stack slot. Native destination widths come from the validated target profile, not the machine
performing extraction. Floating-point conversion behaviour is outside this model.

Checked integer addition, subtraction and multiplication compute their result over `Int` before
checking the signed or unsigned destination range. Overflow cannot silently wrap into a successful
result. The universal extracted addition examples prove natural-number addition whenever the sum
fits, and the runtime comparison matrix checks both successes and faults for all six encodings at
both widths.

Integer division and remainder use an explicit `ArithmeticFault` result, separate from
malformed-state and memory faults. Zero divisors and the signed minimum / -1 pair terminate checked
execution with located faults. Signed quotient uses truncation toward zero, not Lean's Euclidean
division. Signed remainder uses the corresponding truncating remainder. These faults do not
implement managed exception objects, handlers or unwinding.

For signed minimum remainder -1, the model selects the overflowing runtime behaviour documented for
Intel platforms in [the opcode
reference](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.rem). The
regression suite compares the emitted CIL with the executing .NET runtime, including this case. This
is an explicit runtime correspondence assumption, not a proof of architecture-independent CLI
behaviour; proofs requiring successful execution of that input are not supported.

`CIL.Semantics` defines a functional byte-memory execution model, with wrapping bit-vector
arithmetic, instruction-level failure, calls and explicit finite fuel. Its memory addresses do not
themselves certify physical allocations. Its successful execution theorem is not a memory-safety
certificate.

`CIL.Safety.Memory` adds allocation identities, storage kinds, layouts, live/dead state, initialized
bytes, read/write views, end sentinels and managed references. Allocation identities increase and
are never recycled. `CIL.Safety.Execution` checks every memory/reference instruction and frame
transition. It uses the arithmetic interpreter only through the existing value-only whitelist.
Unknown operations cannot fall through to unchecked memory operations.

Successful checked execution excludes the model's faults on the executed path. Library theorems
establish well-formedness preservation, allocation extension, frame ownership, expiration,
caller-memory preservation, valid live values, static-world consistency and running/returned-state
invariants. `InvocationCertificate` records successful execution plus these state properties under
its stated initial-state premises. Premises such as valid views, well-formed input memory and valid
initial references are obligations on callers, not facts inferred from an arbitrary DLL.

`Ensures` describes total correctness of a specified method over a user-supplied precondition and
postcondition. A `VC` is a finite execution condition, not a decision procedure that automatically
finds loop invariants or arithmetic specifications. The symbolic-execution tactic follows actual
generated instructions and optional **proved** summaries. Failed summary elaboration restores the
Lean environment and continues raw execution.

## Aggregate generalisation

The checked interpreter represents general reference-free aggregates as byte lists. A local's
physical size is a bounded `LocalKind.aggregate` size; initialization allocates that exact size.
`localNumber` rejects snapshots of the wrong length. Generic load/store/init operations carry their
byte size, and generic field instructions carry validated byte offsets and scalar widths. They use
the same access and lifetime machinery as scalar/vector memory.

The extractor admits explicit layouts with a positive declared size and sequential layouts computed
from validated primitive, enum or nested aggregate fields, packing and declared size. Both are
reference-free and limited to 65,536 bytes per aggregate; sequential padding follows the runtime
rules below. Overlapping explicit fields remain possible and follow the byte-memory semantics.
Generated `AggregateLayout.Valid` theorems check the emitted layout bounds in Lean. Metadata-to-Lean
correspondence remains part of the extractor trust boundary.

Fixed 256-bit snapshot-home operations use **vector** names to distinguish them from general
aggregates. Lane operations are explicitly vector-lane operations. They do not stand for arbitrary
struct layouts. Validated reference-free nested
layouts and same-assembly value constructors are exposed by extraction; reference-bearing field
layouts remain unsupported.

## Method-body embedding

`MethodEmbeds program index expected` (`CIL.Embedding.Basic`) states that method `index` exists and
that `Embeds expected actual map` holds for its body `actual` and a pc map `map`; expected pc `p`
maps to `map.getD p actual.code.length`, so pcs outside the map go past the end of the actual body.
`Embeds` requires equal profile, return shape, locals, local kinds, vector locals and arguments,
parameter homes and static descriptor list, that pc 0 maps to pc 0, and, for every live expected pc
(any instruction except `.unsupported`):

- the actual instruction at the mapped pc is the expected one with every code target renamed through the map;
- a static address at the mapped pc resolves the same descriptor;
- an instruction that can resume at the next pc (anything except `branch`, `ret`, `throw` and `.unsupported`, and including calls) maps its successor to the next actual pc.

Each condition is a list equality or a Boolean check that the kernel decides by evaluation; no
equality instance on `Op` is involved.

`CIL.Safety.run_refines` proves, for programs related by `ProgramRefines` (every method embedded,
equal program-wide static descriptors), that a successful `CIL.Safety.run` of the expected program
at any pc gives the same result, memory included, for the actual program at the mapped pc with the
same fuel. `invoke_refines`, `MethodEmbeds.invoke` and `MethodEmbeds.certificate` transfer
successful invocations and `InvocationCertificate`s from `program.set index expected` to `program`;
`ProgramRefines.set` composes embeddings of several methods. The step lemma `step_relabel` covers
every `Op` constructor.

Thrown exceptions transfer through the same induction. `run_outcome_refines` relates every expected
outcome that `Transported` admits, a result or a fault whose kind is `.thrown exception`, to the
actual outcome at the mapped pc, with the fault moved by `LocatedFault.relocate`: the method and
exception are unchanged and the instruction becomes the pc its own method's map assigns, so an
exception propagated from a callee is located in the callee. `run_refines` and `invoke_refines` are
its successful instances; `run_raise_refines`, `invoke_raise_refines` and `Embeds.invoke_raise`
state the relocated fault, and `Raises.of_refines`, `OutcomeContract.Holds.of_refines`,
`MethodEmbeds.raises` and `MethodEmbeds.holds` (`CIL.Safety.Embedding.Outcomes`) transfer `Raises`
and both clauses of an outcome contract; `MethodContract.Holds.of_refines` and
`MethodEmbeds.method_holds` transfer a normal-return method contract. The step lemma `step_raise`
shows that only `throw` raises by itself and that every other throw, such as a span index out of
range, comes from a computation both steps share. These theorems depend only on `propext`,
`Quot.sound` and `Classical.choice`.

Scope and limits:

- The transfer covers success and named thrown exceptions only. Fuel exhaustion, `.unsupported`, memory, arithmetic and invalid-state faults do not transfer: the actual program may have code or methods where the expected one faults, and the actual body may fault where the expected body is dead. No handler or post-throw memory is modeled.
- Dead expected pcs are unconstrained: an `.unsupported` instruction faults whenever it executes, so a successful expected run never reaches one. Actual pcs outside the image of live expected pcs are unconstrained as well; the simulation never visits them.
- The relation is syntactic and conservative: an inserted live instruction, even a `nop`, on a reachable path is rejected.

`cil_embed` (`CIL.Embedding.Tactic`) computes the map outside the kernel by aligning live
instructions, following fallthroughs and branch targets. The alignment is untrusted: the proof term
passes the map to `Embeds.mk` with every field closed by `Eq.refl`, and the kernel checks it against
the body reduced from `program[index]?`. A wrong map can only make the kernel reject the proof.
Before building the proof, the tactic evaluates the same conditions and reports the first violated
one.

### Dead locals

`MethodEmbedsDeadLocals program index expected` relaxes only the local declarations:
`EmbedsDeadLocals expected actual map` requires `Embeds expected (actual.withLocalsOf expected)
map`, so every other field and the code are checked as above, and that `actual`'s locals and local
kinds are `expected`'s followed by trailing locals that are each a `.reference` or `.span width
writable` initialized to `.nullRef` or `.unmodeled`, with span widths greater than zero and less
than `2^64` bytes. It also requires `expected`'s kinds and initializers to have equal length, every
opaque vector local to lie among the kept locals, and no parameter homes, which the frame places
after the locals and the extractor addresses by local count. Frame entry creates such a dead local
as a root or span slot without allocating, so `enterFrame_deadLocals` shows that `actual` enters the
frame of `actual.withLocalsOf expected` with the dead slots appended, in the same memory with the
same allocation identities. `StepAppendLocals` is proved separately for every instruction
constructor in `CIL.Safety.Embedding.AppendLocals`; the dispatcher `step_appendLocals` shows that a
step that succeeds or throws behaves the same with the padded frame, since every local an
instruction reads is below the padding, and `run_padded` lifts it to whole runs.
`EmbedsDeadLocals.invoke_outcome` composes this with `invoke_outcome_refines`;
`MethodEmbedsDeadLocals.invoke`, `.raises`, `.method_holds`, `.holds` and
`EmbedsDeadLocals.invoke_raise` (`CIL.Safety.Embedding.DeadLocals`) are its instances, with the same
transfer limits as above. `InvocationCertificate`s are not transferred, since their live state names
the frame. There is no `MethodEmbedsDeadLocals.refines`: the padded run is related to the unpadded
one directly, not through a `ProgramRefines`, so it does not combine with other replacements through
`ProgramRefines.set`. To replace other methods as well, prove their `MethodEmbeds` against
`program.set index expected`, the program with the dead-local method already replaced, and chain
each `.invoke` with this one's.

Trailing byref, pointer and span dead locals are covered. Span slots retain their element width and
mutability, and hold an empty view or an unmodeled value without allocating. Unsupported span widths
and nonempty scalar initializers remain rejected by the kernel-checked condition. Numeric and
interspersed dead locals are outside this exact-memory embedding: their homes change later
allocation identities or local operands. They use the separate allocation refinement below.
`cil_embed` proves `MethodEmbedsDeadLocals` goals too and names the violated local condition.
`CIL.Safety.AllocationRefinement` supplies a separate checked simulation for numeric and
interspersed dead declarations. `MethodRenaming` retains local kinds and initializers in order and
checks all relocated local operands while preserving method indices and execution metadata. Both
methods must satisfy `OrdinaryFrame`: no opaque vector locals or vector/parameter argument homes,
bounded layouts and supported span widths. `LocalDeclarations` preserves each retained initializer
and checks inserted values with `InitializerFits`. Their actual initialization writes affect only
fresh private homes outside the mapped allocation image; null managed slots do not allocate. Invalid
kinds, widths and initializer values are rejected. Actual source entry success supplies successful
retained initialization; the target entry is proved. The initial memory must be well formed and its
static bindings bounded by the allocation counter. These restrictions are premises of the public
theorems.

The relation is injective over the source allocation prefix. New paired allocations extend it
without moving existing images, and extra target homes remain private outside that image. A separate
activation relation preserves frame storage kinds and ownership through nested calls and expiry.
`StepRenaming.stepTransport` proves the complete checked dispatcher; recursive execution extends the
relation through every later allocation. The public `ProgramRenaming.invoke_scalars` and
`.invoke_confined` instantiate this theorem and transfer exact scalar results and `MemoryBelow`
claims on the initial caller prefix. `.raises` also requires valid input arguments and preserves
named exceptions. No consumer-supplied step simulation is assumed. These results do not assert
identical final allocation counters, identical fresh references or arbitrary reference-valued
postconditions.

`MethodContract.Holds.of_allocationRenaming` preserves the same contract and footprint. Its explicit
premises require readiness from the original precondition, scalar result encoding and stability of
the original postcondition under the proved caller-prefix relation. Confinement is transported from
actual successful executions, rather than assumed for the renamed result.

## Shared proof contracts and reduction

`RunTrace` exposes the four successful control-flow cases of checked execution. `FrameSetup`
composes setup effects, while `InstructionContract`, `StaticInstructionContract` and `StepContract`
combine effects and conditional value-validity results. Their constructors and theorems are kernel
checked; clients retain the original well-formedness and validity hypotheses. Sharing these proofs
changes neither the interpreter definitions nor the trusted base.

Checked symbolic execution composes proved instruction equations. Its `rfl` path uses definitional
equality checked by the kernel; equation rewriting and simplification also produce checked proof
terms. Return candidates are limited to fetched return instructions, and fact-dependent steps retain
their explicit hypotheses. These tactics cannot turn an unresolved obligation or failed candidate
into a correctness certificate. See [the proof guide](PROOFS.md) for their use and [validation
coverage](VALIDATION-PROOFS.md#proof-automation). Compiled artifact size and elaboration speed do
not change the theorem's logical guarantee.

