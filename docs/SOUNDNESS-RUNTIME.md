# Runtime and storage assumptions

## Runtime assumptions

Deployment must use the selected supported 64-bit, little-endian .NET 10 profile. Feature flags
describe runtime/OS-visible availability and remain fixed during execution. ISA-specific operations
require their features; portable operations use software semantics. Profile validity is checked,
but the verifier does not discover a deployment's actual CPU, runtime or resource availability.
See [runtime profiles](RUNTIME-PROFILES.md).

`IntPtr.Size`, `UIntPtr.Size` and `Environment.Is64BitProcess` use the profile's required
64-bit process assumption. Their exact getters translate to constants `8`, `8` and `true`;
they do not inspect the verifier host or establish a deployment's actual process width.

| Area | Model convention / deployment premise | Excluded claim |
| --- | --- | --- |
| Numeric operations | Bit-vector wrapping; checked arithmetic/conversions use mathematical bounds; signed division truncates toward zero | Floating-point conversion and arbitrary CLI/runtime behavior |
| Native integers | 64-bit representation; metadata-bound native/int32 widening, with zero extension for unsigned checked arithmetic | Native/int64 arithmetic mixtures, numeric fabrication of references |
| Mixed unsigned branches | Native/int32 unsigned conditional branches require explicit conversions | A uniform implicit widening rule: CoreCLR argument/constant provenance can affect the result |
| Signed minimum remainder -1 | Overflow, matching the admitted runtime behavior | Architecture-independent CLI success for that input |
| Ordinary memory access | Alignment 1 on admitted CoreCLR x64/ARM64 normal memory | Portable natural alignment, device memory, volatile/atomic/concurrent execution |
| Initialization | `initobj` and zero-initialized homes clear the full reference-free layout, including padding | Unknown locals being readable before a write |
| Resources | Requested modeled stack/heap storage can be supplied by the runtime | Absence of physical stack/heap exhaustion |

The [native runtime evidence](evidence/native/README.md) records exact CIL, inputs, outputs, runtime
and binary hashes on pinned x64/ARM64 binaries. It is differential evidence, not a CLR proof or a
reproducible source-to-binary build. Small integers use i32 stack values; narrow stores truncate and
loads/returns sign- or zero-extend by the declared type. Boolean bytes need not be canonical.

### Pointer element offsets

`Unsafe.Add<T>(void*, int)` and `Unsafe.Subtract<T>(void*, int)` use the same checked,
allocation-relative element offsets as their managed-reference counterparts. Runtime correspondence
assumes .NET 10's native-width multiplication by `sizeof(T)` followed by addition or subtraction.
They admit existing storage for supported integer,
enum, vector and reference-free aggregate types; neither fabricates addresses nor grants authority.
Negative offsets wrap at native width before the resulting reference is checked for lifetime and
bounds. Null and invalid resulting references fail. Exact signature checks bind the pointer overload;
primitive/vector stride and signedness are checked directly, and aggregate stride uses layout evidence.

### Unspecified vector lanes

`v128Low64 low` represents every vector with that low lane. `checkedIntrinsic` admits only consumers
proved independent of the upper lane: reinterpretation, lane-zero extraction and the count operands
of the admitted AVX2 logical shifts. Reinterpretation preserves uncertainty. Other observations,
byte stores, bitcasts, returns and call/constructor arguments reject unspecified bits. Internal
dup/pop and eligible opaque locals may forward them. `invoke_return_known` and `step_call_known`
state the boundary guarantees; a contract cannot expose an unknown lane as a concrete value.

`OpaqueLocalsValid` requires a reachable admitted producer and independently recomputes eligibility
from raw local uses, excluding address-taken locals. Opaque by-value helper parameters are unsupported.
Agreement between the permitted consumers and the actual JIT remains a runtime assumption.
See [intrinsic semantics and coverage](SIMD.md) and the [runtime-call inventory](COMPILER-COVERAGE.md).

### Arrays, views and bulk memory

Supplied arrays carry exact element identity, length and allocation-relative backing storage.
The caller must relate that descriptor to the runtime array. Primitive integers, enums, admitted
aggregates and integer vectors share checked lifetime, initialization, bounds and authority rules.
Reference-element and multidimensional arrays, covariance and addresses of array roots are excluded.
Valid null/index failures raise their named exceptions; invalid descriptors, expired storage and
missing authority remain model faults and cannot discharge those exceptional contracts.

`newarr` allocates primitive integer/bool/char/native arrays and same-assembly integer-backed enum
arrays. Enum payloads start at zero even when the enum declares no zero member. Fresh non-null
identities survive frame return, including for empty arrays. Payloads start zeroed and writable.
Negative lengths raise `OverflowException`; lengths above `0x7fffffc7`, invalid native extents and
allocator inconsistency are model faults. The [CoreCLR ceiling](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/gchelpers.cpp)
does not establish available memory. GC, object headers and out-of-memory behavior are not modeled.

Spans, slices, array conversions and `MemoryMarshal` views preserve backing identity and capability;
creating a view neither reads/initializes bytes nor grants byte authority. Readonly views permit
other authorized aliases to write. Cast lengths truncate incomplete elements and raise overflow
above Int32.MaxValue. Single-reference constructors require a live checked reference; pointer
constructors require a checked extent, not a numeric address. Raw `void*` is admitted only at exact
supported helpers/constructors. Arbitrary pointer element types and reference-bearing layouts remain
unsupported. [OPCODES](OPCODES.md) specifies the exact constructor and receiver forms.

Aggregate/vector loads and stores preserve snapshot initialization masks. Fill captures its value
before writing, including aliasing cases, and preserves those masks; Clear initializes every byte.
Nonempty destinations need write authority, not prior readability. Copy requires initialized source
bytes. Empty operations grant no authority. Empty spans have null pinnable references; empty arrays
retain their data reference. Null array data-reference access raises its named exception.

Block copies require disjoint regions; `cpobj` permits identical addresses but rejects partial
overlap. Nonempty block accesses check lifetime, bounds, permissions, initialization, alignment and
GC-reference exclusion. Block alignment is eight unless a valid `unaligned.` prefix selects 1/2/4.
Zero-byte blocks access no memory, including through null. Prefix operands/followers and entry edges
are validated; correspondence to CoreCLR remains assumed.

`BinaryPrimitives` span operations bind width, endian order, signedness and try behavior exactly.
Short ordinary operations raise `ArgumentOutOfRangeException`; short try-reads initialize the output
to zero and short try-writes preserve memory. Reads capture source before writing an aliased output.
These are runtime-helper assumptions backed by validation, not verified runtime implementations.

### Static storage

RVA storage is immutable and extraction-bound. Static keys hash full assembly/field identities;
hash injectivity is not assumed: extraction/import checks reject collisions, and composed full
verification proves `linkChecked`. Raw `link` alone supplies no collision guarantee.

`StaticRegistryValid` requires unique keys, distinct allocations and live immutable storage.
`StaticWorldValid` constrains the listed descriptors. Composition requires shared keys to have equal
descriptors in one memory; it neither merges memories nor infers disjointness from different keys.
First-use absence and repeated-call world-validity are distinct caller premises.

Constructor-initialized readonly values require named initialization assumptions and no later
unmodeled mutation. Recognizing unconditional permitted initializer stores and faithfully decoding
metadata are trusted. `StaticValuesValid` checks literal bytes or re-executes admitted initializer
computation without circular access to the values being justified. Profile-dependent initialization
must match deployment. Reflection and other unmodeled writers are excluded. Reports expose these
assumptions; they do not establish that initialization occurred.

## Argument storage

Assigned/addressed by-value parameters have private typed homes; loads, assignment and addressing
share those homes. Byref assignment changes a private root slot; writes through it affect its
referenced allocation. Addresses of byref slots are unsupported. Owned homes expire at return and
returned references are checked after expiry. Extraction binds parameter-home indices to raw uses.

The certificate permits word64/native interchange only at metadata-bound 64-bit storage/returns.
A known i64 store into an i32/narrow home is a terminal invalid-state case, never a conversion or
successful successor. Unknown values and mismatched homes cannot use that rule.
Null managed references are distinct from numeric zero. Access faults on null are not automatically
named throws; only explicit outcome mappings establish a named exception.

## Sequential struct layout

Admitted layouts are reference-free and bounded by 65,536 bytes. Sequential fields include supported
integers/enums, nested aggregates and admitted vectors. Closed same-assembly generic owners bind
their original fields, arguments and constraints to substituted layouts. Field order, packing, size
and target architecture determine offsets. Default packing is eight; nested alignment comes from
the child layout, capped by packing. Inferred sizes include tail padding, declared size cannot
truncate fields, and empty structs occupy at least one byte. Explicit overlap follows byte storage.

Open generic owners, explicit/auto generic layouts, reference/float fields, inline arrays and
recursive/depth-over-128 layouts are rejected. Vector512 fields are excluded because their aggregate
alignment is not modeled. Storage is managed layout, not interop marshalling. Correspondence to
[CoreCLR layout](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/classlayoutinfo.cpp)
is assumed; runtime probes and kernel layout bounds supply different kinds of evidence.

## Value tuples

Only the exact supported `System.ValueTuple<T1,T2>` identity with two equal-width primitive integer
fields is admitted. CoreCLR auto-layout can reorder mixed-width fields; those tuples, other arities,
enums/nested aggregates, tuple construction/methods and tuple fields inside structs are excluded.
Lean checks the equal-width auto-layout restriction. Faithful resolution and runtime ordering remain
assumptions; [tuple tests](../Tests/TupleDivision.cs) probe both admitted and reordered layouts.

## Typed copies

`copyObject_writes_snapshot` proves destination bytes equal the source snapshot and are initialized,
including padding. Access and initialization premises remain mandatory. References have provenance
and offsets, not nominal CLR type tags: relating `cpobj` to the runtime additionally assumes both
storage regions are compatible with its validated type token. Runtime tests are not a JIT proof.

## Struct instance calls

Admitted direct instance calls use a managed-reference `this`; by-value arguments have private homes.
Existing-storage constructors do not allocate or bypass initialization checks. Aggregate `newobj`
uses zeroed caller-owned temporary storage, a void constructor and checked snapshot readback.
Padding/layout correspondence and resource availability remain assumptions.

Tail transfers retire the caller frame before checking callee arguments, so references into retired
storage fail even if unused. Typed `ldftn`/`calli` identities carry exact closed signatures and
certificate-bound targets; integers cannot fabricate them. Tail cycles need termination proofs.
Only the admitted default-managed static signature subset is supported; imported/intrinsic tail
calls, unmanaged conventions, null table entries and mutable tables are excluded.

Immutable native handler tables require a faithful explicit runtime-slot binding, live static
storage, aligned initialized readable bytes and an exact catalog signature. Targets are supplied
identities, not decoded addresses. Each method has one supported indirect signature; table-pointer
handler signatures are excluded. This is not arbitrary mutable raw-pointer dispatch.

## Integer enums

Same-assembly non-generic enums retain identity but execute with their validated integer storage.
All underlying bit patterns are admitted, not just named constants. Narrow extension/truncation
follows the underlying type. Boxing, reflection, enum instance methods and external enum dependencies
are excluded; equal byte widths do not authorize replacing one enum identity with another.

## Portable bit helpers

Rotations use modulo-width counts; counts/reversal and log2 follow the scalar bit-vector model.
Log2(0) is zero. Round-up returns zero for zero/overflow; signed power-of-two tests exclude the sign
bit. Native overloads assume 64 bits. Primitive signed and unsigned 32-bit, 64-bit and native
`RotateLeft`/`RotateRight` overloads share the same bit-vector rotation model. Correspondence to
these primitive methods and the selected .NET BitOperations and BinaryPrimitives overloads remains
a runtime assumption backed by exact signature checks and boundary/runtime comparisons.
See [SIMD](SIMD.md) and [OPCODES](OPCODES.md).
