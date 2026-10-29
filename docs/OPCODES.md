# CIL opcode support

This table covers all 179 opcode encodings currently handled by the translator and describes the allocation-aware execution model used for memory-safety proofs. It is an inventory of implemented behaviour, not a claim that every listed opcode/operand combination has its own regression test, or that the model is equivalent to every .NET runtime.

- **Complete within the admitted model:** the opcode's operation is implemented for its admitted operands. Ordinary stack/value validity checks still apply.
- **Partial:** translation exists, but the row lists additional type, layout, control-flow or runtime restrictions. Unsupported operand shapes can fail during checked execution even when translation succeeds.
- **Unsupported:** no reachable translation exists; extraction rejects the opcode. All opcodes not listed in the translated-opcode table are unsupported.

Every row is subject to the common target restrictions: Release IL-only .NET 10 assemblies, 64-bit little-endian execution, admitted types, no exception handlers and validated reachable control flow. Ordinary managed calls retain an acyclic extraction order; checked tail transfers may form cycles. A translated method still requires a proof of the desired property. Exhausted fuel, invalid states and unsupported operations are failures, never implicit successes.

The initial extraction target is Release, IL-only **.NET 10**, 64-bit little-endian execution. Supported scalar operations include 32/64-bit wrapping arithmetic, bitwise operations, shifts, selected conversions/comparisons, conditional/unconditional branches, local and argument loads/stores, 64-bit indirect access, and acyclic managed calls to static methods and reference-free struct instance methods. Struct methods receive a checked managed-reference `this`; direct constructor calls on existing storage and `newobj` construction of validated structs are supported. Explicit- and sequential-layout reference-free aggregates use validated sizes and byte offsets; fields admit narrow, 32-bit, 64-bit and native integer storage, including same-assembly enums backed by the eight C# enum integer types and nested reference-free structs. Nested fields support references, snapshots and whole-value assignment, with validated packing and padding. Enum parameters, returns, locals, references and flags use the underlying integer semantics, including unnamed values. Boxing and `System.Enum` methods remain unsupported. SIMD models cover selected Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM operations, as enumerated in `CIL/SIMD` and `Extractor/RuntimeModels.cs`.

## Translated opcodes

Ranges below include every numbered form between the endpoints. `.s` denotes the actual short encoding, not a different semantic operation. Native `nint`/`nuint` values use `i64` under the validated 64-bit target. For mixed native/int32 arithmetic and comparisons, extraction tracks stack types and emits an explicit widening wrapper; invalid native/int64 mixtures are rejected. Mixed native/int32 unsigned branches (`bne.un`, `blt.un`, `bgt.un`, `ble.un`, `bge.un`, including short forms) are rejected because CoreCLR widening depends on operand provenance; insert explicit `conv.i` or `conv.u` to select same-width semantics. The wrapper sign-extends the int32 operand, except that unsigned checked arithmetic zero-extends it. Scalar `clt.un`/`cgt.un` still sign-extend, matching the admitted runtime. The wrapper preserves arithmetic faults and branch targets and cannot dispatch memory or calls. The rows below describe scalar operands after this widening; other mixed widths remain unsupported.

`i32` and `i64` refer to the model's 32- and 64-bit integer stack values; managed references are separate values, not integer addresses.

Same-assembly enums backed by `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long` or `ulong` use their validated underlying integer representation throughout these operations, including fields, argument homes and typed memory instructions. Narrow enum loads sign- or zero-extend exactly like the underlying type. Unnamed values are supported; boxing, `System.Enum` methods and external enum dependencies are not.

| Opcodes | Status | Implemented behaviour and restrictions |
| --- | --- | --- |
| `newarr` | Partial | Fresh zero-initialized primitive integer arrays, including native integers, `bool` and `char`. Int32/native lengths must be nonnegative and at most the .NET 10 CoreCLR ceiling `0x7fffffc7`; negative lengths raise `System.OverflowException`. Heap identity survives returns. Success assumes runtime-supported allocation size and available heap capacity; no GC, object-header or out-of-memory model. |
| `ldlen` | Partial | Length of a supplied integer, enum, reference-free aggregate or integer-vector array, or typed handler table, returned as a native integer. Null raises `System.NullReferenceException`. |
| `ldelema` | Partial | Checked element reference into a supplied integer, enum, reference-free aggregate or integer-vector array. The type token must match the array element type; null and bounds checks precede address formation. Grants no read/write authority and does not make uninitialized contents readable. References retain allocation lifetime across locals, calls and returns. |
| `readonly.` | Partial | Immediately precedes an admitted `ldelema`; branches into the following address instruction are rejected. Produces a restricted reference that remains readonly through byref locals, arguments and returns. Scalar reads are allowed, while stores and adapters that would discard the restriction fail. Other authorized aliases can still update the backing bytes. |
| `ldelem.i1`, `ldelem.u1`, `ldelem.i2`, `ldelem.u2`, `ldelem.i4`, `ldelem.u4`, `ldelem.i8`, `ldelem.i`, `ldelem` | Partial | Checked integer array reads; narrow loads extend according to the opcode. Typed `ldelem` also supports validated aggregate and integer-vector tokens, matching the exact array element identity and width. Scalar reads require initialized bytes; aggregate/vector snapshot reads retain initialization masks. All reads require read authority. `ldelem.i` and typed `ldelem` also select typed entries from supplied handler tables. |
| `stelem.i1`, `stelem.i2`, `stelem.i4`, `stelem.i8`, `stelem.i`, `stelem` | Partial | Checked integer array stores; narrow stores truncate. Typed `stelem` requires a matching integer, enum, aggregate or integer-vector token. Stores require write authority; scalar stores initialize the selected element, while aggregate/vector stores preserve snapshot initialization masks. |
| `ldc.i4`, `ldc.i4.s`, `ldc.i4.m1`, `ldc.i4.0`–`ldc.i4.8` | Complete within the admitted model | Push the encoded 32-bit integer constant. |
| `ldc.i8` | Complete within the admitted model | Push the encoded 64-bit integer constant. |
| `ldnull` | Partial | Push an object null for truth tests, equality with another object null, stack shuffles/discard, or a supplied supported array or typed handler-table slot/call/return. General object parameters, locals, returns and object-null/managed-pointer mixtures remain unsupported. |
| `nop` | Complete within the admitted model | Advance without changing the stack or memory. |
| `dup`, `pop` | Complete within the admitted model | Duplicate or discard a supported stack value; stack underflow fails. |
| `ldarg`, `ldarg.s`, `ldarg.0`–`ldarg.3` | Partial | Load admitted argument values; struct instance methods have a managed-reference `this` at index zero; narrow integers are truncated and sign- or zero-extended to `i32`. Reference values undergo validity checks; class instance methods remain unsupported. |
| `starg`, `starg.s` | Partial | Assign a private parameter home using its declared storage type. Narrow stores truncate; byref assignment changes the private reference slot. Does not overwrite the caller's by-value source. |
| `ldarga`, `ldarga.s` | Partial | Address the same private parameter home read by `ldarg` and written by `starg`. Addresses expire when the frame returns. Taking the address of a byref parameter is rejected; nested-reference storage is unsupported. |
| `ldloc`, `ldloc.s`, `ldloc.0`–`ldloc.3` | Partial | Load admitted scalar, vector, aggregate or managed-reference locals. Narrow integers are sign- or zero-extended to `i32`; initialization and lifetime rules apply. |
| `stloc`, `stloc.s`, `stloc.0`–`stloc.3` | Partial | Store values compatible with the declared local storage kind; narrow integer locals truncate an `i32` to their physical width. No general object or reference-bearing aggregate storage. |
| `ldloca`, `ldloca.s` | Partial | Form a checked reference to byte-backed local storage. Taking the address of a managed-reference local is explicitly unsupported. |
| `neg` | Partial | Wrapping negation of an `i32` or `i64`; the signed minimum maps to itself. No floating-point or reference operands. |
| `add` | Partial | Wrapping arithmetic on two `i32` values or two `i64` values, plus the mixed native/int32 cases described above. Also accepts a checked reference as the first operand and an int32 or native integer byte offset as the second, preserving allocation identity and checking lifetime and bounds when forming the result. Supplied immutable native handler tables also admit checked byte-offset addition. No floating-point operands or arbitrary numeric address fabrication. |
| `sub` | Partial | Wrapping scalar subtraction; also subtract an int32/native byte offset from a checked reference, preserving its readonly restriction, or compute the native byte difference of two live references within one allocation. Null, cross-allocation differences and invalid resulting positions fail. |
| `mul` | Partial | Wrapping arithmetic on two `i32` values or two `i64` values, plus the mixed native/int32 cases described above. No floating-point or reference/pointer operands. |
| `div`, `div.un`, `rem`, `rem.un` | Partial | Same-width `i32`/`i64` quotient or remainder. Signed quotient truncates toward zero; signed remainder follows the dividend sign. Zero divisors fault. Signed minimum with divisor -1 faults for both signed operations under the admitted runtime assumption. No floating-point, mixed-width operands or exception handlers. |
| `add.ovf`, `sub.ovf`, `mul.ovf`, `add.ovf.un`, `sub.ovf.un`, `mul.ovf.un` | Partial | Checked signed/unsigned arithmetic on same-width `i32`/`i64`. Compute the mathematical integer result, then reject values outside the destination range with a located overflow fault. No floating-point, reference arithmetic or exception handlers. |
| `and`, `or`, `xor`, `not` | Partial | Bitwise operations on `i32`/`i64`; binary operands must have the same width. |
| `shl`, `shr`, `shr.un` | Partial | Shift an `i32`, `i64` or native integer by an `i32` or native integer count, masked modulo the value width under the admitted runtime. `shr` is arithmetic; `shr.un` is logical. Native counts normalize to their low 32 bits; ordinary `int64` counts and reference operands are rejected by extraction and its certificate. |
| `conv.ovf.i1`, `conv.ovf.u1`, `conv.ovf.i2`, `conv.ovf.u2`, `conv.ovf.i4`, `conv.ovf.u4`, `conv.ovf.i8`, `conv.ovf.u8`, `conv.ovf.i`, `conv.ovf.u`, and each corresponding `.un` form | Partial | Checked conversion from `i32`/`i64`, preserving the mathematical value or producing a located overflow fault. `.un` interprets the input as unsigned; the destination controls the accepted range. Narrow results occupy `i32`; native destinations use the validated 64-bit profile. No floating-point or reference conversions. |
| `conv.i4`, `conv.u4` | Partial | `i64` to low 32 bits; `i32` identity. No floating-point or reference conversions. |
| `conv.i1`, `conv.i2` | Partial | Truncate an `i32` or `i64` to eight or sixteen bits, then sign-extend to an `i32` stack value. |
| `conv.u2` | Partial | Truncate an `i32` or `i64` to sixteen bits, then zero-extend to an `i32` stack value. |
| `conv.u1` | Partial | Low eight bits of an `i32` or `i64`, zero-extended to an `i32` stack value. |
| `conv.u8` | Partial | Zero-extend `i32` to `i64`, or preserve an `i64`. |
| `conv.i8` | Partial | Sign-extend `i32` to `i64`, or preserve an `i64`. No floating-point or reference conversions. |
| `conv.i` | Partial | Sign-extend an integer `i32` to the admitted 64-bit native width, or preserve an `i64`. No pointer/reference or floating-point conversion. |
| `conv.u` | Partial | Model native unsigned integers as 64-bit: zero-extend `i32`, or preserve `i64`. Does not convert a managed reference to an integer address. |
| `clt`, `clt.un`, `cgt`, `cgt.un`, `ceq` | Partial | Same-width `i32`/`i64` comparisons, returning `i32` zero or one. `clt` and `cgt` are signed; `.un` comparisons are unsigned. `ceq` additionally supports checked reference equality as described below; `clt.un` and `cgt.un` additionally order live references within one allocation. Signed reference ordering remains unsupported. No floating-point/unordered comparisons. |
| `br`, `br.s` | Partial | Unconditional branch to an admitted instruction boundary, including backward edges and self-loops. |
| `switch` | Partial | Pop an `i32` unsigned table index; branch to its target or fall through when outside the table. Empty and duplicate-target tables are supported. All reachable targets must be valid instruction boundaries; each arm and the fallthrough participate in dependency and stack analysis. |
| `sizeof` | Partial | Push the validated storage width as `i32` for admitted integer types (including Boolean/char), same-assembly explicit- or sequential-layout reference-free aggregates, or the integer vectors listed below. Native integers use eight bytes under the validated profile. Closed same-assembly generic structs require validated sequential layouts. No reference types, floating-point or unsupported generic layouts. |
| `brfalse`, `brfalse.s`, `brtrue`, `brtrue.s` | Partial | Zero/nonzero tests of `i32` or `i64`. Also accepts checked references, including readonly references and null. Admitted forward and backward successors. |
| `blt`, `blt.s`, `bge`, `bge.s`, `bgt`, `bgt.s`, `ble`, `ble.s` | Partial | Signed comparison of same-width `i32`/`i64`, branching to admitted forward or backward targets. |
| `blt.un`, `blt.un.s`, `bge.un`, `bge.un.s`, `bgt.un`, `bgt.un.s`, `ble.un`, `ble.un.s` | Partial | Unsigned comparison of same-width `i32`/`i64` or two live references within one allocation, branching to admitted forward or backward targets. Cross-allocation reference ordering is unsupported. |
| `beq`, `beq.s`, `bne.un`, `bne.un.s` | Partial | Equality/inequality of same-width `i32`/`i64`, branching to admitted forward or backward targets. Also supports checked reference equality as described below. No floating-point comparison. |
| `ldind.i`, `stind.i` | Partial | Native-width integer load/store through checked managed references; eight bytes on the admitted target, with the same allocation, permission and lifetime checks. A native handler-table cursor also supports authenticated pointer loads through `ldind.i`; stores to these immutable tables are unsupported. |
| `ldind.i8`, `stind.i8` | Partial | Eight-byte integer load/store through a checked reference. Allocation bounds, permissions, initialization and lifetime rules apply; arbitrary numeric addresses are not accepted. |
| `ldind.i1`, `ldind.u1`, `ldind.i2`, `ldind.u2`, `ldind.i4`, `ldind.u4` | Partial | One-, two- or four-byte integer loads through a checked reference. Signed narrow loads sign-extend and unsigned loads zero-extend to `i32`; both four-byte forms return the same `i32` bits. Aggregate snapshots and numeric addresses are rejected. |
| `stind.i1`, `stind.i2`, `stind.i4` | Partial | Store the low one, two or four bytes of an `i32` through a checked reference. Allocation bounds, write permissions and lifetime apply; adjacent bytes remain unchanged. |
| `ldfld`, `ldflda`, `stfld` | Partial | Fields in same-assembly, validated explicit- or sequential-layout, reference-free value types, and `Item1`/`Item2` of an equal-width primitive `ValueTuple<T1, T2>` (see [value tuples](SOUNDNESS.md#value-tuples)). Supported field storage is `sbyte`, byte/Boolean, `short`, `ushort`/`char`, 32-bit integer, 64-bit integer, native integer, integer-backed enum or nested reference-free aggregate. Nested snapshots and assignments copy all field bytes, including padding. Narrow stores truncate; narrow loads sign- or zero-extend to `i32` according to field metadata. `ldfld` accepts an aggregate byte snapshot or reference; field addresses and stores require a reference. No general managed objects, auto layouts or static fields through these opcodes. |
| `ldobj`, `stobj` | Partial | Load/store admitted integer types through checked references, with narrow truncation/extension derived from the validated type token. Also copy validated aggregates of 1–65,536 bytes or admitted Vector128/256/512 integer values, retaining initialization masks. No general objects, reference-bearing storage or floating-point tokens. Native-integer tokens use eight-byte storage. |
| `cpobj` | Partial | Copy validated integer, aggregate or admitted Vector128/256/512 integer storage through checked references. Requires initialized readable source and writable destination; self-copy is supported, partial overlap is rejected. No reference-bearing or floating-point tokens. |
| `initobj` | Partial | Zero the validated width of an admitted integer type, same-assembly explicit- or sequential-layout aggregate, or admitted Vector128/256/512 integer value. This initializes previously unknown bytes without touching neighboring storage. No managed-object initialization. |
| `ldsfld` | Partial | Value of a same-assembly `static readonly` integer, enum or reference-free struct field that its static constructor fixes, with the declaring type named by `--assume-initialized` (see [static readonly values](#static-readonly-values)). Other static fields are rejected. |
| `ldsflda` | Partial | Address of validated same-assembly static readonly RVA data, or a constructor-initialized readonly value under the initialization assumption. Uses identity-keyed immutable storage with checked write denial. See [static span tables](#static-span-tables) and [static readonly values](#static-readonly-values). Not arbitrary static fields or mutable global state. |
| `call` | Partial | Acyclic calls to supported static methods or reference-free struct instance methods (including direct constructor calls) in the same assembly, concrete generic-method specializations, or exact runtime/intrinsic signatures in the allowlist, including integer BinaryPrimitives byte-span transfers and no-read span/array accessors. Closed generic declaring types are admitted for static calls, including nested owners; validated closed sequential structs also admit direct instance methods and constructors. No arbitrary external calls, class instance methods or general virtual dispatch. |
| `newobj` | Partial | Same-assembly constructors of validated reference-free structs: zero-initialize caller-owned storage, invoke the constructor with managed-reference `this`, then return a checked value snapshot. Also admitted `Span<T>` and `ReadOnlySpan<T>` constructors over checked existing storage for supported integer, enum, aggregate and integer-vector elements, from a single reference, `(void*, int)`, an array, or `(array, start, length)`. Class construction and unsupported generic constructors or cyclic dependencies are rejected. |
| `ldtoken` | Partial | A type token as an operand of a decided closed type test, which emits a no-op, or a static data field token for `RuntimeHelpers.CreateSpan<T>`, which emits the field's address (see below). Other tokens are rejected. |
| `throw` | Partial | Only `throw new E(...)` with `ldstr`/`ldnull` arguments (see below): it raises a located `thrown "E"` fault. Other throws are rejected. |
| `constrained.`, `callvirt` | Partial | Adjacent prefix and call resolving to a concrete same-assembly struct implementation; see [constrained struct calls](#constrained-struct-calls). No boxing or general virtual dispatch. |
| `ldftn` | Partial | Exact static same-assembly managed method addresses, retaining scoped identity and closed signature. Callable values have no numeric address representation. See typed indirect dispatch below. |
| `calli` | Partial | Static default-managed signatures over admitted integer/enum, reference-free aggregate and integer-vector values, and managed references to these types. The pointer must identify an authenticated catalog entry with the exact signature. Ordinary indirect calls select a forward target; tail calls permit cycles. Supplied immutable native tables also admit checked byte offsets and `ldind.i` with authenticated target provenance. No unmanaged conventions or arbitrary numeric targets. |
| `tail.` | Partial | Adjacent `tail. call ret` or `tail. calli ret` with exactly its arguments and optional function pointer on the stack and the same return type. Retires caller storage before entering the callee and revalidates argument lifetimes. Admitted same-assembly transfers may form cycles; virtual, imported and intrinsic tail calls remain unsupported. |
| `ret` | Partial | Return from an admitted method with exactly zero or one result according to its signature. Narrow integer results are truncated and sign- or zero-extended to `i32`. The checked model validates returned references and rejects references that escape expired local storage. |
| `initblk`, `cpblk` | Partial | Managed references and unsigned 32-bit counts; checked block alignment and access rules. Nonempty overlapping copies are rejected. |
| `unaligned.` | Partial | Values 1, 2 and 4 before supported ordinary or block memory accesses; malformed prefix sequences and interior branch targets are rejected. |
| `localloc` | Partial | Frame-owned storage within an explicit per-activation quota; checked initialization, alignment and expiry. See [dynamic stack allocation](#dynamic-stack-allocation). |

## Typed indirect dispatch

Managed function pointers can be held in typed locals or supplied as parameters. Supplied
immutable single-dimensional handler tables support `ldlen` and `ldelem.i`; entries retain
one exact signature and must name non-null catalog targets. A null table raises
`NullReferenceException`, and invalid indexes raise `IndexOutOfRangeException`.

Catalog discovery uses same-assembly `ldftn` references and already extracted methods with
matching signatures. Each entry binds the scoped metadata identity, generic arguments and
program index to an extracted body. Pointer identities stay stable when linking relocates
program indices. Supported signatures contain primitive integer, enum, reference-free aggregate or
integer-vector parameters/results, managed references to those types, and void results. Closed
generic structs retain their exact scoped identity. Calling conventions are checked exactly.

Supplied immutable `nint*` tables admit byte-offset addition, `ldind.i` and native target locals.
An explicit binding identifies the static allocation and authenticated catalog identities;
numeric bytes alone cannot establish callable provenance. Loads check bounds, eight-byte
alignment, initialization and read authority. Forming a one-past reference is allowed, but
loading it is not. Each body requires one exact supported managed indirect-call signature; handler
signatures carrying native table pointers are not supported.

Table allocation, updates, null entries, pointer fields and numeric-address conversions are
not supported. Mutable raw-pointer EVM tables therefore need further work. All-tail cycles are supported; mixed ordinary/tail recursive graphs may be rejected. Tail cycles consume ordinary
execution fuel; admitting a cycle neither proves termination nor makes exhaustion successful.

## Dynamic stack allocation

`localloc` accepts an unsigned int32 or native byte count as its sole stack operand. It creates
fresh allocation-relative storage owned by the current activation. The caller supplies
`Memory.stackLimit`, a per-activation quota up to 65,536 bytes; its default is zero. Each nonempty
request charges its size rounded to 16 bytes. Insufficient quota produces a distinct
`stackAllocationFailure`; a zero request returns null and consumes no quota.

The raw method's `localsinit` flag controls zero initialization. Otherwise bytes remain unreadable
until written. Checked pointer offsets, typed loads and stores, and admitted span construction
retain allocation bounds and authority. Returning a reference or span into expired stack storage
fails. Numeric address fabrication and general pointer casts remain unsupported.

The quota is a deployment premise rather than a physical-stack measurement. Ordinary frame and
call overhead are outside it; see [the soundness boundary](SOUNDNESS.md#what-is-defined-and-proved).

## Reference observations

Reference truth tests and equality validate lifetime and reference formation without requiring
read authority or initialized bytes. Readonly references retain their write restriction.
Equality compares offsets within one allocation and distinguishes interior addresses from
separate allocations. Cross-allocation comparisons involving an end sentinel are rejected:
the model does not know whether the physical end address equals a neighbouring allocation's
start. Comparing invalid or expired references fails, even when both operands are identical.

The certificate tracks an `ldnull` object separately from managed references. It cannot be
stored or passed as a managed pointer. Existing `Unsafe.NullRef<T>` values remain managed
references and can participate in reference comparisons. Numeric zero does not become a
reference through these rules.

The managed-reference overloads of `Unsafe.AreSame`, `IsAddressLessThan` and
`IsAddressGreaterThan` use these checked comparisons. Ordering and
`Unsafe.ByteOffset(origin, target)` require two live references in the same allocation;
the latter returns the native-width byte displacement from origin to target.
`Unsafe.AddByteOffset` and `SubtractByteOffset` accept `nint` or `nuint` offsets.
`Unsafe.Subtract<T>` accepts `int`, `nint` or `nuint` element offsets for admitted scalar,
aggregate and vector storage. Scaling and subtraction wrap at the native 64-bit width;
the resulting reference must still be live and in bounds. These operations grant no read
or write authority. Numeric pointer overloads remain unsupported.

## Block memory and alignment prefixes

`initblk` and `cpblk` are partially supported for checked managed references and unsigned 32-bit byte counts. Initialization uses the low eight bits of its integer value. Copying requires initialized, readable source bytes; both operations require writable destination bytes, valid lifetimes, bounds and reference-free storage. Every nonempty overlapping copy, including an exact alias, is rejected because CLI overlap behaviour is unspecified. Zero counts access no memory and permit null references.

Unprefixed block operations require eight-byte alignment on the admitted 64-bit target. Model-owned 32-bit and 64-bit scalar local/parameter homes carry four-byte and eight-byte natural alignment respectively, so aligned block access can succeed on a 64-bit scalar home. Aggregate, vector and narrow homes retain conservative byte alignment. An immediately preceding `unaligned. 1`, `2` or `4` selects that alignment requirement. Prefix operands, permitted followers and branch targets are validated: a branch cannot enter between a prefix and its instruction. Prefix combinations with unsupported modifiers remain rejected.

`unaligned.` is also accepted before supported integer `ldind.*`/`stind.*`, `ldobj`/`stobj` and `ldfld`/`stfld` instructions. These retain the existing target-specific ordinary byte-aligned memory semantics; a prefix does not bypass any safety check. The prefix occupies its original instruction position and lowers to a no-op, with block alignment encoded in the following operation.

The exact managed-reference and pointer overloads of `Unsafe.InitBlock`, `InitBlockUnaligned`,
`CopyBlock` and `CopyBlockUnaligned` use these same operations. Pointer arguments must come from
admitted allocation-relative references; arbitrary integer addresses remain unsupported. The
certificate binds each helper's exact signature, operation and alignment.

## Pointer subtraction and ordering

Pointer subtraction uses byte offsets, signed int32/native displacements and native-width
wrapping arithmetic, followed by the existing formation checks. Same-allocation differences
return native integer bits; `clt.un`, `cgt.un`, `blt.un`, `ble.un`, `bgt.un` and `bge.un`
(including short branches) compare allocation-relative offsets. Both operands must be non-null,
live and well formed. Declared end positions are allowed without granting byte access.
Cross-allocation differences and orderings are unsupported. Numeric-minus-pointer and signed
reference orderings are not admitted. Overflow-checking `sub.ovf.un` remains scalar-only.

## Unsupported opcodes

Supplied arrays admit `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long`, `ulong`,
`nint`, `nuint`, `bool`, `char`, admitted enums, validated reference-free aggregates and
supported integer Vector128/256/512 elements over existing storage. Their length, element type
and allocation identity remain explicit across locals, calls and returns. Indexing checks
null before bounds; negative and out-of-range indices raise `System.IndexOutOfRangeException`
on a valid non-null array. Length does not require readable contents. Invalid storage and
insufficient authority remain model faults. Primitive integer arrays can also be allocated with
`newarr`. Array-root address-taking, object identity tests and reference/floating-point elements
remain outside this subset.

The table above is exhaustive for reachable translation. Notable exclusions include:

| Area | Examples rejected by extraction |
| --- | --- |
| Debugger and prefixes | `break`, `volatile.`; `tail.` outside admitted same-assembly calls; `readonly.` outside the checked array-element subset; `constrained.` outside the checked struct-call subset |
| Other conversions | Floating-point conversions |
| Other indirect/block memory | `ldind.ref`, floating-point `ldind.*`, `stind.ref`, floating-point `stind.*` |
| Objects, arrays and metadata | `ldstr` outside a folded throw, `box`, `unbox`, `unbox.any`, `castclass`, `isinst`, nonprimitive `newarr`, reference/floating-point `ldelem.*`/`stelem.*`, `ldtoken` of a method or of a type outside a decided type test |
| Static field values | `stsfld`, `ldsfld` and `ldsflda` of fields outside the admitted readonly subset |
| Dispatch and exceptions | Unconstrained `callvirt`, `jmp`, `ldvirtftn`, `throw` outside a folded throw, `rethrow`, `leave`, `leave.s`, `endfinally`, `endfilter` |
| Floating-point constants | `ldc.r4`, `ldc.r8` |

### Type tests

In a specialized generic body, `typeof(A) == typeof(B)` and `typeof(A) != typeof(B)` compile to `ldtoken A; call Type::GetTypeFromHandle; ldtoken B; call Type::GetTypeFromHandle; call Type::op_Equality` (or `op_Inequality`), with the `System.Runtime` signatures. When both types are closed and their identity is decided, the four operand instructions emit `nop` and the comparison emits `ldc.i4.0` or `ldc.i4.1`, as the JIT folds them. Profile reachability then prunes the dead branch. Types are equal when their metadata is identical, and different when their full names differ; one full name in two scopes, decorated names and `void` stay undecided. Undecided tests, any other instruction between the five, a branch into the last four, other `System.Type` members and `Type` values in locals remain rejected.

### Throws

`throw new E(...)` compiles to one `ldstr` or `ldnull` per constructor argument, `newobj` of `E`'s constructor and `throw`. For an exact allowlisted `System.Runtime` constructor, the loads and `newobj` emit `nop` and `throw` emits `.throw "E"`, which ends execution with a fault located at the `throw`. A `[DoesNotReturn]` helper containing only this pattern is an ordinary call. Other arguments, any instruction between the parts, a branch past the first part, rethrowing a stored exception and exception handlers remain rejected.

In addition to the admitted string constructors, `Exception`, `InvalidOperationException`,
`ArgumentException` and `ArgumentOutOfRangeException` admit a message with a null inner exception.
`ArgumentException` also admits message, parameter name and null inner exception;
`ArgumentOutOfRangeException` admits parameter name, null actual value and message.
Only the thrown type is observed. Constructor signatures and null operands are checked independently;
expressions with effects or faults are not discarded. Prefix recognition inspects at most four loads.

### Constrained struct calls

An adjacent `constrained. T; callvirt` pair supports a concrete, reference-free same-assembly
struct `T` and a method declared on that struct or a directly implemented same-assembly interface.
Closed sequential generic structs admit direct slots and directly implemented interface slots,
including closed generic interfaces. The slot's closed declaring owner must match exactly.
Implicit implementations must uniquely match the public name and signature; explicit `MethodImpl`
overrides take precedence and retain the closed interface owner as well as the method token.
Closed generic helpers can use a directly implemented closed interface constraint.
The original managed-reference receiver is passed to the resolved implementation, so mutations
remain visible to the caller without boxing.

The Lean certificate independently resolves serialized type, interface and method metadata and
checks the selected method token, signature, closed owner arguments and argument count.
A branch cannot bypass the prefix.
Reference receivers, boxing fallbacks, inherited or default-interface dispatch, generic methods
on interfaces, open interface constraints and ordinary unconstrained virtual calls remain unsupported.

### Static span tables

`Span<T>` and `ReadOnlySpan<T>` over the eight fixed-width integer types, `nint`, `nuint`,
`char`, `bool`, admitted same-assembly enums, validated reference-free structs and supported
integer Vector128/256/512 types have typed, allocation-relative storage
for by-value parameters and reusable locals. Their length, indexing, slicing and readonly
conversion retain element width and allocation lifetime. `MemoryMarshal.CreateSpan` and
`CreateReadOnlySpan` form views over existing storage; they do not grant access authority or
initialize bytes. Readonly element references reject stores, while other writable aliases
can still update the same backing memory. Slicing checks signed input ranges and permits an
empty view at the allocation end. Byref span parameters and general ref structs remain outside
this support.

Aggregate span widths come from the validated target-specific layout, including vector-field
alignment; vectors use their exact storage width. Indexing yields a checked element reference
for existing typed load/store operations. Parameters, locals, slicing, reference factories,
reinterpretation, copies, fills and clearing reuse the same checked views. Single-reference
constructors form one-element views over live storage; pointer constructors take an explicit
int32 length. Both forms support primitive, enum, aggregate and integer-vector elements and
retain the element layout, lifetime and readonly capability without reading or initializing bytes.
Opaque values and numeric addresses cannot fabricate references.

Span `IsEmpty` and `GetPinnableReference` inspect a validated view without reading its bytes.
An empty span's pinnable reference is null; readonly views return readonly references.
`MemoryMarshal.GetArrayDataReference<T>` supports all admitted array elements: an empty array
retains its data reference, while a null array raises `NullReferenceException`. These accessors
grant no byte-access authority.

Array constructors, implicit array conversions and the array overloads of
`MemoryExtensions.AsSpan` form views over supplied integer, enum, aggregate and integer-vector
array storage. Enum views retain their exact enum identity through locals, slices, calls and returns; equal-width
enums are not interchangeable. `AsSpan` accepts a whole array, a start index, or a start and length. Null arrays produce empty
spans only for a zero range; invalid ranges raise `ArgumentOutOfRangeException`.
These operations allocate no backing storage, preserve aliases and grant no byte-access
authority. Non-array `AsSpan` overloads remain unsupported.

In-place construction of a span local accepts `ldloca`, up to three simple argument loads or
integer constants, and its exact constructor call. The address cannot escape or be duplicated,
and control flow cannot enter the sequence after its first instruction. The local may be
reused or reinitialized; construction faults remain at the call instruction.

`Span<T>.Clear` initializes the complete view using one checked range write, including
aggregate and vector elements. `Fill` repeats a captured primitive, enum, aggregate or integer-vector
value using one checked range write. Aggregate/vector snapshots retain initialization masks;
unknown bytes never become initialized, and unspecified low-lane-only vector values remain rejected.
Both require write authority, but not initialized or readable destination bytes. Empty spans require
no byte access; nonempty fills establish repeated contents and preserve neighbouring
bytes, including other slices in the same allocation. Readonly views do not admit these members.

`MemoryMarshal.AsBytes` and `Cast<TFrom,TTo>` reinterpret admitted integer, enum, aggregate
and integer-vector spans without copying or reading their bytes. They retain allocation identity,
lifetime and write capability. The result length is the source byte extent divided by the target element
width, rounded down; a length exceeding `Int32.MaxValue` raises `OverflowException`.
Readonly views stay readonly, and reinterpreting uninitialized storage does not initialize it.

`CopyTo` and `TryCopyTo` accept writable destination spans of the same element type, from
either writable or readonly source spans. Copying captures initialized, readable source bytes
before writing, so either overlap direction and exact aliases are supported. A short destination
raises `ArgumentException` or returns false without reading or writing bytes. Empty copies need
no byte access. Successful nonempty copies require write authority and preserve neighboring bytes.

`MemoryMarshal.Read<T>`, `Write<T>`, `TryRead<T>` and `TryWrite<T>` transfer admitted integer,
aggregate or integer-vector values through byte spans. Short `Read`/`Write` calls raise
`ArgumentOutOfRangeException`. A short `TryRead` writes initialized `default(T)` to its out
reference and returns false; a short `TryWrite` returns false without reading the input value
or modifying memory. Successful transfers preserve snapshot initialization masks and retain
the checked model's bounds, lifetime and authority requirements.

A collection-expression property such as `static ReadOnlySpan<uint> Table => [...]` compiles to `ldtoken <field>; call RuntimeHelpers::CreateSpan<uint>` over a static data field (`ldsflda` rules, packing 1, 2, 4 or 8). The span covers the whole field and has `size / sizeof(T)` elements, for any primitive integer `T`. A caller reads it as `stloc s; ldloca s; [index;] call get_Item` or `stloc s; ldloca s; call get_Length`: the store and address emit `nop`, so the span stays on the stack as the receiver. `get_Item` faults with `System.IndexOutOfRangeException` at the call when the index is out of range, compared unsigned as in .NET. `MemoryMarshal.GetReference` also accepts these spans. The fold is used only for a single-use receiver with a single-load or constant index; other supported uses retain typed span storage. Branches into a folded receiver and byref spans remain rejected.

### Static readonly values

Primitive integer fields (including Boolean, Char and 64-bit native integers) and same-assembly
integer enums also admit a direct integer literal, optionally widened with the supported integer
conversions. They may instead use the same checked helper-call initializer or copy an earlier
field of the same type. Loads truncate to the declared storage width and sign-extend signed
8-/16-bit fields. Lean checks stored bytes against the literal or executed initializer and binds
the load width and signedness to the raw field type. Mutable fields, address-taking during
initialization, repeated stores and conditional initialization remain rejected.

`public static readonly UInt256 One = 1ul;` compiles to `ldc.i4.1; conv.i8; call op_Implicit(ulong); stsfld One` in the static constructor. A reachable `ldsfld` of such a field emits `.staticValue bytes`, which pushes the field's value as an aggregate and touches no memory. The static constructor must store the field exactly once, unconditionally (no control flow before the store and no branch back to it). A helper-call initializer uses a same-assembly static call whose arguments are integer constants (`ldc.i4*`, `ldc.i8` with `conv.i4`/`conv.u4`/`conv.i8`/`conv.u8`/`conv.i`/`conv.u`). A field may instead copy (`ldsfld G; stsfld F`) such a field stored earlier, as in `MinValue = Zero`. The field's declaring type must be named by `--assume-initialized`. The called method and its callees become part of the extracted program and must not access static fields. The static site records the call, and the extraction certificate reruns it in the checked interpreter: the result must be exactly the emitted bytes, or `translation_valid` fails.

Direct `new T(integer constants)` initialization is also admitted for same-assembly
reference-free structs, including closed generic structs stored on nongeneric declaring types.
Closed constructors use the ordinary checked generic specialization. The certificate executes
the existing aggregate-construction
operation, including zero initialization and constructor readback, to establish the stored bytes.

`ldsflda` of an admitted readonly field uses the same identity-keyed immutable storage as RVA
data. Repeated accesses share one allocation; distinct fields remain distinct even when their
bytes agree. The reference can be passed to supported helpers and instance methods. Checked
writes through it fail, including writes through `Unsafe.AsRef`.

Rejected: a declaring type without the assumption; values built by other code shapes; a second
store, a store outside the static constructor, or `ldsflda` of the field during initialization;
and `stsfld` in an extracted method.

Release configuration is required, but it does not guarantee that a compiler emits only supported instructions. For example, reachable reference-element array allocation or exception handling is still rejected.

## Runtime calls and SIMD

Reachable same-assembly generic methods are specialized for supported primitive, enum, reference-free aggregate and vector type arguments. This substitutes types in the original CIL parameters, locals, type operands and nested generic calls; it does not replace method bodies with functional summaries. Repeated uses share a specialization, while different type arguments retain separate bodies. Ordinary calls retain an acyclic order; tail transfers may form cycles. Extraction rejects more than 256 distinct specializations.

Select a non-generic entry method whose compiled calls supply the concrete type arguments. Static calls on closed same-assembly generic declaring types are supported, including nested owners and combined owner/method type arguments. Closed same-assembly sequential generic structs admit reference-free storage, field accesses, direct instance methods and constructors after substituting their owner arguments. Explicit/auto generic layouts, reference-containing instantiations and interface/reference-constrained generic structs remain rejected, as do boxing, general runtime dispatch and unsupported storage types. A same-assembly interface constraint is admitted when the concrete struct directly declares that interface; constrained calls are checked as described below. Unconstrained parameters and admitted value-type/default-constructor/unmanaged constraints are supported for the reference-free value types above. Every specialized body's instructions undergo the normal validation.

See the [per-family intrinsic tables](SIMD.md) for the exact Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM operations, operand types and profile requirements.

SIMD and hardware features enter compiled CIL mostly through `call`, rather than dedicated SIMD CIL opcodes. Selected Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM overloads have models. The exact allowed runtime assembly identities, generic arguments, signatures and capability requirements are defined in [RuntimeModels.cs](../Extractor/RuntimeModels.cs) and [FeatureProfiles.cs](../Extractor/FeatureProfiles.cs). Supporting one overload or CPU feature does not mean the entire API is supported.

`Unsafe.SizeOf<T>()` and the managed-reference `Unsafe.Add<T>` overloads with `int`, `nint` or `nuint` offsets use validated layouts for supported integer primitives, enums, reference-free structs and supported Vector128/256/512 types. Sizes include managed packing and padding; reference offsets scale by that size and wrap at the validated native width. Forming the resulting reference checks allocation identity, lifetime and bounds, including explicitly admitted one-past positions. It does not grant permission to read or write. Classes, pointer/byref type arguments and unsupported layouts fail extraction.

`Unsafe.SkipInit<T>(out T)` admits the same supported storage types. Its checked
operation validates the managed reference and leaves memory unchanged, including
initialization flags and access permissions. It does not initialize the output;
reads still require initialized bytes. Extraction evidence checks the exact
runtime call identity and its translation to `skipInit`.

`Unsafe.NullRef<T>()` and `Unsafe.IsNullRef<T>(ref readonly T)` admit the same
storage types. `NullRef` pushes the model's null managed reference, which a
byref local or argument can hold like any other reference. `IsNullRef` returns
1 for it and 0 for every other reference, live or not, without accessing memory.
Every load, store, copy, initialization, field or lane access of one or more
bytes through null faults with `nullDereference`, the model's
`NullReferenceException`, and no address is formed from it; zero-length block
operations access nothing, as above. Extraction evidence binds each call to its operation in
both directions, as for `SkipInit`. `NullRef` produces a null byref; the bounded
`ldnull` support above produces an object null and does not permit mixing it with managed pointers.

The runtime allowlist also includes specific `Unsafe.AsRef`, `Unsafe.As`, `Unsafe.BitCast`, `MemoryMarshal.GetReference` and span constructor signatures. These are narrow translations into reference, memory or vector operations, not blanket support for those classes. CIL `add` on references supports the checked byte-offset form described above.

Managed byte-reference and pointer `Unsafe.ReadUnaligned<T>` and `WriteUnaligned<T>` support admitted
integer, aggregate and integer-vector storage. They use the existing typed loads and stores
with byte alignment, retaining bounds, lifetime, access authority and snapshot initialization
masks. Readonly source references are accepted; writes require writable references and byte
authority. Pointer overloads require allocation-relative references, not numeric addresses.
`Unsafe.Read<T>(void*)` and `Write<T>(void*, T)` reuse those checked transfers after an alignment
check. Primitive integers require their storage width; aggregates require their computed layout
alignment, including packing. Integer vectors conservatively require alignment to their full byte
width. This subset can reject vector addresses that a particular runtime accepts; the unaligned
overloads remain available. Alignment checks do not repeat the per-byte authority scan.
`Unsafe.AsRef<T>(void*)` preserves that provenance and forms a live reference without reading or
initializing bytes or granting access authority. Reference-bearing value types remain unsupported.

The checked model supports `Unsafe.BitCast<TFrom,TTo>` between equal-size validated unmanaged aggregates and `Vector128`/`Vector256` values with `uint` or `ulong` elements, in both directions and under the scalar profile. Byte snapshots retain initialization flags through the cast, local and parameter homes, and value loads/stores. Partially initialized results remain snapshots; numeric reads and vector arithmetic cannot consume their unknown bytes. The pure model does not implement this value-cast operation.

`CIL.Safety.ValueBitCasts` supplies byte/vector round-trip lemmas and `bitcastValue_preserves_snapshot`; `CIL.Safety.SnapshotMemory` supplies checked snapshot write/readback facts. Access witnesses in `AccessAlignment` distinguish initialized reads/writes from snapshot copies, which preserve flags instead of asserting initialization.

Reachability is evaluated under the chosen, validated feature profile. Instructions excluded by that analysis are emitted as explicit unsupported placeholders, not silently assigned successful semantics. If execution reaches such a placeholder it fails. Changing the profile invalidates extraction artifacts.

## Lean-only operations and source of truth

The Lean `CIL.Op` type and memory/SIMD modules contain operations beyond the extractor's current mapping, including vector argument homes, fixed vector-lane helpers, `newVector256` and additional memory helpers. Their existence is not evidence that the corresponding arbitrary CIL or .NET API is extractable. Generic aggregate operations are implemented by the checked memory interpreter; the older pure interpreter explicitly rejects those operations.

This inventory was checked against:

- [InstructionTranslation.cs](../Extractor/InstructionTranslation.cs): opcode translation and default rejection.
- [MetadataValidation.cs](../Extractor/MetadataValidation.cs), [Reachability.cs](../Extractor/Reachability.cs) and [StaticData.cs](../Extractor/StaticData.cs): type, call, control-flow and static-data restrictions.
- [Semantics.lean](../CIL/Semantics.lean): scalar operand cases and conversions.
- [Execution.lean](../CIL/Safety/Execution.lean), [Frames.lean](../CIL/Safety/Frames.lean), [InstructionMemory.lean](../CIL/Safety/InstructionMemory.lean) and [StaticMemory.lean](../CIL/Safety/StaticMemory.lean): checked execution, local storage and memory behaviour.

When extending translation or operand support, update this table together with the implementation and relevant semantic/extractor regressions. See [validation results](VALIDATION.md) for the tests actually run and [soundness](SOUNDNESS.md) for the runtime assumptions and trusted base.

## Portable scalar runtime helpers

These are exact `call` signatures, not additional CIL opcodes. They work with every admitted hardware profile.

| Runtime type | Supported methods and overloads | Semantics |
| --- | --- | --- |
| `System.Numerics.BitOperations` | `RotateLeft` / `RotateRight` on `uint`, `ulong` or `nuint`, with `int` count | Circular rotation, count modulo 32/64, including negative counts |
| `System.Numerics.BitOperations` | `PopCount`, `LeadingZeroCount`, `TrailingZeroCount` on `uint`, `ulong` or `nuint` | `int` result; zero has 32/64 leading/trailing zeros |
| `System.Numerics.BitOperations` | `IsPow2` on `int`, `uint`, `long`, `ulong`, `nint` or `nuint` | True for positive powers of two; false for zero and signed negative values |
| `System.Numerics.BitOperations` | `Log2` on `uint`, `ulong` or `nuint` | Floor base-two logarithm as `int`; zero input returns zero |
| `System.Numerics.BitOperations` | `RoundUpToPowerOf2` on `uint`, `ulong` or `nuint` | Least power of two at least the input; zero for zero input or overflow |
| `System.Buffers.Binary.BinaryPrimitives` | `ReverseEndianness` on `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long`, `ulong`, `nint` or `nuint` | Reverse bytes within the value; preserve signed return conventions; byte/sbyte are identity operations |

`System.Math.Min`, `Max` and `Clamp` support signed and unsigned 8-, 16-, 32-, 64-bit and native integers. `Abs` and `Sign` support the signed types; `Sign` returns an `int`. `Abs` of the signed minimum produces an arithmetic overflow fault. `Clamp` with a lower bound greater than its upper bound produces an invalid-bounds fault. These failures terminate checked execution; exception handlers are not modelled.

`System.Math.BigMul(ulong, ulong, out ulong)` returns the high 64 bits of the unsigned product and writes the low 64 bits through the checked output reference. The destination must be live, in bounds and writable; its previous bytes need not be initialized. `CIL.Safety.bigMul64_succeeds` exposes the exact result, low-word readback, allocation preservation and preservation of cells outside the output's eight bytes.

Native-width overloads use the validated 64-bit target. The 128-bit, generic-math and other unlisted helper overloads remain unsupported. The extractor validates the exact .NET 10 runtime assembly identity, declaring type, static calling convention and signature. These portable API semantics do not require any ISA to be enabled and do not establish correctness of a particular runtime implementation.

`BinaryPrimitives.Read{Int,UInt}{16,32,64}{Little,Big}Endian`, their `TryRead` forms,
`Write` forms and `TryWrite` forms operate on checked byte spans. Reads sign- or zero-extend
according to the named integer type after applying byte order; writes store exactly that width.
Short ordinary transfers raise `ArgumentOutOfRangeException`; short try-reads write zero to
the output and return false, while short try-writes return false without modifying memory.
Successful transfers retain bounds, lifetime, initialization and authority checks. These
48 exact signatures do not admit floating-point, 128-bit or native-width span overloads.

### Vector storage and fields

`sizeof`, `initobj`, `ldobj`, `stobj` and `cpobj` admit `Vector128<T>`, `Vector256<T>`
and `Vector512<T>` for `byte`, `int`, `uint`, `long` and `ulong`. Exact type-token
checks bind each operation to its storage width. Loads, stores, parameters and returns
retain initialization masks; using unknown lanes as numeric values is rejected.
`cpobj` requires initialized source bytes even when the token names a vector.

Instance fields support `Vector128<T>` and `Vector256<T>` for `byte`, `int`, `uint`,
`long` and `ulong`. The owner must have a validated, reference-free sequential or
explicit layout. Other vector element types and 512-bit fields are rejected.
Auto-layout tuples do not admit vector fields.
Layout computation uses CoreCLR's default packing limit of 64 bytes.
`Vector128<T>` has natural field alignment 16. `Vector256<T>` has natural
field alignment 32 under x64 profiles and 16 under ARM64 profiles. Explicit
packing caps these values. The checked method profile selects the layout in both
the extractor and the Lean certificate. A scalar profile must use an explicit
packing limit of at most 16 for `Vector256<T>` fields because it does not
select a target architecture.

Field widths come from the vector type. Raw layout evidence keeps vector storage
separate from integer and nested aggregate storage. Lean recomputes each field
offset and checks each field instruction against that evidence.

Field reads and writes use the ordinary byte-aligned access rule. A packed field
does not require vector-width alignment. Checked accesses retain allocation
bounds and initialization masks. `Unsafe.As` can expose these fields through an
admitted struct reference without changing its address or access bounds.
