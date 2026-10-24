# CIL opcode support

This table covers all 155 opcode encodings currently handled by the translator and describes the allocation-aware execution model used for memory-safety proofs. It is an inventory of implemented behaviour, not a claim that every listed opcode/operand combination has its own regression test, or that the model is equivalent to every .NET runtime.

- **Complete within the admitted model:** the opcode's operation is implemented for its admitted operands. Ordinary stack/value validity checks still apply.
- **Partial:** translation exists, but the row lists additional type, layout, control-flow or runtime restrictions. Unsupported operand shapes can fail during checked execution even when translation succeeds.
- **Unsupported:** no reachable translation exists; extraction rejects the opcode. All opcodes not listed in the translated-opcode table are unsupported.

Every row is subject to the common target restrictions: Release IL-only .NET 10 assemblies, 64-bit little-endian execution, admitted types, no exception handlers, validated reachable control flow (including loops) and an acyclic graph of admitted managed methods. A translated method still requires a proof of the desired property. Exhausted fuel, invalid states and unsupported operations are failures, never implicit successes.

The initial extraction target is Release, IL-only **.NET 10**, 64-bit little-endian execution. Supported scalar operations include 32/64-bit wrapping arithmetic, bitwise operations, shifts, selected conversions/comparisons, conditional/unconditional branches, local and argument loads/stores, 64-bit indirect access, and acyclic managed calls to static methods and reference-free struct instance methods. Struct methods receive a checked managed-reference `this`; direct constructor calls on existing storage and `newobj` construction of validated structs are supported. Explicit- and sequential-layout reference-free aggregates use validated sizes and byte offsets; fields admit narrow, 32-bit, 64-bit and native integer storage, including same-assembly enums backed by the eight C# enum integer types and nested reference-free structs. Nested fields support references, snapshots and whole-value assignment, with validated packing and padding. Enum parameters, returns, locals, references and flags use the underlying integer semantics, including unnamed values. Boxing and `System.Enum` methods remain unsupported. SIMD models cover selected Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM operations, as enumerated in `CIL/SIMD` and `Extractor/RuntimeModels.cs`.

## Translated opcodes

Ranges below include every numbered form between the endpoints. `.s` denotes the actual short encoding, not a different semantic operation. Native `nint`/`nuint` values use `i64` under the validated 64-bit target. For mixed native/int32 arithmetic and comparisons, extraction tracks stack types and emits an explicit widening wrapper; invalid native/int64 mixtures are rejected. Mixed native/int32 unsigned branches (`bne.un`, `blt.un`, `bgt.un`, `ble.un`, `bge.un`, including short forms) are rejected because CoreCLR widening depends on operand provenance; insert explicit `conv.i` or `conv.u` to select same-width semantics. The wrapper sign-extends the int32 operand, except that unsigned checked arithmetic zero-extends it. Scalar `clt.un`/`cgt.un` still sign-extend, matching the admitted runtime. The wrapper preserves arithmetic faults and branch targets and cannot dispatch memory or calls. The rows below describe scalar operands after this widening; other mixed widths remain unsupported.

`i32` and `i64` refer to the model's 32- and 64-bit integer stack values; managed references are separate values, not integer addresses.

Same-assembly enums backed by `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long` or `ulong` use their validated underlying integer representation throughout these operations, including fields, argument homes and typed memory instructions. Narrow enum loads sign- or zero-extend exactly like the underlying type. Unnamed values are supported; boxing, `System.Enum` methods and external enum dependencies are not.

| Opcodes | Status | Implemented behaviour and restrictions |
| --- | --- | --- |
| `ldc.i4`, `ldc.i4.s`, `ldc.i4.m1`, `ldc.i4.0`–`ldc.i4.8` | Complete within the admitted model | Push the encoded 32-bit integer constant. |
| `ldc.i8` | Complete within the admitted model | Push the encoded 64-bit integer constant. |
| `nop` | Complete within the admitted model | Advance without changing the stack or memory. |
| `dup`, `pop` | Complete within the admitted model | Duplicate or discard a supported stack value; stack underflow fails. |
| `ldarg`, `ldarg.s`, `ldarg.0`–`ldarg.3` | Partial | Load admitted argument values; struct instance methods have a managed-reference `this` at index zero; narrow integers are truncated and sign- or zero-extended to `i32`. Reference values undergo validity checks; class instance methods remain unsupported. |
| `starg`, `starg.s` | Partial | Assign a private parameter home using its declared storage type. Narrow stores truncate; byref assignment changes the private reference slot. Does not overwrite the caller's by-value source. |
| `ldarga`, `ldarga.s` | Partial | Address the same private parameter home read by `ldarg` and written by `starg`. Addresses expire when the frame returns. Taking the address of a byref parameter is rejected; nested-reference storage is unsupported. |
| `ldloc`, `ldloc.s`, `ldloc.0`–`ldloc.3` | Partial | Load admitted scalar, vector, aggregate or managed-reference locals. Narrow integers are sign- or zero-extended to `i32`; initialization and lifetime rules apply. |
| `stloc`, `stloc.s`, `stloc.0`–`stloc.3` | Partial | Store values compatible with the declared local storage kind; narrow integer locals truncate an `i32` to their physical width. No general object or reference-bearing aggregate storage. |
| `ldloca`, `ldloca.s` | Partial | Form a checked reference to byte-backed local storage. Taking the address of a managed-reference local is explicitly unsupported. |
| `neg` | Partial | Wrapping negation of an `i32` or `i64`; the signed minimum maps to itself. No floating-point or reference operands. |
| `add`, `sub`, `mul` | Partial | Wrapping arithmetic on two `i32` values or two `i64` values. No floating-point, mixed-width or reference/pointer arithmetic through these opcodes. |
| `div`, `div.un`, `rem`, `rem.un` | Partial | Same-width `i32`/`i64` quotient or remainder. Signed quotient truncates toward zero; signed remainder follows the dividend sign. Zero divisors fault. Signed minimum with divisor -1 faults for both signed operations under the admitted runtime assumption. No floating-point, mixed-width operands or exception handlers. |
| `add.ovf`, `sub.ovf`, `mul.ovf`, `add.ovf.un`, `sub.ovf.un`, `mul.ovf.un` | Partial | Checked signed/unsigned arithmetic on same-width `i32`/`i64`. Compute the mathematical integer result, then reject values outside the destination range with a located overflow fault. No floating-point, reference arithmetic or exception handlers. |
| `and`, `or`, `xor`, `not` | Partial | Bitwise operations on `i32`/`i64`; binary operands must have the same width. |
| `shl`, `shr`, `shr.un` | Partial | Shift an `i32` or `i64` by an `i32` count, masked modulo 32 or 64. `shr` is arithmetic; `shr.un` is logical. An `i64` count is not implemented. |
| `conv.ovf.i1`, `conv.ovf.u1`, `conv.ovf.i2`, `conv.ovf.u2`, `conv.ovf.i4`, `conv.ovf.u4`, `conv.ovf.i8`, `conv.ovf.u8`, `conv.ovf.i`, `conv.ovf.u`, and each corresponding `.un` form | Partial | Checked conversion from `i32`/`i64`, preserving the mathematical value or producing a located overflow fault. `.un` interprets the input as unsigned; the destination controls the accepted range. Narrow results occupy `i32`; native destinations use the validated 64-bit profile. No floating-point or reference conversions. |
| `conv.i4`, `conv.u4` | Partial | `i64` to low 32 bits; `i32` identity. No floating-point or reference conversions. |
| `conv.i1`, `conv.i2` | Partial | Truncate an `i32` or `i64` to eight or sixteen bits, then sign-extend to an `i32` stack value. |
| `conv.u2` | Partial | Truncate an `i32` or `i64` to sixteen bits, then zero-extend to an `i32` stack value. |
| `conv.u1` | Partial | Low eight bits of an `i32` or `i64`, zero-extended to an `i32` stack value. |
| `conv.u8` | Partial | Zero-extend `i32` to `i64`, or preserve an `i64`. |
| `conv.i8` | Partial | Sign-extend `i32` to `i64`, or preserve an `i64`. No floating-point or reference conversions. |
| `conv.i` | Partial | Sign-extend an integer `i32` to the admitted 64-bit native width, or preserve an `i64`. No pointer/reference or floating-point conversion. |
| `conv.u` | Partial | Model native unsigned integers as 64-bit: zero-extend `i32`, or preserve `i64`. Does not convert a managed reference to an integer address. |
| `clt`, `clt.un`, `cgt`, `cgt.un`, `ceq` | Partial | Same-width `i32`/`i64` comparisons, returning `i32` zero or one. `clt` and `cgt` are signed; `.un` comparisons are unsigned. No reference/null equality or floating-point/unordered comparisons. |
| `br`, `br.s` | Partial | Unconditional branch to an admitted instruction boundary, including backward edges and self-loops. |
| `switch` | Partial | Pop an `i32` unsigned table index; branch to its target or fall through when outside the table. Empty and duplicate-target tables are supported. All reachable targets must be valid instruction boundaries; each arm and the fallthrough participate in dependency and stack analysis. |
| `sizeof` | Partial | Push the validated storage width as `i32` for admitted integer types (including Boolean/char) or same-assembly explicit- or sequential-layout, reference-free aggregates. Native integers use eight bytes under the validated profile. No reference types, floating-point, generic layouts or vector types. |
| `brfalse`, `brfalse.s`, `brtrue`, `brtrue.s` | Partial | Zero/nonzero tests of `i32` or `i64`. No managed-reference/null truth tests. Admitted forward and backward successors. |
| `blt`, `blt.s`, `bge`, `bge.s`, `bgt`, `bgt.s`, `ble`, `ble.s` | Partial | Signed comparison of same-width `i32`/`i64`, branching to admitted forward or backward targets. |
| `blt.un`, `blt.un.s`, `bge.un`, `bge.un.s`, `bgt.un`, `bgt.un.s`, `ble.un`, `ble.un.s` | Partial | Unsigned comparison of same-width `i32`/`i64`, branching to admitted forward or backward targets. |
| `beq`, `beq.s`, `bne.un`, `bne.un.s` | Partial | Equality/inequality of same-width `i32`/`i64`, branching to admitted forward or backward targets. No reference or floating-point comparison. |
| `ldind.i`, `stind.i` | Partial | Native-width integer load/store through checked managed references; eight bytes on the admitted target, with the same allocation, permission and lifetime checks. |
| `ldind.i8`, `stind.i8` | Partial | Eight-byte integer load/store through a checked reference. Allocation bounds, permissions, initialization and lifetime rules apply; arbitrary numeric addresses are not accepted. |
| `ldind.i1`, `ldind.u1`, `ldind.i2`, `ldind.u2`, `ldind.i4`, `ldind.u4` | Partial | One-, two- or four-byte integer loads through a checked reference. Signed narrow loads sign-extend and unsigned loads zero-extend to `i32`; both four-byte forms return the same `i32` bits. Aggregate snapshots and numeric addresses are rejected. |
| `stind.i1`, `stind.i2`, `stind.i4` | Partial | Store the low one, two or four bytes of an `i32` through a checked reference. Allocation bounds, write permissions and lifetime apply; adjacent bytes remain unchanged. |
| `ldfld`, `ldflda`, `stfld` | Partial | Fields in same-assembly, validated explicit- or sequential-layout, reference-free value types, and `Item1`/`Item2` of an equal-width primitive `ValueTuple<T1, T2>` (see [value tuples](SOUNDNESS.md#value-tuples)). Supported field storage is `sbyte`, byte/Boolean, `short`, `ushort`/`char`, 32-bit integer, 64-bit integer, native integer, integer-backed enum or nested reference-free aggregate. Nested snapshots and assignments copy all field bytes, including padding. Narrow stores truncate; narrow loads sign- or zero-extend to `i32` according to field metadata. `ldfld` accepts an aggregate byte snapshot or reference; field addresses and stores require a reference. No general managed objects, auto layouts or static fields through these opcodes. |
| `ldobj`, `stobj` | Partial | Load/store admitted integer types through checked references, with narrow truncation/extension derived from the validated type token. Also copy validated aggregates of 1–65,536 bytes, or exactly `Vector128<ulong>` / `Vector256<ulong>`. No general objects, reference-bearing storage, floating-point tokens. Native-integer tokens use eight-byte storage. |
| `cpobj` | Partial | Copy validated integer, aggregate or Vector128/256 ulong storage through checked references. Requires initialized readable source and writable destination; self-copy is supported, partial overlap is rejected. No reference-bearing or floating-point tokens. |
| `initobj` | Partial | Zero the validated width of an admitted integer type or same-assembly explicit- or sequential-layout aggregate. This initializes previously unknown bytes without touching neighboring storage. No general vector or managed-object initialization. |
| `ldsfld` | Partial | Value of a same-assembly `static readonly` integer, enum or reference-free struct field that its static constructor fixes, with the declaring type named by `--assume-initialized` (see [static readonly values](#static-readonly-values)). Other static fields are rejected. |
| `ldsflda` | Partial | Address of validated same-assembly static readonly RVA data with an explicit packed blob layout and no static constructor. A `ReadOnlySpan<byte>` over such data may be returned by value (for example from a C# collection-expression property); see [static span tables](#static-span-tables) for other element types. Not arbitrary static fields or mutable global state. |
| `call` | Partial | Acyclic calls to supported static methods or reference-free struct instance methods (including direct constructor calls) in the same assembly, concrete generic-method specializations, or exact runtime/intrinsic signatures in the allowlist. No arbitrary external calls, generic declaring types, class instance methods or virtual dispatch. |
| `newobj` | Partial | Same-assembly constructors of validated reference-free structs: zero-initialize caller-owned storage, invoke the constructor with managed-reference `this`, then return a checked value snapshot. Also the explicitly modelled `ReadOnlySpan<byte>(void*, int)` runtime constructor. Class construction, generic constructors and cyclic dependencies are rejected. |
| `ldtoken` | Partial | A type token as an operand of a decided closed type test, which emits a no-op, or a static data field token for `RuntimeHelpers.CreateSpan<T>`, which emits the field's address (see below). Other tokens are rejected. |
| `throw` | Partial | Only `throw new E(...)` with `ldstr`/`ldnull` arguments (see below): it raises a located `thrown "E"` fault. Other throws are rejected. |
| `constrained.`, `callvirt` | Partial | Adjacent prefix and call resolving to a concrete same-assembly struct implementation; see [constrained struct calls](#constrained-struct-calls). No boxing or general virtual dispatch. |
| `ret` | Partial | Return from an admitted method with exactly zero or one result according to its signature. Narrow integer results are truncated and sign- or zero-extended to `i32`. The checked model validates returned references and rejects references that escape expired local storage. |
| `initblk`, `cpblk` | Partial | Managed references and unsigned 32-bit counts; checked block alignment and access rules. Nonempty overlapping copies are rejected. |
| `unaligned.` | Partial | Values 1, 2 and 4 before supported ordinary or block memory accesses; malformed prefix sequences and interior branch targets are rejected. |

## Block memory and alignment prefixes

`initblk` and `cpblk` are partially supported for checked managed references and unsigned 32-bit byte counts. Initialization uses the low eight bits of its integer value. Copying requires initialized, readable source bytes; both operations require writable destination bytes, valid lifetimes, bounds and reference-free storage. Every nonempty overlapping copy, including an exact alias, is rejected because CLI overlap behaviour is unspecified. Zero counts access no memory and permit null references.

Unprefixed block operations require eight-byte alignment on the admitted 64-bit target. Model-owned 32-bit and 64-bit scalar local/parameter homes carry four-byte and eight-byte natural alignment respectively, so aligned block access can succeed on a 64-bit scalar home. Aggregate, vector and narrow homes retain conservative byte alignment. An immediately preceding `unaligned. 1`, `2` or `4` selects that alignment requirement. Prefix operands, permitted followers and branch targets are validated: a branch cannot enter between a prefix and its instruction. Prefix combinations with unsupported modifiers remain rejected.

`unaligned.` is also accepted before supported integer `ldind.*`/`stind.*`, `ldobj`/`stobj` and `ldfld`/`stfld` instructions. These retain the existing target-specific ordinary byte-aligned memory semantics; a prefix does not bypass any safety check. The prefix occupies its original instruction position and lowers to a no-op, with block alignment encoded in the following operation.

The exact managed-reference overloads of `Unsafe.InitBlock`, `InitBlockUnaligned`, `CopyBlock` and `CopyBlockUnaligned` use these same operations. Pointer overloads and arbitrary integer addresses remain unsupported.

## Unsupported opcodes

The table above is exhaustive for reachable translation. Notable exclusions include:

| Area | Examples rejected by extraction |
| --- | --- |
| Debugger and prefixes | `break`, `volatile.`, `readonly.`, `tail.`; `constrained.` outside the checked struct-call subset |
| Other conversions | Floating-point conversions |
| Other indirect/block memory | `ldind.ref`, floating-point `ldind.*`, `stind.ref`, floating-point `stind.*`, `localloc` |
| Objects, arrays and metadata | `ldnull` and `ldstr` outside a folded throw, `box`, `unbox`, `unbox.any`, `castclass`, `isinst`, `newarr`, `ldlen`, all `ldelem.*`/`stelem.*` forms, `ldelema`, `ldtoken` of a method or of a type outside a decided type test |
| Static field values | `stsfld`, `ldsfld` of other fields, `ldsflda` of constructor-initialized fields |
| Dispatch and exceptions | Unconstrained `callvirt`, `calli`, `jmp`, `ldftn`, `ldvirtftn`, `throw` outside a folded throw, `rethrow`, `leave`, `leave.s`, `endfinally`, `endfilter` |
| Floating-point constants | `ldc.r4`, `ldc.r8` |

### Type tests

In a specialized generic body, `typeof(A) == typeof(B)` and `typeof(A) != typeof(B)` compile to `ldtoken A; call Type::GetTypeFromHandle; ldtoken B; call Type::GetTypeFromHandle; call Type::op_Equality` (or `op_Inequality`), with the `System.Runtime` signatures. When both types are closed and their identity is decided, the four operand instructions emit `nop` and the comparison emits `ldc.i4.0` or `ldc.i4.1`, as the JIT folds them. Profile reachability then prunes the dead branch. Types are equal when their metadata is identical, and different when their full names differ; one full name in two scopes, decorated names and `void` stay undecided. Undecided tests, any other instruction between the five, a branch into the last four, other `System.Type` members and `Type` values in locals remain rejected.

### Throws

`throw new E(...)` compiles to one `ldstr` or `ldnull` per constructor argument, `newobj` of `E`'s constructor and `throw`. When `E` is a `System.Runtime` type, the loads and `newobj` emit `nop` and `throw` emits `.throw "E"`, which ends execution with a fault located at the `throw`. A `[DoesNotReturn]` helper containing only this pattern is an ordinary call. Other arguments, any instruction between the parts, a branch past the first part, rethrowing a stored exception and exception handlers remain rejected.

### Constrained struct calls

An adjacent `constrained. T; callvirt` pair supports a concrete, reference-free same-assembly
struct `T` and a method declared on that struct or a directly implemented same-assembly interface.
Implicit implementations must uniquely match the public name and signature; explicit `MethodImpl`
overrides take precedence. Closed generic helpers can use a directly implemented interface constraint.
The original managed-reference receiver is passed to the resolved implementation, so mutations
remain visible to the caller without boxing.

The Lean certificate independently resolves serialized type, interface and method metadata and
checks the selected method token, signature and argument count. A branch cannot bypass the prefix.
Reference receivers, boxing fallbacks, inherited or default-interface dispatch, generic declaring
types and ordinary unconstrained virtual calls remain unsupported.

### Static span tables

Primitive integer `Span<T>` and `ReadOnlySpan<T>` also have typed, allocation-relative storage
for by-value parameters and reusable locals. Their length, indexing, slicing and readonly
conversion retain element width and allocation lifetime. `MemoryMarshal.CreateSpan` and
`CreateReadOnlySpan` form views over existing storage; they do not grant access authority or
initialize bytes. Readonly element references reject stores, while other writable aliases
can still update the same backing memory. Slicing checks signed input ranges and permits an
empty view at the allocation end. Byref span parameters and general ref structs remain outside
this support.

A collection-expression property such as `static ReadOnlySpan<uint> Table => [...]` compiles to `ldtoken <field>; call RuntimeHelpers::CreateSpan<uint>` over a static data field (`ldsflda` rules, packing 1, 2, 4 or 8). The span covers the whole field and has `size / sizeof(T)` elements, for any primitive integer `T`. A caller reads it as `stloc s; ldloca s; [index;] call get_Item` or `stloc s; ldloca s; call get_Length`: the store and address emit `nop`, so the span stays on the stack as the receiver. `get_Item` faults with `System.IndexOutOfRangeException` at the call when the index is out of range, compared unsigned as in .NET. `MemoryMarshal.GetReference` also accepts these spans. The fold is used only for a single-use receiver with a single-load or constant index; other supported uses retain typed span storage. Branches into a folded receiver and byref spans remain rejected.

### Static readonly values

Primitive integer fields (including Boolean, Char and 64-bit native integers) and same-assembly
integer enums also admit a direct integer literal, optionally widened with the supported integer
conversions. They may instead use the same checked helper-call initializer or copy an earlier
field of the same type. Loads truncate to the declared storage width and sign-extend signed
8-/16-bit fields. Lean checks stored bytes against the literal or executed initializer and binds
the load width and signedness to the raw field type. Mutable fields, address-taking during
initialization, repeated stores and conditional initialization remain rejected.

`public static readonly UInt256 One = 1ul;` compiles to `ldc.i4.1; conv.i8; call op_Implicit(ulong); stsfld One` in the static constructor. A reachable `ldsfld` of such a field emits `.staticValue bytes`, which pushes the field's value as an aggregate and touches no memory. The static constructor must store the field exactly once, unconditionally (no control flow before the store and no branch back to it), as the result of a same-assembly static call whose arguments are integer constants (`ldc.i4*`, `ldc.i8` with `conv.i4`/`conv.u4`/`conv.i8`/`conv.u8`/`conv.i`/`conv.u`), or as a copy (`ldsfld G; stsfld F`) of such a field stored earlier, as in `MinValue = Zero`. The field's declaring type must be named by `--assume-initialized`. The called method and its callees become part of the extracted program and must not access static fields. The static site records the call, and the extraction certificate reruns it in the checked interpreter: the result must be exactly the emitted bytes, or `translation_valid` fails.

Rejected: a declaring type without the assumption; values built by `newobj` in the static constructor or by any other code shape; a second store, a store outside the static constructor, or `ldsflda` of the field during initialization; `stsfld` in an extracted method; and `ldsflda` of the field in an extracted method, so its address, and any write through it, is never formed. Static fields of primitive type are rejected too.

Release configuration is required, but it does not guarantee that a compiler emits only supported instructions. For example, reachable array allocation or exception handling is still rejected.

## Runtime calls and SIMD

Reachable same-assembly generic methods are specialized for supported primitive, enum, reference-free aggregate and vector type arguments. This substitutes types in the original CIL parameters, locals, type operands and nested generic calls; it does not replace method bodies with functional summaries. Repeated uses share a specialization, while different type arguments retain separate bodies. The call graph must remain acyclic, and extraction rejects more than 256 distinct specializations.

Select a non-generic entry method whose compiled calls supply the concrete type arguments. Generic declaring types, generic constructors, reference-type constraints, boxing, general runtime dispatch and unsupported storage types remain rejected. A same-assembly interface constraint is admitted when the concrete struct directly declares that interface; constrained calls are checked as described below. Unconstrained parameters and admitted value-type/default-constructor/unmanaged constraints are supported for the reference-free value types above. Every specialized body's instructions undergo the normal validation.

See the [per-family intrinsic tables](SIMD.md) for the exact Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM operations, operand types and profile requirements.

SIMD and hardware features enter compiled CIL mostly through `call`, rather than dedicated SIMD CIL opcodes. Selected Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM overloads have models. The exact allowed runtime assembly identities, generic arguments, signatures and capability requirements are defined in [RuntimeModels.cs](../Extractor/RuntimeModels.cs) and [FeatureProfiles.cs](../Extractor/FeatureProfiles.cs). Supporting one overload or CPU feature does not mean the entire API is supported.

`Unsafe.SizeOf<T>()` and the managed-reference `Unsafe.Add<T>` overloads with `int`, `nint` or `nuint` offsets use validated layouts for supported integer primitives, enums, reference-free structs and supported Vector128/256 types. Sizes include managed packing and padding; reference offsets scale by that size and wrap at the validated native width. Forming the resulting reference checks allocation identity, lifetime and bounds, including explicitly admitted one-past positions. It does not grant permission to read or write. Classes, pointer/byref type arguments and unsupported layouts fail extraction.

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
both directions, as for `SkipInit`. `ldnull` remains unsupported: this is a null
byref, not a null object reference.

The runtime allowlist also includes specific `Unsafe.AsRef`, `Unsafe.As`, `Unsafe.BitCast`, `MemoryMarshal.GetReference` and byte-span constructor signatures. These are narrow translations into reference, memory or vector operations, not blanket support for those classes. CIL `add` on references remains unsupported.

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

Native-width overloads use the validated 64-bit target. The 128-bit, span, generic-math and other helper overloads remain unsupported. The extractor validates the exact .NET 10 runtime assembly identity, declaring type, static calling convention and signature. These portable API semantics do not require any ISA to be enabled and do not establish correctness of a particular runtime implementation.

### Vector fields

Instance fields support `Vector128<ulong>` and `Vector256<ulong>`, matching the
vector types admitted by `ldobj` and `stobj`. The owner must have a validated,
reference-free sequential or explicit layout. Other vector element types and
widths in fields are rejected. Auto-layout tuples do not admit vector fields.
Layout computation uses CoreCLR's default packing limit of 64 bytes.
`Vector128<ulong>` has natural field alignment 16. `Vector256<ulong>` has natural
field alignment 32 under x64 profiles and 16 under ARM64 profiles. Explicit
packing caps these values. The checked method profile selects the layout in both
the extractor and the Lean certificate. A scalar profile must use an explicit
packing limit of at most 16 for `Vector256<ulong>` fields because it does not
select a target architecture.

Field widths come from the vector type. Raw layout evidence keeps vector storage
separate from integer and nested aggregate storage. Lean recomputes each field
offset and checks each field instruction against that evidence.

Field reads and writes use the ordinary byte-aligned access rule. A packed field
does not require vector-width alignment. Checked accesses retain allocation
bounds and initialization masks. `Unsafe.As` can expose these fields through an
admitted struct reference without changing its address or access bounds.
