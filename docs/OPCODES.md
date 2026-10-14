# CIL opcode support

This table covers all 148 opcode encodings currently handled by the translator and describes the allocation-aware execution model used for memory-safety proofs. It is an inventory of implemented behaviour, not a claim that every listed opcode/operand combination has its own regression test, or that the model is equivalent to every .NET runtime.

- **Complete within the admitted model:** the opcode's operation is implemented for its admitted operands. Ordinary stack/value validity checks still apply.
- **Partial:** translation exists, but the row lists additional type, layout, control-flow or runtime restrictions. Unsupported operand shapes can fail during checked execution even when translation succeeds.
- **Unsupported:** no reachable translation exists; extraction rejects the opcode. All opcodes not listed in the translated-opcode table are unsupported.

Every row is subject to the common target restrictions: Release IL-only .NET 10 assemblies, 64-bit little-endian execution, admitted types, no exception handlers, forward-only reachable control flow and an acyclic graph of static managed methods. A translated method still requires a proof of the desired property. Exhausted fuel, invalid states and unsupported operations are failures, never implicit successes.

## Translated opcodes

Ranges below include every numbered form between the endpoints. `.s` denotes the actual short encoding, not a different semantic operation. Native `nint`/`nuint` values use `i64` under the validated 64-bit target. For mixed native/int32 arithmetic and comparisons, extraction tracks stack types and emits an explicit widening wrapper; invalid native/int64 mixtures are rejected. The wrapper sign-extends the int32 operand, except that unsigned checked arithmetic and unsigned conditional branches zero-extend it. Scalar `clt.un`/`cgt.un` still sign-extend, matching the admitted runtime. The wrapper preserves arithmetic faults and branch targets and cannot dispatch memory or calls. The rows below describe scalar operands after this widening; other mixed widths remain unsupported.

`i32` and `i64` refer to the model's 32- and 64-bit integer stack values; managed references are separate values, not integer addresses.

Same-assembly enums backed by `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long` or `ulong` use their validated underlying integer representation throughout these operations, including fields, argument homes and typed memory instructions. Narrow enum loads sign- or zero-extend exactly like the underlying type. Unnamed values are supported; boxing, `System.Enum` methods and external enum dependencies are not.

| Opcodes | Status | Implemented behaviour and restrictions |
| --- | --- | --- |
| `ldc.i4`, `ldc.i4.s`, `ldc.i4.m1`, `ldc.i4.0`–`ldc.i4.8` | Complete within the admitted model | Push the encoded 32-bit integer constant. |
| `ldc.i8` | Complete within the admitted model | Push the encoded 64-bit integer constant. |
| `nop` | Complete within the admitted model | Advance without changing the stack or memory. |
| `dup`, `pop` | Complete within the admitted model | Duplicate or discard a supported stack value; stack underflow fails. |
| `ldarg`, `ldarg.s`, `ldarg.0`–`ldarg.3` | Partial | Load admitted argument values in static methods; narrow integers are truncated and sign- or zero-extended to `i32`. Reference values undergo validity checks; this does not provide general instance-method support. |
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
| `br`, `br.s` | Partial | Unconditional branch to an admitted forward target. Reachable backward edges and cycles are rejected. |
| `switch` | Partial | Pop an `i32` unsigned table index; branch to its target or fall through when outside the table. Empty and duplicate-target tables are supported. All reachable targets must be forward instruction boundaries; each arm and the fallthrough participate in dependency and stack analysis. |
| `sizeof` | Partial | Push the validated storage width as `i32` for admitted integer types (including Boolean/char) or same-assembly explicit- or sequential-layout, reference-free aggregates. Native integers use eight bytes under the validated profile. No reference types, floating-point, generic layouts or vector types. |
| `brfalse`, `brfalse.s`, `brtrue`, `brtrue.s` | Partial | Zero/nonzero tests of `i32` or `i64`. No managed-reference/null truth tests. Only admitted forward successors. |
| `blt`, `blt.s`, `bge`, `bge.s`, `bgt`, `bgt.s`, `ble`, `ble.s` | Partial | Signed comparison of same-width `i32`/`i64`, branching forward. |
| `blt.un`, `blt.un.s`, `bge.un`, `bge.un.s`, `bgt.un`, `bgt.un.s`, `ble.un`, `ble.un.s` | Partial | Unsigned comparison of same-width `i32`/`i64`, branching forward. |
| `beq`, `beq.s`, `bne.un`, `bne.un.s` | Partial | Equality/inequality of same-width `i32`/`i64`, branching forward. No reference or floating-point comparison. |
| `ldind.i`, `stind.i` | Partial | Native-width integer load/store through checked managed references; eight bytes on the admitted target, with the same allocation, permission and lifetime checks. |
| `ldind.i8`, `stind.i8` | Partial | Eight-byte integer load/store through a checked reference. Allocation bounds, permissions, initialization and lifetime rules apply; arbitrary numeric addresses are not accepted. |
| `ldind.i1`, `ldind.u1`, `ldind.i2`, `ldind.u2`, `ldind.i4`, `ldind.u4` | Partial | One-, two- or four-byte integer loads through a checked reference. Signed narrow loads sign-extend and unsigned loads zero-extend to `i32`; both four-byte forms return the same `i32` bits. Aggregate snapshots and numeric addresses are rejected. |
| `stind.i1`, `stind.i2`, `stind.i4` | Partial | Store the low one, two or four bytes of an `i32` through a checked reference. Allocation bounds, write permissions and lifetime apply; adjacent bytes remain unchanged. |
| `ldfld`, `ldflda`, `stfld` | Partial | Fields in same-assembly, validated explicit- or sequential-layout, reference-free value types. Supported field storage is `sbyte`, byte/Boolean, `short`, `ushort`/`char`, 32-bit integer, 64-bit integer or native integer. Narrow stores truncate; narrow loads sign- or zero-extend to `i32` according to field metadata. `ldfld` accepts an aggregate byte snapshot or reference; field addresses and stores require a reference. No general managed objects, auto layouts or static fields through these opcodes. |
| `ldobj`, `stobj` | Partial | Load/store admitted integer types through checked references, with narrow truncation/extension derived from the validated type token. Also copy validated aggregates of 1–65,536 bytes, or exactly `Vector128<ulong>` / `Vector256<ulong>`. No general objects, reference-bearing storage, floating-point tokens. Native-integer tokens use eight-byte storage. |
| `cpobj` | Partial | Copy validated integer, aggregate or Vector128/256 ulong storage through checked references. Requires initialized readable source and writable destination; self-copy is supported, partial overlap is rejected. No reference-bearing or floating-point tokens. |
| `initobj` | Partial | Zero the validated width of an admitted integer type or same-assembly explicit- or sequential-layout aggregate. This initializes previously unknown bytes without touching neighboring storage. No general vector or managed-object initialization. |
| `ldsflda` | Partial | Address of validated same-assembly static readonly RVA data with an explicit packed blob layout and no static constructor. Not arbitrary static fields or mutable global state. |
| `call` | Partial | Acyclic calls to supported static managed methods in the same assembly, or exact runtime/intrinsic signatures in the allowlist. No arbitrary external calls, generic managed dependencies, instance methods or virtual dispatch. |
| `newobj` | Partial | Only the explicitly modelled `ReadOnlySpan<byte>(void*, int)` constructor via the runtime allowlist. This models span formation, not general object allocation. General value-type constructors and class construction are rejected. |
| `ret` | Partial | Return from an admitted method with exactly zero or one result according to its signature. Narrow integer results are truncated and sign- or zero-extended to `i32`. The checked model validates returned references and rejects references that escape expired local storage. |

## Unsupported opcodes

The table above is exhaustive for reachable translation. Notable exclusions include:

| Area | Examples rejected by extraction |
| --- | --- |
| Debugger and prefixes | `break`, `volatile.`, `unaligned.`, `readonly.`, `tail.`, `constrained.` |
| Other conversions | Floating-point conversions |
| Other indirect/block memory | `ldind.ref`, floating-point `ldind.*`, `stind.ref`, floating-point `stind.*`, `cpblk`, `initblk`, `localloc` |
| Objects, arrays and metadata | `ldnull`, `ldstr`, `box`, `unbox`, `unbox.any`, `castclass`, `isinst`, `newarr`, `ldlen`, all `ldelem.*`/`stelem.*` forms, `ldelema`, `ldtoken` |
| Static field values | `ldsfld`, `stsfld` |
| Dispatch and exceptions | `callvirt`, `calli`, `jmp`, `ldftn`, `ldvirtftn`, `throw`, `rethrow`, `leave`, `leave.s`, `endfinally`, `endfilter` |
| Floating-point constants | `ldc.r4`, `ldc.r8` |

Release configuration is required, but it does not guarantee that a compiler emits only supported instructions. For example, reachable array allocation or exception handling is still rejected.

## Runtime calls and SIMD

See the [per-family intrinsic tables](SIMD.md) for the exact Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM operations, operand types and profile requirements.

SIMD and hardware features enter compiled CIL mostly through `call`, rather than dedicated SIMD CIL opcodes. Selected Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM overloads have models. The exact allowed runtime assembly identities, generic arguments, signatures and capability requirements are defined in [RuntimeModels.cs](../Extractor/RuntimeModels.cs) and [FeatureProfiles.cs](../Extractor/FeatureProfiles.cs). Supporting one overload or CPU feature does not mean the entire API is supported.

The runtime allowlist also includes specific `Unsafe.AsRef`, `Unsafe.As`, `Unsafe.Add`, `Unsafe.BitCast`, `MemoryMarshal.GetReference` and byte-span constructor signatures. These are narrow translations into reference, memory or vector operations, not blanket support for those classes. For example, `Unsafe.Add<ulong>` has a reference-offset model although CIL `add` on references is not implemented.

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

Native-width overloads use the validated 64-bit target. The 128-bit, span, generic-math and other helper overloads remain unsupported. The extractor validates the exact .NET 10 runtime assembly identity, declaring type, static calling convention and signature. These portable API semantics do not require any ISA to be enabled and do not establish correctness of a particular runtime implementation.
