# CIL opcode support

This table covers all 96 opcode encodings currently handled by the translator and describes the allocation-aware execution model used for memory-safety proofs. It is an inventory of implemented behaviour, not a claim that every listed opcode/operand combination has its own regression test, or that the model is equivalent to every .NET runtime.

- **Complete within the admitted model:** the opcode's operation is implemented for its admitted operands. Ordinary stack/value validity checks still apply.
- **Partial:** translation exists, but the row lists additional type, layout, control-flow or runtime restrictions. Unsupported operand shapes can fail during checked execution even when translation succeeds.
- **Unsupported:** no reachable translation exists; extraction rejects the opcode. All opcodes not listed in the translated-opcode table are unsupported.

Every row is subject to the common target restrictions: Release IL-only .NET 10 assemblies, 64-bit little-endian execution, admitted types, no exception handlers, forward-only reachable control flow and an acyclic graph of static managed methods. A translated method still requires a proof of the desired property. Exhausted fuel, invalid states and unsupported operations are failures, never implicit successes.

## Translated opcodes

Ranges below include every numbered form between the endpoints. `.s` denotes the actual short encoding, not a different semantic operation. `i32` and `i64` refer to the model's 32- and 64-bit integer stack values; managed references are separate values, not integer addresses.

| Opcodes | Status | Implemented behaviour and restrictions |
| --- | --- | --- |
| `ldc.i4`, `ldc.i4.s`, `ldc.i4.m1`, `ldc.i4.0`–`ldc.i4.8` | Complete within the admitted model | Push the encoded 32-bit integer constant. |
| `ldc.i8` | Complete within the admitted model | Push the encoded 64-bit integer constant. |
| `nop` | Complete within the admitted model | Advance without changing the stack or memory. |
| `dup`, `pop` | Complete within the admitted model | Duplicate or discard a supported stack value; stack underflow fails. |
| `ldarg`, `ldarg.s`, `ldarg.0`–`ldarg.3` | Partial | Load admitted argument values in static methods. Reference values undergo validity checks; this does not provide general instance-method support. |
| `ldloc`, `ldloc.s`, `ldloc.0`–`ldloc.3` | Partial | Load admitted scalar, vector, aggregate or managed-reference locals. Initialization and lifetime rules apply. |
| `stloc`, `stloc.s`, `stloc.0`–`stloc.3` | Partial | Store values compatible with the declared local storage kind. No general object or reference-bearing aggregate storage. |
| `ldloca`, `ldloca.s` | Partial | Form a checked reference to byte-backed local storage. Taking the address of a managed-reference local is explicitly unsupported. |
| `neg` | Partial | Wrapping negation of an `i32` or `i64`; the signed minimum maps to itself. No floating-point or reference operands. |
| `add`, `sub`, `mul` | Partial | Wrapping arithmetic on two `i32` values or two `i64` values. No floating-point, mixed-width or reference/pointer arithmetic through these opcodes. |
| `and`, `or`, `xor`, `not` | Partial | Bitwise operations on `i32`/`i64`; binary operands must have the same width. |
| `shl`, `shr`, `shr.un` | Partial | Shift an `i32` or `i64` by an `i32` count, masked modulo 32 or 64. `shr` is arithmetic; `shr.un` is logical. An `i64` count is not implemented. |
| `conv.i4`, `conv.u4` | Partial | `i64` to low 32 bits; `i32` identity. No floating-point or reference conversions. |
| `conv.u1` | Partial | Low eight bits of an `i32` or `i64`, zero-extended to an `i32` stack value. |
| `conv.u8` | Partial | Zero-extend `i32` to `i64`, or preserve an `i64`. |
| `conv.i8` | Partial | Sign-extend `i32` to `i64`. The `i64` identity case is currently not implemented by the execution semantics. |
| `conv.u` | Partial | Model native unsigned integers as 64-bit: zero-extend `i32`, or preserve `i64`. Does not convert a managed reference to an integer address. |
| `clt`, `clt.un`, `cgt`, `cgt.un`, `ceq` | Partial | Same-width `i32`/`i64` comparisons, returning `i32` zero or one. `clt` and `cgt` are signed; `.un` comparisons are unsigned. No reference/null equality or floating-point/unordered comparisons. |
| `br`, `br.s` | Partial | Unconditional branch to an admitted forward target. Reachable backward edges and cycles are rejected. |
| `brfalse`, `brfalse.s`, `brtrue`, `brtrue.s` | Partial | Zero/nonzero tests of `i32` or `i64`. No managed-reference/null truth tests. Only admitted forward successors. |
| `blt`, `blt.s`, `bge`, `bge.s`, `bgt`, `bgt.s`, `ble`, `ble.s` | Partial | Signed comparison of same-width `i32`/`i64`, branching forward. |
| `blt.un`, `blt.un.s`, `bge.un`, `bge.un.s`, `bgt.un`, `bgt.un.s`, `ble.un`, `ble.un.s` | Partial | Unsigned comparison of same-width `i32`/`i64`, branching forward. |
| `beq`, `beq.s`, `bne.un`, `bne.un.s` | Partial | Equality/inequality of same-width `i32`/`i64`, branching forward. No reference or floating-point comparison. |
| `ldind.i8`, `stind.i8` | Partial | Eight-byte integer load/store through a checked reference. Allocation bounds, permissions, initialization and lifetime rules apply; arbitrary numeric addresses are not accepted. |
| `ldfld`, `ldflda`, `stfld` | Partial | Fields in same-assembly, validated explicit-layout, reference-free value types. Supported field storage is byte/Boolean, 32-bit integer or 64-bit integer. `ldfld` accepts an aggregate byte snapshot or reference; field addresses and stores require a reference. No general managed objects, implicit layouts or static fields through these opcodes. |
| `ldobj`, `stobj` | Partial | Copy validated aggregates of 1–65,536 bytes, or exactly `Vector128<ulong>` / `Vector256<ulong>`, through references. These are not general typed loads/stores; primitive scalar `ldobj`/`stobj` cases are not translated. |
| `initobj` | Partial | Zero a validated same-assembly explicit-layout aggregate. No general primitive, vector or managed-object initialization through this opcode. |
| `ldsflda` | Partial | Address of validated same-assembly static readonly RVA data with an explicit packed blob layout and no static constructor. Not arbitrary static fields or mutable global state. |
| `call` | Partial | Acyclic calls to supported static managed methods in the same assembly, or exact runtime/intrinsic signatures in the allowlist. No arbitrary external calls, generic managed dependencies, instance methods or virtual dispatch. |
| `newobj` | Partial | Only the explicitly modelled `ReadOnlySpan<byte>(void*, int)` constructor via the runtime allowlist. This models span formation, not general object allocation. General value-type constructors and class construction are rejected. |
| `ret` | Partial | Return from an admitted method with exactly zero or one result according to its signature. The checked model validates returned references and rejects references that escape expired local storage. |

## Unsupported opcodes

The table above is exhaustive for reachable translation. Notable exclusions include:

| Area | Examples rejected by extraction |
| --- | --- |
| Debugger and prefixes | `break`, `volatile.`, `unaligned.`, `readonly.`, `tail.`, `constrained.` |
| Argument mutation/addressing | `starg`, `starg.s`, `ldarga`, `ldarga.s` |
| Arithmetic | `div`, `div.un`, `rem`, `rem.un`, `add.ovf`, `sub.ovf`, `mul.ovf` and their `.un` forms |
| Other control flow | `switch` |
| Other conversions | `conv.i`, `conv.i1`, `conv.i2`, `conv.u2`, floating-point conversions and all `conv.ovf.*` forms |
| Other indirect/block memory | `ldind.i1`, `ldind.u1`, `ldind.i2`, `ldind.u2`, `ldind.i4`, `ldind.u4`, `ldind.i`, `ldind.ref`, other `stind.*` forms, `cpobj`, `cpblk`, `initblk`, `localloc` |
| Objects, arrays and metadata | `ldnull`, `ldstr`, `box`, `unbox`, `unbox.any`, `castclass`, `isinst`, `newarr`, `ldlen`, all `ldelem.*`/`stelem.*` forms, `ldelema`, `ldtoken`, `sizeof` |
| Static field values | `ldsfld`, `stsfld` |
| Dispatch and exceptions | `callvirt`, `calli`, `jmp`, `ldftn`, `ldvirtftn`, `throw`, `rethrow`, `leave`, `leave.s`, `endfinally`, `endfilter` |
| Floating-point constants | `ldc.r4`, `ldc.r8` |

In particular, Release configuration is required, but it does not guarantee that a compiler emits only supported instructions. A Release assembly containing a reachable `switch` is still rejected.

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
