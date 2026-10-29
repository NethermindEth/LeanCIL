# Vector and hardware-intrinsic support

These tables list the overloads currently recognised by the extractor, not entire .NET API families. All families have **partial coverage**. Calls must match the runtime assembly identity, declaring type, generic arguments, parameter types and return type in [RuntimeModels.cs](../Extractor/RuntimeModels.cs). Other overloads are rejected.

`V128<T>`, `V256<T>` and `V512<T>` below abbreviate `Vector128<T>`, `Vector256<T>` and `Vector512<T>`. Unqualified vector APIs belong to `System.Runtime.Intrinsics`; x86 families belong to `.X86`, and ARM families to `.Arm`. Names such as `Avx512F.VL` use C# notation for nested types.

Values are modelled as bit patterns with lane zero in the least-significant bits. Integer arithmetic wraps at the lane width. Floating-point vector types appear in a few reinterpretation, selection and mask operations; this does **not** provide floating-point arithmetic semantics.

## Overview

| Family | Extractable operations |
| --- | --- |
| [Portable vectors](#portable-vector-operations) | Selected integer arithmetic, bitwise/equality operators, lane comparisons, construction, extraction, reductions, arithmetic shifts and bit reinterpretation |
| [SSE](#sse) | `Sse2.ShiftLeftLogical128BitLane`, `Ssse3.AlignRight`; SSE4.1/4.2 getters only |
| [AVX](#avx) | Selected `MoveMask`, `Blend`, `TestZ` overloads |
| [AVX2](#avx2) | `Permute4x64`, `Blend`, `Add`, `CompareEqual`, `CompareGreaterThan`, widening even-lane `Multiply`, bitwise operations, logical shifts |
| [AVX512](#avx512) | F.VL alignment, ternary logic and unsigned comparisons; DQ mask extraction and DQ.VL low multiplication on 256-bit vectors; F unsigned comparisons and DQ mask extraction on 512-bit vectors |
| [BMI](#bmi) | `Bmi1.BitFieldExtract(uint, byte, byte)`, `Bmi2.X64.MultiplyNoFlags(ulong, ulong)` |
| [X86Base](#x86base) | `X86Base.X64.DivRem(ulong, ulong, ulong)` returning `(ulong Quotient, ulong Remainder)` |
| [ARM](#arm) | `AdvSimd.ExtractVector128` on `ulong` lanes, `ArmBase.Arm64.MultiplyHigh(ulong, ulong)` |

An enabled CPU feature does not imply support for all of its APIs. Float/double vectors are used only for selected bit operations, not floating-point arithmetic. Vector64 is not supported, and Vector512 only through the rows below that name it. See the [profile table](#feature-getters-profiles-and-execution-restrictions) for the exact flags enabled by each built-in profile.

## Portable vector operations

Rows apply to the named widths, with matching input/output widths. The bitwise and equality operators accept Vector128, Vector256 and Vector512. These portable vector operations require no ISA flag in the extractor and can be modelled under the `scalar` profile; that is a semantics choice, not a claim about how a JIT implements them.

| API / operation | Accepted element types / overloads | Model |
| --- | --- | --- |
| `Vector128<T>` / `Vector256<T>` operators `+`, `-` | `T = ulong` | Per-lane wrapping 64-bit addition/subtraction |
| Operators `&`, `\|`, `^`, `~` | `T = byte`, `int`, `uint`, `long`, `ulong` | Bitwise operations on the complete vector |
| Operator `==` | `T = byte`, `int`, `uint`, `long`, `ulong` | Boolean equality of all bits; `!=` is not mapped |
| `Vector128.LessThan<ulong>`, `Vector256.LessThan<ulong>` | Two vectors of `ulong` | Unsigned per-lane comparison; each result lane is all ones or zero |
| `Vector128.Equals<ulong>`, `Vector256.Equals<ulong>` | Two vectors of `ulong` | Per-lane equality masks |
| `Vector128.EqualsAll<T>`, `Vector256.EqualsAll<T>`, `Vector512.EqualsAll<T>` | `T = byte`, `int`, `uint`, `long`, `ulong` | One Boolean result |
| `Vector128.GetElement<ulong>`, `Vector256.GetElement<ulong>` | Vector and `int` index | Return one `ulong`; valid indices are 0–1 / 0–3; other indices fail |
| `Vector128<T>.Zero`, `Vector256<T>.Zero`, `Vector512<T>.Zero` | `T = byte`, `int`, `uint`, `long`, `ulong` | All-zero vector |
| `Vector128<T>.AllBitsSet`, `Vector256<T>.AllBitsSet`, `Vector512<T>.AllBitsSet` | `T = byte`, `int`, `uint`, `long`, `ulong` | All-one vector |
| `Vector128.Create`, `Vector256.Create` | One `ulong`, or respectively two/four `ulong` arguments | Broadcast one value, or construct the individual lanes |
| `Vector128.CreateScalar`, `Vector256.CreateScalar` | One `ulong` or one `uint` | Put the value in the low lane and zero the remaining bits |
| `Vector128.CreateScalarUnsafe` (128-bit only) | One `ulong` | Put the value in the low lane; the upper lane is unspecified, and only `GetElement(0)`, `As*` and the AVX2 shift counts may read the result (see [SOUNDNESS](SOUNDNESS-RUNTIME.md#runtime-assumptions)) |
| `Vector512.Create` (512-bit only) | Two `V256<ulong>` | Concatenate, first operand in the low half |
| `Vector128.ShiftRightArithmetic`, `Vector256.ShiftRightArithmetic` | Vector of `long` and `int` count | Signed 64-bit lane shifts; count modulo 64 |
| `Vector128.ExtractMostSignificantBits<ulong>`, `Vector256.ExtractMostSignificantBits<ulong>` | Vector of `ulong` | Return a `uint` containing the two/four lane sign bits |
| `Vector128.Sum<ulong>`, `Vector256.Sum<ulong>` | Vector of `ulong` | Wrapping sum of the 64-bit lanes |
| `AsByte`, `AsUInt32`, `AsInt64`, `AsDouble`, `AsUInt64`, `AsInt32`, `AsSingle` on `Vector128` / `Vector256` | Source element type is `ulong`, `byte`, `uint`, `long`, `int` or `float`; target is the named type | Preserve the bit pattern. The extractor does not currently accept `double` as a source for these casts |

No other element types or operators are implied. In particular, portable vector multiplication is present as a Lean operation but has no generic vector-operator mapping in the extractor. There is no Vector64 support, Vector512 is limited to bitwise/equality operators, the rows naming it and to `ldobj`/`stobj`/`initobj` of `V512<ulong>`, and there is no general vector load/store API coverage. The specific vector `ldobj`/`stobj` cases are documented in the [opcode table](OPCODES.md).

## SSE

| Exact API | Arguments → result | Required feature | Model |
| --- | --- | --- | --- |
| `Sse2.ShiftLeftLogical128BitLane` | `V128<ulong>, byte` → `V128<ulong>` | `Sse2` | Shift the whole vector left by a byte count, zero-filling; counts ≥16 yield zero |
| `Ssse3.AlignRight` | `V128<byte>, V128<byte>, byte` → `V128<byte>` | `Ssse3` | Extract a 16-byte window from the concatenation, with the second operand as the low half; out-of-range bits are zero |

SSE4.1 and SSE4.2 capability getters are recognised, but their instruction APIs have no mappings. There is no blanket SSE/SSE2 arithmetic, comparison or load/store support.

## AVX

All rows require the `Avx` feature.

| Exact API | Arguments → result | Model |
| --- | --- | --- |
| `Avx.MoveMask` | `V256<double>` → `int` | Collect the four 64-bit lane sign bits |
| `Avx.MoveMask` | `V256<float>` → `int` | Collect the eight 32-bit lane sign bits |
| `Avx.Blend` | `V256<float>, V256<float>, byte` → `V256<float>` | Select each 32-bit lane from the first or second vector using its control bit |
| `Avx.TestZ` | `V256<ulong>, V256<ulong>` → `bool` | Test whether the bitwise intersection is zero |

The float/double overloads above operate on bits; floating-point addition, comparisons, rounding and exceptions are not modelled.

## AVX2

All rows require `Avx2` and operate on 256-bit vectors.

| Exact API | Arguments → result | Model |
| --- | --- | --- |
| `Avx2.Permute4x64` | `V256<ulong>, byte` → `V256<ulong>` | Four 2-bit selectors choose the output lanes |
| `Avx2.Blend` | Two `V256<uint>` or two `V256<int>`, then `byte` → matching vector type | Select each 32-bit lane using a control bit |
| `Avx2.Add` | `V256<ulong>, V256<ulong>` → `V256<ulong>` | Wrapping lane addition |
| `Avx2.CompareEqual` | `V256<ulong>, V256<ulong>` → `V256<ulong>` | Per-lane all-one/zero equality masks |
| `Avx2.CompareGreaterThan` | `V256<long>, V256<long>` → `V256<long>` | Signed per-lane greater-than masks |
| `Avx2.Multiply` | `V256<uint>, V256<uint>` → `V256<ulong>` | Multiply unsigned 32-bit lanes 0, 2, 4 and 6 into four 64-bit products |
| `Avx2.ShiftLeftLogical`, `Avx2.ShiftRightLogical` | `V256<ulong>, byte` → `V256<ulong>` | Logical shifts of each 64-bit lane; counts ≥64 yield zero |
| `Avx2.ShiftLeftLogical`, `Avx2.ShiftRightLogical` | `V256<ulong>, V128<ulong>` -> `V256<ulong>` | Shift each lane by the count's lane 0; counts of 64 or more yield zero; the upper count lane is ignored |
| `Avx2.And`, `Avx2.Or`, `Avx2.Xor`, `Avx2.AndNot` | `V256<ulong>, V256<ulong>` -> `V256<ulong>` | Bitwise operations; `AndNot(a, b)` is `~a & b` |

These are the exact widths and overloads admitted. For example, accepting `Add` on `ulong` vectors does not enable `Add` on byte or 32-bit lanes.

## AVX512

The AVX512 operations use **256-bit operands**, including the VL APIs, except the last two rows, which take `V512<ulong>`.

| Exact API | Arguments → result | Required feature | Model |
| --- | --- | --- | --- |
| `Avx512F.VL.AlignRight64` | Two `V256<ulong>`, then `byte` → `V256<ulong>` | `Avx512FVL` | Extract four lanes from the concatenation, second operand low; control modulo four |
| `Avx512F.VL.TernaryLogic` | Three `V256<ulong>`, then `byte` → `V256<ulong>` | `Avx512FVL` | Per-bit 3-input truth table; control index is `4*a + 2*b + c` |
| `Avx512F.VL.CompareLessThan` | Two `V256<ulong>` → `V256<ulong>` | `Avx512FVL` | Unsigned per-lane less-than masks |
| `Avx512F.VL.CompareGreaterThan` | Two `V256<ulong>` → `V256<ulong>` | `Avx512FVL` | Unsigned per-lane greater-than masks |
| `Avx512F.VL.CompareGreaterThanOrEqual` | Two `V256<ulong>` → `V256<ulong>` | `Avx512FVL` | Unsigned per-lane greater-than-or-equal masks |
| `Avx512DQ.MoveMask` | `V256<ulong>` → `int` | `Avx512DQ` | Collect the four 64-bit lane sign bits |
| `Avx512DQ.VL.MultiplyLow` | Two `V256<ulong>` → `V256<ulong>` | `Avx512DQVL` | Low 64 bits of each lane product |
| `Avx512F.CompareLessThan`, `Avx512F.CompareGreaterThan` | Two `V512<ulong>` -> `V512<ulong>` | `Avx512F` | Unsigned per-lane masks over eight lanes |
| `Avx512DQ.MoveMask` | `V512<ulong>` -> `int` | `Avx512DQ` | Collect the eight 64-bit lane sign bits |

The built-in `x64-v4` profile enables F, DQ and both VL forms together.

## BMI

These operations use scalar integer operands, not vectors.

| Exact API | Arguments → result | Required feature | Model |
| --- | --- | --- | --- |
| `Bmi1.BitFieldExtract` | `uint, byte start, byte length` → `uint` | `Bmi1` | Extract a bit field; start ≥32 yields zero, length is clipped to the remaining bits |
| `Bmi2.X64.MultiplyNoFlags` | `ulong, ulong` → `ulong` | `Bmi2` | Return the high 64 bits of the unsigned 128-bit product |

The pointer-output `MultiplyNoFlags` overload is not mapped. The .NET 10 CoreCLR profile validator requires BMI1, BMI2 and AVX2 to agree.

## X86Base

| Exact API | Arguments → result | Required feature | Model |
| --- | --- | --- | --- |
| `X86Base.X64.DivRem` | `ulong lower, ulong upper, ulong divisor` → `ValueTuple<ulong, ulong>` | `X86Base64` | Divide `upper * 2^64 + lower` by `divisor`; Item1 (`Quotient`) is the quotient and Item2 (`Remainder`) the remainder |

The precondition is `upper < divisor`, so the quotient fits in 64 bits. Otherwise the instruction raises #DE, and the checked interpreter fails with a located arithmetic fault, never a wrapped result: `.divideByZero` for a zero divisor and `.overflow` for any other `upper >= divisor`, matching CoreCLR's `DivideByZeroException` and `OverflowException`. `CIL.Safety.divRem_fields` proves that Item1 and Item2 of a successful call are the `Nat` quotient and remainder, and `CIL.Safety.divRem_fault` that every input violating the precondition faults. The result is a 16-byte aggregate with Item1 at offset 0 and Item2 at offset 8; extraction requires the recomputed `ValueTuple<ulong, ulong>` layout to match it. The 32-bit `X86Base.DivRem` and the signed overloads are not mapped. The API is marked experimental (`SYSLIB5004`) in .NET 10, and only this exact signature is recognised.

## ARM

| Exact API | Arguments → result | Required feature | Model |
| --- | --- | --- | --- |
| `AdvSimd.ExtractVector128` | `V128<ulong>, V128<ulong>, byte index` → `V128<ulong>` | `AdvSimd` | Extract two 64-bit lanes from the concatenation, first operand low. Only indices 0 and 1 are admitted |
| `ArmBase.Arm64.MultiplyHigh` | `ulong, ulong` → `ulong` | `ArmBase64` | High 64 bits of the unsigned 128-bit product |

No other AdvSimd operations, signed `MultiplyHigh` overload or ARM ISA family is mapped. Portable Vector128 operations can still be used under an ARM profile when their signatures match the first table.

## Feature getters, profiles and execution restrictions

Recognised `IsSupported` getters are `X86Base.X64`, `Sse2`, `Ssse3`, `Sse41`, `Sse42`, `Avx`, `Avx2`, `Avx512F`, `Avx512F.VL`, `Avx512DQ`, `Avx512DQ.VL`, `Bmi1`, `Bmi2.X64`, `AdvSimd` and `ArmBase.Arm64`. `Vector128.IsHardwareAccelerated` and `Vector256.IsHardwareAccelerated` are also recognised. The getter result comes from the chosen profile, not the host CPU. Other getters are rejected.

| Built-in profile | Enabled capabilities |
| --- | --- |
| `scalar` | No hardware feature flags |
| `x64-sse2` | `X86Base64`, `Sse2`, `Vector128Accelerated` |
| `x64-sse42` | The above plus `Ssse3`, `Sse41`, `Sse42` |
| `x64-v3` | The above plus `Avx`, `Avx2`, `Bmi1`, `Bmi2`, `Vector256Accelerated` |
| `x64-v4` | The above plus `Avx512F`, `Avx512FVL`, `Avx512DQ`, `Avx512DQVL` |
| `arm64-advsimd` | `ArmBase64`, `AdvSimd`, `Vector128Accelerated` |

Profiles target .NET 10 CoreCLR. Both the extractor and Lean certificate reject capability sets that split its runtime groups. Custom profiles must supply every field and satisfy the same constraints. A v3/v4 custom profile may disable `vector256Accelerated` for a runtime configured with `PreferredVectorBitWidth=128`; it cannot enable it without AVX2.

See [runtime-profile evidence and migration](RUNTIME-PROFILES.md) for measured x64/arm64 versions, retired names and consumer migration. Changing a profile requires fresh extraction and proof verification; old certificates do not acquire the new capabilities.

Pass the profile after the extraction output directory, for example:

```sh
leancil extract MyAssembly.dll "Operations::Method(ulong)" artifacts/Method x64-v3
```

A reachable ISA-specific intrinsic whose required flag is false is rejected. Profile-based reachability can exclude a branch; excluded instructions remain explicit unsupported placeholders, and changing profiles invalidates the artifacts.

Byte controls are consumed by the Lean evaluator as `i32` values in 0–255; other shapes or values fail. ARM extraction and vector element access impose the narrower bounds stated above. The model does not establish JIT immediate-operand lowering or physical CPU behaviour; those are part of the [runtime correspondence assumptions](SOUNDNESS.md). Supporting a vector type in metadata alone does not support every operation on it.

## Source and validation boundary

The extraction inventory comes from [RuntimeModels.cs](../Extractor/RuntimeModels.cs) and [FeatureProfiles.cs](../Extractor/FeatureProfiles.cs). Operand checks and operation evaluation are defined in [Intrinsics.lean](../CIL/SIMD/Intrinsics.lean), with bit-level functions in the [SIMD modules](../CIL/SIMD).

Additional Lean definitions, such as portable vector multiplication, do not automatically add extractor mappings. These tables describe implemented support, not exhaustive testing of every overload or universal correctness of user methods. See [validation results](VALIDATION.md) for the tests run and the [opcode table](OPCODES.md) for non-intrinsic CIL support.

`initobj` for the exact `Vector128<UInt64>`, `Vector256<UInt64>`, and
`Vector512<UInt64>` runtime types clears 16, 32, and 64 bytes respectively. The
translation certificate binds the raw opcode, full type identities, and byte
width. These ordinary memory writes need no SIMD ISA capability and require a
valid modeled profile. They retain ordinary write bounds and access checks.
This support does not add vector512 field layouts or verify CoreCLR behavior.
