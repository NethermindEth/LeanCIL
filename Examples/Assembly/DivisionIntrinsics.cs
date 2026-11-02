using System;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;
using ArmAes = System.Runtime.Intrinsics.Arm.Aes;
using X86Aes = System.Runtime.Intrinsics.X86.Aes;

namespace Examples;

public static class DivisionIntrinsics
{
    public static ulong DefinedLocal(ulong value)
    {
        var local = Vector128.Create(value);
        return local.GetElement(0) + local.GetElement(1);
    }
    public static ulong PrunedUnsafeLocal(ulong value)
    {
        var local = Avx2.IsSupported ? Vector128.CreateScalarUnsafe(value) : Vector128.Create(value);
        return local.GetElement(0) + local.GetElement(1);
    }
    public static ulong And(ulong left, ulong right) => Avx2.And(Vector256.Create(left), Vector256.Create(right)).GetElement(0);
    public static ulong Or(ulong left, ulong right) => Avx2.Or(Vector256.Create(left), Vector256.Create(right)).GetElement(1);
    public static ulong Xor(ulong left, ulong right) => Avx2.Xor(Vector256.Create(left), Vector256.Create(right)).GetElement(2);
    public static ulong AndNot(ulong left, ulong right) => Avx2.AndNot(Vector256.Create(left), Vector256.Create(right)).GetElement(3);
    public static ulong ShiftLeft(ulong value, ulong count)
    {
        Vector128<ulong> local = Vector128.CreateScalarUnsafe(count);
        return Avx2.ShiftLeftLogical(Vector256.Create(value), local).GetElement(0);
    }
    public static ulong ShiftRight(ulong value, ulong count)
    {
        Vector128<ulong> local = Vector128.CreateScalarUnsafe(count);
        return Avx2.ShiftRightLogical(Vector256.Create(value), local).GetElement(3);
    }
    public static int Less(ulong left, ulong right)
    {
        Vector512<ulong> first = Vector512.Create(Vector256.Create(left), Vector256.Create(left));
        Vector512<ulong> second = Vector512.Create(Vector256.Create(right), Vector256.Create(right));
        return Avx512DQ.MoveMask(Avx512F.CompareLessThan(first, second));
    }
    public static int Greater(ulong left, ulong right)
    {
        Vector512<ulong> first = Vector512.Create(Vector256.Create(left), Vector256.Create(left));
        Vector512<ulong> second = Vector512.Create(Vector256.Create(right), Vector256.Create(right));
        return Avx512DQ.MoveMask(Avx512F.CompareGreaterThan(first, second));
    }
    public static ulong UnsafeLow(ulong value) => Vector128.CreateScalarUnsafe(value).GetElement(0);
    public static Vector128<ulong> UnsafeReturn(ulong value) => Vector128.CreateScalarUnsafe(value);
    public static ulong UnsafeCall(ulong value) => ReadLow(Vector128.CreateScalarUnsafe(value));
    private static ulong ReadLow(Vector128<ulong> value) => value.GetElement(0);
    public static void UnsafeStore(ref Vector128<ulong> destination, ulong value) =>
        destination = Vector128.CreateScalarUnsafe(value);
    public static ulong UnsafeHigh(ulong value) => Vector128.CreateScalarUnsafe(value).GetElement(1);
    public static bool UnsafeEquals(ulong value) => Vector128.CreateScalarUnsafe(value) == Vector128.CreateScalarUnsafe(value);
    public static void Init128(ref Vector128<ulong> value) => value = default;
    public static void Init256(ref Vector256<ulong> value) => value = default;
    public static void Init512(ref Vector512<ulong> value) => value = default;
    public static Vector256<byte> Shuffle256(ReadOnlySpan<byte> source, ReadOnlySpan<byte> control) =>
        Avx2.Shuffle(Vector256.Create(source), Vector256.Create(control));
    public static Vector128<byte> Shuffle128(ReadOnlySpan<byte> source, ReadOnlySpan<byte> control) =>
        Ssse3.Shuffle(Vector128.Create(source), Vector128.Create(control));
    // The int256 and Nethermind hash round: x86 AESENC, else ARM64 AESE with a zero key, AESMC and the key.
    public static Vector128<byte> AesRound(ulong state0, ulong state1, ulong key0, ulong key1)
    {
        Vector128<byte> state = Vector128.Create(state0, state1).AsByte();
        Vector128<byte> roundKey = Vector128.Create(key0, key1).AsByte();
        return X86Aes.IsSupported
            ? X86Aes.Encrypt(state, roundKey)
            : ArmAes.MixColumns(ArmAes.Encrypt(state, Vector128<byte>.Zero)) ^ roundKey;
    }
    // The int256 arithmetic shift window: index k takes limb k below 4 and a lane of the sign fill above it.
    public static Vector256<ulong> SignWindow(ulong v0, ulong v1, ulong v2, ulong v3,
        ulong index0, ulong index1, ulong index2, ulong index3)
    {
        Vector256<ulong> value = Vector256.Create(v0, v1, v2, v3);
        Vector256<long> negative = Vector256.LessThan(value.AsInt64(), Vector256<long>.Zero);
        Vector256<ulong> fill = Avx2.Permute4x64(negative.AsUInt64(), 0xFF);
        return Avx512F.VL.PermuteVar4x64x2(value, Vector256.Create(index0, index1, index2, index3), fill);
    }
    public static Vector256<uint> CreateWords(uint r0, uint r1, uint r2, uint r3,
        uint r4, uint r5, uint r6, uint r7) => Vector256.Create(r0, r1, r2, r3, r4, r5, r6, r7);
    // The int256 ARM64 big-endian limb reversal of one 16-byte half.
    public static Vector128<ulong> ReverseLimbs(ulong low, ulong high) =>
        AdvSimd.ReverseElement8(Vector128.Create(low, high));
    // The int256 ARM64 read and write: each 16-byte half moves whole, the second at byte offset 16.
    public static void SwapHalves(ReadOnlySpan<byte> source, Span<byte> destination)
    {
        ref byte from = ref MemoryMarshal.GetReference(source);
        ref byte to = ref MemoryMarshal.GetReference(destination);
        Vector128<byte> lower = Vector128.LoadUnsafe(ref from);
        Vector128<byte> upper = Vector128.LoadUnsafe(ref from, 16);
        upper.StoreUnsafe(ref to);
        lower.StoreUnsafe(ref to, 16);
    }
}
