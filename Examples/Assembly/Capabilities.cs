using System;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

namespace Examples;

public static class Capabilities
{
    public ref struct ReferenceFreeView { public int Value; }

    public static int ReferenceFree()
    {
        if (RuntimeHelpers.IsReferenceOrContainsReferences<int>() ||
            RuntimeHelpers.IsReferenceOrContainsReferences<Signed16>() ||
            RuntimeHelpers.IsReferenceOrContainsReferences<Vector128<int>>() ||
            RuntimeHelpers.IsReferenceOrContainsReferences<EnumRecord>() ||
            RuntimeHelpers.IsReferenceOrContainsReferences<GenericPair<uint>>() ||
            RuntimeHelpers.IsReferenceOrContainsReferences<ReferenceFreeView>())
            return (int)Math.Sqrt(2);
        return 73;
    }

    // Each getter folds to the selected profile's flag.
    public static uint Flags() => (X86Base.X64.IsSupported ? 1u : 0u) | (Vector128.IsHardwareAccelerated ? 2u : 0u);

    // AdvSimd.Arm64 folds with AdvSimd, so the two flags always agree.
    public static uint ArmFlags() => (AdvSimd.Arm64.IsSupported ? 1u : 0u) | (AdvSimd.IsSupported ? 2u : 0u);

    // The ARM64 body is unmodeled: only profiles without AdvSimd prune it.
    public static int ArmCount(ulong value) =>
        AdvSimd.Arm64.IsSupported ? ArmBase.Arm64.LeadingSignCount((long)value) : (int)(value & 1);

    public static bool Crc64() => Crc32.Arm64.IsSupported;

    public static bool Rdm64() => Rdm.Arm64.IsSupported;

    // Avx512Vbmi.VL folds with Avx512Vbmi, so the two flags always agree.
    public static uint VbmiFlags() => (Avx512Vbmi.VL.IsSupported ? 1u : 0u) | (Avx512Vbmi.IsSupported ? 2u : 0u);

    // The VBMI body is unmodeled: only profiles without VBMI prune it.
    public static int VbmiCount(ulong value) => Avx512Vbmi.VL.IsSupported
        ? Avx512Vbmi.VL.PermuteVar32x8(Vector256<byte>.Zero, Vector256<byte>.Zero).GetElement(0)
        : (int)(value & 1);

    public static bool Vbmi2() => Avx512Vbmi2.VL.IsSupported;

    // Valid profiles are little-endian, so the big-endian branch is pruned.
    public static int Endian() => BitConverter.IsLittleEndian ? 1 : (int)Math.Sqrt(2);

    public static int Platform()
    {
        if (IntPtr.Size != 8 || UIntPtr.Size != 8 || !Environment.Is64BitProcess)
            return (int)Math.Sqrt(2);
        if (IntPtr.Size <= 4 || UIntPtr.Size > 16)
            return (int)Math.Sqrt(2);
        if (!((IntPtr.Size > 4) & ((uint)UIntPtr.Size < uint.MaxValue)))
            return (int)Math.Sqrt(2);
        switch (IntPtr.Size & 3)
        {
            case 0: break;
            case 1: return 1;
            case 2: return 2;
            default: return (int)Math.Sqrt(2);
        }
        return IntPtr.Size + UIntPtr.Size + (Environment.Is64BitProcess ? 1 : 0);
    }
}
