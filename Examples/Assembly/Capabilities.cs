using System;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
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
