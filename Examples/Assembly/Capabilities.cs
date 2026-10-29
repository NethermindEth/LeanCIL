using System;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Examples;

public static class Capabilities
{
    // Each getter folds to the selected profile's flag.
    public static uint Flags() => (X86Base.X64.IsSupported ? 1u : 0u) | (Vector128.IsHardwareAccelerated ? 2u : 0u);

    public static int Platform()
    {
        if (!((IntPtr.Size == 8) & (UIntPtr.Size == 8) & Environment.Is64BitProcess))
            return (int)Math.Sqrt(2);
        return IntPtr.Size + UIntPtr.Size + (Environment.Is64BitProcess ? 1 : 0);
    }
}
