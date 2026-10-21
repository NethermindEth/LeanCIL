using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Examples;

public static class Capabilities
{
    // Each getter folds to the selected profile's flag.
    public static uint Flags() => (X86Base.X64.IsSupported ? 1u : 0u) | (Vector128.IsHardwareAccelerated ? 2u : 0u);
}
