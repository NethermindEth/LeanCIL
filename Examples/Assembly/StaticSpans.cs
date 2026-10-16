using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

internal static class StaticSpans
{
    // Sixteen bytes keep Roslyn on the explicit-layout RVA blob instead of a primitive-typed field.
    private static ReadOnlySpan<byte> Lookup => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];

    public static byte First() => MemoryMarshal.GetReference(Lookup);
    public static byte Last() => Unsafe.Add(ref MemoryMarshal.GetReference(Lookup), 15);
    public static byte PastEnd() => Unsafe.Add(ref MemoryMarshal.GetReference(Lookup), 16);
    public static void Write() => MemoryMarshal.GetReference(Lookup) = 0;
}
