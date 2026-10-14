using System.Runtime.Intrinsics;

namespace Examples;

internal static class TypedCopy
{
    public static void Packet(ref Packet destination, ref Packet source) => destination = source;
    public static void Record(ref Record destination, ref Record source) => destination = source;
    public static void Vector128(ref Vector128<ulong> destination, ref Vector128<ulong> source) => destination = source;
    public static void Vector256(ref Vector256<ulong> destination, ref Vector256<ulong> source) => destination = source;
}
