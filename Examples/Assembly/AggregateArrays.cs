using System;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;

namespace Examples;

internal static class AggregateArrays
{
    [StructLayout(LayoutKind.Sequential)]
    public struct Pair
    {
        public ulong First;
        public ulong Second;
    }

    public static Pair Read(Pair[] source, int index) => source[index];
    public static void Write(Pair[] target, int index, Pair value) => target[index] = value;
    public static ref Pair Address(Pair[] source, int index) => ref source[index];
    public static ref Pair Data(Pair[] source) => ref MemoryMarshal.GetArrayDataReference(source);
    public static Span<Pair> View(Pair[] source) => source;
    public static ReadOnlySpan<Pair> ReadOnlyView(Pair[] source) => source;
    public static Span<Pair> Slice(Pair[] source, int start, int length) => source.AsSpan(start, length);
    public static int ConstructedLength(Pair[] source, int start, int length)
    {
        var span = new Span<Pair>(source, start, length);
        return span.Length;
    }
    public static Vector128<ulong> ReadVector(Vector128<ulong>[] source, int index) => source[index];
    public static void WriteVector(Vector128<ulong>[] target, int index, Vector128<ulong> value) =>
        target[index] = value;
    public static Span<Vector128<ulong>> VectorView(Vector128<ulong>[] source) => source;
}
