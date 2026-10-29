using System;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;

namespace Examples;

internal static class AggregateSpans
{
    [StructLayout(LayoutKind.Sequential)]
    public struct Words
    {
        public ulong First;
        public ulong Second;
        public ulong Third;
        public ulong Fourth;
    }

    public static Span<byte> Bytes(Span<Words> source) => MemoryMarshal.AsBytes(source);
    public static ReadOnlySpan<Words> WordsView(ReadOnlySpan<byte> source) =>
        MemoryMarshal.Cast<byte, Words>(source);
    public static Span<byte> VectorBytes(Span<Vector128<ulong>> source) => MemoryMarshal.AsBytes(source);
    public static Vector128<ulong> ReadVector(ReadOnlySpan<Vector128<ulong>> source) => source[0];
    public static Words Read(ReadOnlySpan<Words> source) => source[0];
    public static void Write(Span<Words> target, Words value) => target[0] = value;
    public static void WriteVector(Span<Vector128<ulong>> target, Vector128<ulong> value) => target[0] = value;
    public static bool Copy(ReadOnlySpan<Words> source, Span<Words> target) => source.TryCopyTo(target);
    public static Span<Words> Slice(Span<Words> source, int offset, int length) => source.Slice(offset, length);
    public static void Clear(Span<Words> source) => source.Clear();
}
