using System;
using System.Buffers.Binary;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

public static class SpanReferences
{
    /// <summary>Four limbs read from a readonly span reference.</summary>
    public readonly struct Limbs
    {
        public readonly ulong U0, U1, U2, U3;

        public Limbs(in ReadOnlySpan<ulong> data, bool reversed)
        {
            if (reversed)
            {
                U3 = data[0];
                U2 = data[1];
                U1 = data[2];
                U0 = data[3];
            }
            else
            {
                U0 = data[0];
                U1 = data[1];
                U2 = data[2];
                U3 = data[3];
            }
        }
    }

    /// <summary>A two-word aggregate span element.</summary>
    [StructLayout(LayoutKind.Sequential)]
    public struct Pair
    {
        public ulong Low;
        public ulong High;
    }

    public static ulong High(in Span<Pair> values, int index) => values[index].High;

    public static ulong ReadOnlyHigh(in ReadOnlySpan<Pair> values, int index) => values[index].High;

    public static ulong HighAddress(in ReadOnlySpan<Pair> values, int index)
    {
        ref readonly var high = ref values[index].High;
        return high;
    }

    public static ulong Word(in ReadOnlySpan<ulong> values) => MemoryMarshal.GetReference(values);

    public static ulong BigEndianWord(in ReadOnlySpan<byte> values) =>
        BinaryPrimitives.ReverseEndianness(Unsafe.ReadUnaligned<ulong>(ref MemoryMarshal.GetReference(values)));

    public static ulong FirstHigh(in ReadOnlySpan<Pair> values) => MemoryMarshal.GetReference(values).High;

    // Faults: a reference from a readonly view grants no write permission.
    public static void WriteWord(in ReadOnlySpan<ulong> values, ulong value) =>
        MemoryMarshal.GetReference(values) = value;

    // Faults: the field store needs write permission the readonly view never granted.
    public static void SetHigh(in ReadOnlySpan<Pair> values, ulong value) =>
        MemoryMarshal.GetReference(values).High = value;

    public static int Sum(in ReadOnlySpan<byte> values)
    {
        var total = 0;
        for (var index = 0; index < values.Length; index++) total += values[index];
        return total;
    }

    public static int Length(ref readonly ReadOnlySpan<int> values) => values.Length;

    public static int First(in Span<int> values) => values[0];

    public static void WriteFirst(in Span<int> values, int value) => values[0] = value;

    public static int Forward(in ReadOnlySpan<byte> values) => Sum(in values);

    public static int Tail(in ReadOnlySpan<byte> values) => Sum(values.Slice(1));

    public static int Copy(in ReadOnlySpan<byte> values)
    {
        var copy = values;
        return copy.Length;
    }

    public static byte At(in ReadOnlySpan<byte> values, int index) => values[index];

    public static int Caller(byte[] data)
    {
        ReadOnlySpan<byte> values = data;
        return Sum(in values);
    }

    public static int Argument(ReadOnlySpan<byte> values) => Sum(in values);

    public static int Temporary(ReadOnlySpan<byte> values) => Sum(values.Slice(1));

    // Rejected: a span reference return could outlive the caller's span home.
    public static ref Span<int> Alias(ref Span<int> values) => ref values;

    // Rejected: the callee replaces the caller's span.
    public static void Replace(out Span<int> values) => values = default;

    public static ulong Construct(ReadOnlySpan<ulong> data)
    {
        var limbs = new Limbs(in data, false);
        return limbs.U0 + limbs.U3;
    }
}
