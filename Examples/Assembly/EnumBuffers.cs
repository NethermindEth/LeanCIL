using System;

namespace Examples;

public static class EnumBuffers
{
    public enum Small : sbyte { Minus = -1, Seven = 7 }
    public enum OtherSmall : sbyte { Seven = 7 }
    public enum Large : ulong { High = 0x8000000000000001 }

    public static Small Roundtrip(Small[] values, int index, Small value)
    {
        values[index] = value;
        return values[index];
    }

    public static Large Wide(Large[] values, int index) => values[index];

    public static Small Address(Small[] values, int index, Small value)
    {
        ref var slot = ref values[index];
        slot = value;
        return slot;
    }

    public static Small SpanRoundtrip(Small[] values, int start, Small value)
    {
        var span = values.AsSpan(start);
        span[0] = value;
        ReadOnlySpan<Small> readOnly = span;
        return Read(readOnly.Slice(0, 1));
    }

    public static Small Read(ReadOnlySpan<Small> values) => values[0];

    public static Span<Small> Slice(Span<Small> values, int start) => values.Slice(start);

    public static Small Loop(Small[] values, int count)
    {
        var span = values.AsSpan();
        for (var index = 0; index < count; index++) span[index] = Small.Seven;
        return span[count - 1];
    }
}
