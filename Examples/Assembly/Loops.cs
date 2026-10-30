using System;

namespace Examples;

public static class Loops
{
    public static bool AllZero(ReadOnlySpan<uint> values)
    {
        while (values.Length != 0)
        {
            if (values[0] != 0) return false;
            values = values.Slice(1);
        }
        return true;
    }

    public static ulong Sum(ReadOnlySpan<ulong> values)
    {
        ulong total = 0;
        while (values.Length != 0)
        {
            total = unchecked(total + values[0]);
            values = values.Slice(1);
        }
        return total;
    }

    public static int Drain(ReadOnlySpan<int> values)
    {
        while (values.Length != 0)
            values = values.Slice(1);
        return values.Length;
    }

    public static uint Countdown(uint value)
    {
        uint remaining = value;
        while (remaining != 0)
            remaining = unchecked(remaining - 1);
        return remaining;
    }

    public static uint WrongCountdown(uint value)
    {
        uint remaining = value;
        while (remaining > 1)
            remaining = unchecked(remaining - 1);
        return remaining;
    }

    public static uint FeatureCountdown(uint value)
    {
        uint remaining = value;
        while (remaining != 0)
        {
            if (System.Runtime.Intrinsics.X86.Avx2.IsSupported)
                return (uint)new float[remaining].Length;
            remaining = unchecked(remaining - 1);
        }
        return remaining;
    }

    public static uint Decrement(uint value) => unchecked(value - 1);

    public static void FillWords(ref ulong destination, ulong value, int count)
    {
        for (int i = 0; i < count; i++)
            System.Runtime.CompilerServices.Unsafe.Add(ref destination, i) = value;
    }

    public static uint CountCalls(uint value)
    {
        uint remaining = value;
        uint count = 0;
        while (remaining != 0)
        {
            remaining = Decrement(remaining);
            count = unchecked(count + 1);
        }
        return count;
    }

    public static uint Bump(uint count, uint limit) =>
        count == limit ? throw new InvalidOperationException() : unchecked(count + 1);

    // Returns its input when it is at most limit; otherwise Bump throws after limit iterations.
    public static uint CountUntil(uint value, uint limit)
    {
        uint remaining = value;
        uint count = 0;
        while (remaining != 0)
        {
            count = Bump(count, limit);
            remaining = unchecked(remaining - 1);
        }
        return count;
    }
}
