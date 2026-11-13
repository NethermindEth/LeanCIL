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

    struct Tally
    {
        public uint Count;
        public uint Sum;
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    static uint AddTwo(uint value) => unchecked(value + 2);

    // Counts to value in a struct local, adding two per iteration through a helper.
    public static uint TallyTwice(uint value)
    {
        Tally tally = default;
        while (tally.Count != value)
        {
            tally.Sum = AddTwo(tally.Sum);
            tally.Count = unchecked(tally.Count + 1);
        }
        return tally.Sum;
    }

    struct Scan
    {
        public uint Count;
        public bool Stopped;
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    static void Stamp(ref uint slot, uint value) => slot = value;

    // Copies the words before the first zero to output; returns the count, with bit 31 set if a zero ended the copy.
    public static uint CopyUntilZero(ReadOnlySpan<uint> values, ref uint output)
    {
        Scan scan = default;
        while (values.Length != 0)
        {
            uint value = values[0];
            if (value == 0)
            {
                scan.Stopped = true;
                break;
            }
            Stamp(ref System.Runtime.CompilerServices.Unsafe.Add(ref output, (int)scan.Count), value);
            scan.Count = unchecked(scan.Count + 1);
            values = values.Slice(1);
        }
        return scan.Stopped ? scan.Count | 0x80000000u : scan.Count;
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

    // Counts its input down to zero, then a second loop counts back up to it.
    public static uint DownThenUp(uint value)
    {
        uint remaining = value;
        while (remaining != 0)
            remaining = unchecked(remaining - 1);
        uint climbed = 0;
        while (climbed != value)
            climbed = unchecked(climbed + 1);
        return climbed;
    }

    // Writes every element through the span, which need not have been readable before.
    public static void Fill(Span<uint> target, uint value)
    {
        while (target.Length != 0)
        {
            target[0] = value;
            target = target.Slice(1);
        }
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    static void Put(Span<uint> target, uint value) => target[0] = value;

    // Fills the span through a helper that writes only the first element of the span it is passed.
    public static void FillThrough(Span<uint> target, uint value)
    {
        while (target.Length != 0)
        {
            Put(target, value);
            target = target.Slice(1);
        }
    }

    // Adds the array's elements by index; the bound test reads the array's length each iteration.
    public static ulong SumIndexed(ulong[] values)
    {
        ulong total = 0;
        for (var index = 0; index < values.Length; index++) total = unchecked(total + values[index]);
        return total;
    }

    // Stores the value into every element of the array by index.
    public static void FillIndexed(uint[] values, uint value)
    {
        for (var index = 0; index < values.Length; index++) values[index] = value;
    }

    // Adds the array's elements through a span local that drops each element it has read.
    public static ulong SumThroughSpan(ulong[] values)
    {
        ReadOnlySpan<ulong> rest = values;
        ulong total = 0;
        while (rest.Length != 0)
        {
            total = unchecked(total + rest[0]);
            rest = rest.Slice(1);
        }
        return total;
    }

    // Adds a span's elements through a local copy of it.
    public static ulong SumThroughLocal(ReadOnlySpan<ulong> values)
    {
        var rest = values;
        ulong total = 0;
        while (rest.Length != 0)
        {
            total = unchecked(total + rest[0]);
            rest = rest.Slice(1);
        }
        return total;
    }

    // Stores the value into every element of the array through a span local over it.
    public static void FillThroughSpan(uint[] values, uint value)
    {
        Span<uint> rest = values;
        while (rest.Length != 0)
        {
            rest[0] = value;
            rest = rest.Slice(1);
        }
    }

    // Struct names that sort in the opposite order to the locals that hold them, so layout numbers follow
    // the order the extraction emits them, not the order of their identities.
    struct Zulu
    {
        public uint Count;
        public uint Spare;
    }

    struct Alpha
    {
        public ulong Sum;
    }

    public static ulong TwoStructs(uint value)
    {
        Zulu zulu = default;
        Alpha alpha = default;
        while (zulu.Count != value)
        {
            zulu.Count = unchecked(zulu.Count + 1);
            alpha.Sum = unchecked(alpha.Sum + 2);
        }
        return alpha.Sum;
    }

    public struct Inner
    {
        public uint Count;
    }

    public struct Outer
    {
        public Inner Part;
        public uint Other;
    }

    // `outer` is named first in the extraction, and `Inner` nests in it, so the two orders of layouts disagree.
    public static uint InnerCount(Outer outer, uint value)
    {
        Inner inner = default;
        while (inner.Count != value) inner.Count = unchecked(inner.Count + 1);
        return inner.Count;
    }

    // Walks down from the reference: the offset of each store is a negative stride, which no loop step names.
    public static void FillWordsDown(ref ulong destination, ulong value, int count)
    {
        for (int i = 0; i < count; i++)
            System.Runtime.CompilerServices.Unsafe.Subtract(ref destination, i) = value;
    }

    // Loop tests against a small constant: signed and unsigned order, and equality.
    public static int CountToFive(int start)
    {
        var count = start;
        while (count < 5) count = unchecked(count + 1);
        return count;
    }

    public static uint CountUpToFive(uint start)
    {
        var count = start;
        while (count < 5u) count = unchecked(count + 1);
        return count;
    }

    public static uint ReachFive(uint start)
    {
        var count = start;
        while (count != 5) count = unchecked(count + 1);
        return count;
    }
}
