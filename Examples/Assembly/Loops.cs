namespace Examples;

public static class Loops
{
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
                return (uint)new int[remaining].Length;
            remaining = unchecked(remaining - 1);
        }
        return remaining;
    }

    public static uint Decrement(uint value) => unchecked(value - 1);

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
}
