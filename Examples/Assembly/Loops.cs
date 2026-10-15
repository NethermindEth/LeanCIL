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
}
