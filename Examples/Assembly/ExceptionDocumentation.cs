using System;
using System.Runtime.Intrinsics.X86;

namespace Examples;

public static class ExceptionDocumentation
{
    /// <exception cref="DivideByZeroException">The divisor is zero.</exception>
    /// <exception cref="OverflowException">The signed division overflows.</exception>
    public static long Divide(long value, long divisor) => value / divisor;

    /// <exception cref="DivideByZeroException">The divisor is zero.</exception>
    public static ulong UnsignedDivide(ulong value, ulong divisor) => value / divisor;

    /// <exception cref="OverflowException">The signed value has no positive counterpart.</exception>
    public static int Absolute(int value) => Math.Abs(value);

    /// <exception cref="ArgumentException">The lower bound is greater than the upper bound.</exception>
    public static int Clamp(int value, int lower, int upper) => Math.Clamp(value, lower, upper);

    /// <exception cref="ArgumentOutOfRangeException">An AVX2 path rejects the value.</exception>
    public static uint Profile(uint value)
    {
        if (Avx2.IsSupported) throw new ArgumentOutOfRangeException(nameof(value));
        return value;
    }

    /// <summary>Updates the referenced word.</summary>
    public static void Reference(ref ulong value) => value++;
}
