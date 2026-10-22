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

    /// <exception cref="OverflowException">The checked sum overflows.</exception>
    public static long CheckedAdd(long left, long right) => checked(left + right);

    /// <exception cref="OverflowException">The input does not fit a signed 32-bit value.</exception>
    public static int CheckedNarrow(long value) => checked((int)value);

    /// <exception cref="IndexOutOfRangeException">The index is outside the modeled static span.</exception>
    public static uint SpanItem(int index) => SpanTables.Word(index);

    /// <exception cref="DivideByZeroException">The divisor is zero.</exception>
    /// <exception cref="OverflowException">The quotient does not fit an unsigned 64-bit value.</exception>
    public static ulong DivRem(ulong lower, ulong upper, ulong divisor) => TupleDivision.Quotient(lower, upper, divisor);

    /// <summary>Updates the referenced word.</summary>
    public static void Reference(ref ulong value) => value++;
}
