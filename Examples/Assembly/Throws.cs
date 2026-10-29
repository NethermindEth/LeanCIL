using System;
using System.Diagnostics.CodeAnalysis;

namespace Examples;

public static class Throws
{
    // A zero divisor raises from the helper, before `div` could fault.
    public static uint Quotient(uint value, uint divisor)
    {
        if (divisor == 0) ThrowDivideByZero();
        return value / divisor;
    }

    public static uint Percent(uint value) =>
        value <= 100 ? value : throw new ArgumentOutOfRangeException(nameof(value), "must not exceed 100");

    public static uint Inner(uint value) => value == 0 ? value :
        throw new InvalidOperationException("invalid value", (Exception?)null);

    public static uint ArgumentInner(uint value) => value == 0 ? value :
        throw new ArgumentException("invalid value", nameof(value), null);

    public static uint ActualValue(uint value) => value == 0 ? value :
        throw new ArgumentOutOfRangeException(nameof(value), null, "invalid value");

    [DoesNotReturn]
    static void ThrowDivideByZero() => throw new DivideByZeroException();
}
