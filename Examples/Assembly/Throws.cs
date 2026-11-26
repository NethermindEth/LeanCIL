using System;
using System.Diagnostics.CodeAnalysis;

namespace Examples;

public static class Throws
{
    public static uint Null(uint value)
    {
        if (value == 0) ThrowNull();
        return value;
    }

    [DoesNotReturn]
    static void ThrowNull() => throw null!;

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

    public static uint Message(uint value) => value == 0 ? value :
        throw new InvalidOperationException("invalid value");

    public static uint NamedArgument(uint value) => value == 0 ? value :
        throw new ArgumentException("invalid value", nameof(value));

    public static uint ArgumentInner(uint value) => value == 0 ? value :
        throw new ArgumentException("invalid value", nameof(value), null);

    public static uint ActualValue(uint value) => value == 0 ? value :
        throw new ArgumentOutOfRangeException(nameof(value), null, "invalid value");

    [DoesNotReturn]
    static void ThrowDivideByZero() => throw new DivideByZeroException();

    // Input 1 is caught and returns 1, input 2 escapes the unrelated catch, and any other input returns 0;
    // the finally counts each call once in counts[0], including the one that escapes.
    public static uint Guarded(uint value, uint[] counts, FaultSlot slot)
    {
        slot.Error = new InvalidOperationException("invalid value", (Exception?)null);
        try
        {
            try
            {
                if (value == 1) throw slot.Error;
            }
            catch (InvalidOperationException)
            {
                return 1;
            }
            try
            {
                if (value == 2) throw slot.Error;
            }
            catch (ArgumentException)
            {
                return 3;
            }
        }
        finally
        {
            counts[0]++;
        }
        return 0;
    }
}

/// <summary>Holds the one exception <see cref="Throws.Guarded"/> raises from both of its throw sites.</summary>
public sealed class FaultSlot
{
    public Exception? Error;
}
