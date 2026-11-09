using System;

namespace Examples;

/// <summary>
/// Framework argument guards: each throws its named exception exactly when its .NET 10 condition holds, and the
/// parameter name the compiler passes is an opaque string.
/// </summary>
public static class Guards
{
    /// <summary>The count, which must not be negative.</summary>
    public static int Count(int count)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(count);
        return count;
    }

    /// <summary>The index, which must be below <paramref name="length"/>.</summary>
    public static uint Index(uint index, uint length)
    {
        ArgumentOutOfRangeException.ThrowIfGreaterThanOrEqual(index, length);
        return index;
    }

    /// <summary>The label, which must not be null.</summary>
    public static string Required(string? label)
    {
        ArgumentNullException.ThrowIfNull(label);
        return label;
    }
}
