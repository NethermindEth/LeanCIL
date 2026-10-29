using System;
using System.Runtime.CompilerServices;

namespace Examples;

public readonly struct StaticPair<T> where T : unmanaged
{
    public readonly T First;
    public readonly ulong Second;

    public StaticPair(T first, ulong second)
    {
        First = first;
        Second = second;
    }
}

// Shaped like UInt256: the static constructor fixes Zero and One through an implicit conversion.
public readonly struct Word256
{
    public readonly ulong U0, U1, U2, U3;

    public Word256(ulong u0, ulong u1, ulong u2, ulong u3)
    {
        U0 = u0;
        U1 = u1;
        U2 = u2;
        U3 = u3;
    }

    public static implicit operator Word256(ulong value) => new(value, 0, 0, 0);

    public static readonly Word256 Zero = 0ul;
    public static readonly Word256 One = 1ul;
    public static readonly Word256 MinValue = Zero;
    public static readonly Word256 MaxValue = new(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
    public static readonly StaticPair<uint> Pair32 = new(7u, 9ul);
    public static readonly StaticPair<ulong> Pair64 = new(11ul, 13ul);
    // Unmodelled code in the same static constructor.
    public static readonly long Seed = Environment.TickCount64;
}

public static class StaticValues
{
    public static Word256 One() => Word256.One;
    public static Word256 Zero() => Word256.Zero;
    public static Word256 Min() => Word256.MinValue;
    public static Word256 Max() => Word256.MaxValue;
    public static StaticPair<uint> Pair32() => Word256.Pair32;
    public static StaticPair<ulong> Pair64() => Word256.Pair64;

    // ExpMod's shape: store a loaded value through an out parameter.
    public static void Select(bool one, out Word256 result)
    {
        if (one) result = Word256.One;
        else result = Word256.Zero;
    }

    public static void Overwrite() => Unsafe.AsRef(in Word256.One) = default;
}
