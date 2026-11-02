using System;
using System.Buffers.Binary;
using System.Security.Cryptography;

namespace Examples;

// Process-random hash seeds, as in Nethermind.Int256: extraction cannot run their initializer.
public static class SeededHash
{
    private const ulong Multiplier = 0x9E3779B97F4A7C15;

    private static readonly ulong Seed0 = CreateSeed();
    private static readonly ulong Seed1 = CreateSeed();

    private static ulong CreateSeed()
    {
        Span<byte> bytes = stackalloc byte[sizeof(ulong)];
        RandomNumberGenerator.Fill(bytes);
        return BinaryPrimitives.ReadUInt64LittleEndian(bytes);
    }

    public static ulong Hash(ulong value) => unchecked((value ^ Seed0) * Multiplier + Seed1);

    // Both loads observe one fixed value, whatever it is.
    public static ulong Twice() => Seed0 - Seed0;

    private static ulong Read(in ulong value) => value;

    public static ulong ByReference() => Read(in Seed0);
}
