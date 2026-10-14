using System.Buffers.Binary;
using System.Numerics;

namespace Examples;

public static class Bits
{
    public static uint Left32(uint value, int count) => BitOperations.RotateLeft(value, count);
    public static ulong Left64(ulong value, int count) => BitOperations.RotateLeft(value, count);
    public static uint Right32(uint value, int count) => BitOperations.RotateRight(value, count);
    public static ulong Right64(ulong value, int count) => BitOperations.RotateRight(value, count);

    public static int Population32(uint value) => BitOperations.PopCount(value);
    public static int Population64(ulong value) => BitOperations.PopCount(value);
    public static int Leading32(uint value) => BitOperations.LeadingZeroCount(value);
    public static int Leading64(ulong value) => BitOperations.LeadingZeroCount(value);
    public static int Trailing32(uint value) => BitOperations.TrailingZeroCount(value);
    public static int Trailing64(ulong value) => BitOperations.TrailingZeroCount(value);

    public static short ReverseI16(short value) => BinaryPrimitives.ReverseEndianness(value);
    public static ushort ReverseU16(ushort value) => BinaryPrimitives.ReverseEndianness(value);
    public static int ReverseI32(int value) => BinaryPrimitives.ReverseEndianness(value);
    public static uint ReverseU32(uint value) => BinaryPrimitives.ReverseEndianness(value);
    public static long ReverseI64(long value) => BinaryPrimitives.ReverseEndianness(value);
    public static ulong ReverseU64(ulong value) => BinaryPrimitives.ReverseEndianness(value);

    public static ulong RoundTrip(ulong value) => BitOperations.RotateRight(BitOperations.RotateLeft(value, 13), 13);
    public static ulong WrongRoundTrip(ulong value) => BitOperations.RotateRight(BitOperations.RotateLeft(value, 13), 12);
}
