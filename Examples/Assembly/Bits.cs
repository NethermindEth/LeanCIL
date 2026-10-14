using System.Buffers.Binary;
using System.Numerics;

namespace Examples;

public static class Bits
{
    public static nuint LeftNative(nuint value, int count) => BitOperations.RotateLeft(value, count);
    public static nuint RightNative(nuint value, int count) => BitOperations.RotateRight(value, count);
    public static int PopulationNative(nuint value) => BitOperations.PopCount(value);
    public static int LeadingNative(nuint value) => BitOperations.LeadingZeroCount(value);
    public static int TrailingNative(nuint value) => BitOperations.TrailingZeroCount(value);
    public static int Log32(uint value) => BitOperations.Log2(value);
    public static uint RoundUp32(uint value) => BitOperations.RoundUpToPowerOf2(value);
    public static int Log64(ulong value) => BitOperations.Log2(value);
    public static ulong RoundUp64(ulong value) => BitOperations.RoundUpToPowerOf2(value);
    public static int LogNative(nuint value) => BitOperations.Log2(value);
    public static nuint RoundUpNative(nuint value) => BitOperations.RoundUpToPowerOf2(value);
    public static bool PowerI32(int value) => BitOperations.IsPow2(value);
    public static bool PowerU32(uint value) => BitOperations.IsPow2(value);
    public static bool PowerI64(long value) => BitOperations.IsPow2(value);
    public static bool PowerU64(ulong value) => BitOperations.IsPow2(value);
    public static bool PowerNative(nint value) => BitOperations.IsPow2(value);
    public static bool PowerUNative(nuint value) => BitOperations.IsPow2(value);
    public static sbyte ReverseI8(sbyte value) => BinaryPrimitives.ReverseEndianness(value);
    public static byte ReverseU8(byte value) => BinaryPrimitives.ReverseEndianness(value);
    public static nint ReverseNative(nint value) => BinaryPrimitives.ReverseEndianness(value);
    public static nuint ReverseUNative(nuint value) => BinaryPrimitives.ReverseEndianness(value);

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
    public static int WrongLog64(ulong value) => BitOperations.Log2(value) + 1;
}
