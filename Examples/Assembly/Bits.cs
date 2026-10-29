using System.Buffers.Binary;
using System.Numerics;

namespace Examples;

public static class Bits
{
    public static int PrimitivePopulation32(int value) => int.PopCount(value);
    public static uint PrimitivePopulationU32(uint value) => uint.PopCount(value);
    public static int PrimitiveLeading32(int value) => int.LeadingZeroCount(value);
    public static uint PrimitiveLeadingU32(uint value) => uint.LeadingZeroCount(value);
    public static int PrimitiveTrailing32(int value) => int.TrailingZeroCount(value);
    public static uint PrimitiveTrailingU32(uint value) => uint.TrailingZeroCount(value);
    public static uint PrimitiveLogU32(uint value) => uint.Log2(value);
    public static bool PrimitivePower32(int value) => int.IsPow2(value);
    public static bool PrimitivePowerU32(uint value) => uint.IsPow2(value);
    public static bool PrimitivePower64(long value) => long.IsPow2(value);
    public static bool PrimitivePowerU64(ulong value) => ulong.IsPow2(value);
    public static bool PrimitivePowerNative(nint value) => nint.IsPow2(value);
    public static bool PrimitivePowerUNative(nuint value) => nuint.IsPow2(value);
    public static int PrimitiveLeft32(int value, int count) => int.RotateLeft(value, count);
    public static int PrimitiveRight32(int value, int count) => int.RotateRight(value, count);
    public static uint PrimitiveLeftU32(uint value, int count) => uint.RotateLeft(value, count);
    public static uint PrimitiveRightU32(uint value, int count) => uint.RotateRight(value, count);
    public static long PrimitiveLeft64(long value, int count) => long.RotateLeft(value, count);
    public static long PrimitiveRight64(long value, int count) => long.RotateRight(value, count);
    public static ulong PrimitiveLeftU64(ulong value, int count) => ulong.RotateLeft(value, count);
    public static ulong PrimitiveRightU64(ulong value, int count) => ulong.RotateRight(value, count);
    public static nint PrimitiveLeftNative(nint value, int count) => nint.RotateLeft(value, count);
    public static nint PrimitiveRightNative(nint value, int count) => nint.RotateRight(value, count);
    public static nuint PrimitiveLeftUNative(nuint value, int count) => nuint.RotateLeft(value, count);
    public static nuint PrimitiveRightUNative(nuint value, int count) => nuint.RotateRight(value, count);
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

    public static int PrimitiveNarrow8(uint value) => byte.PopCount((byte)value) |
        (byte.Log2((byte)value) << 8) | ((byte.IsPow2((byte)value) ? 1 : 0) << 16) |
        (byte.LeadingZeroCount((byte)value) << 18) | (byte.TrailingZeroCount((byte)value) << 22);
    public static int PrimitiveNarrow16(uint value) => ushort.PopCount((ushort)value) |
        (ushort.Log2((ushort)value) << 8) | ((ushort.IsPow2((ushort)value) ? 1 : 0) << 16) |
        (ushort.LeadingZeroCount((ushort)value) << 18) | (ushort.TrailingZeroCount((ushort)value) << 23);
    public static int PrimitiveNarrowSigned(uint value) => (sbyte.IsPow2((sbyte)value) ? 1 : 0) |
        ((short.IsPow2((short)value) ? 1 : 0) << 1) | (sbyte.PopCount((sbyte)value) << 2) |
        (short.PopCount((short)value) << 6) | (sbyte.LeadingZeroCount((sbyte)value) << 11) |
        (sbyte.TrailingZeroCount((sbyte)value) << 15) | (short.LeadingZeroCount((short)value) << 19) |
        (short.TrailingZeroCount((short)value) << 24);
    public static int PrimitiveNarrowRotate8(uint value, int count) => byte.RotateLeft((byte)value, count) |
        (byte.RotateRight((byte)value, count) << 8);
    public static int PrimitiveNarrowRotate16(uint value, int count) => ushort.RotateLeft((ushort)value, count) |
        (ushort.RotateRight((ushort)value, count) << 16);

    public static ulong RoundTrip(ulong value) => BitOperations.RotateRight(BitOperations.RotateLeft(value, 13), 13);
    public static ulong WrongRoundTrip(ulong value) => BitOperations.RotateRight(BitOperations.RotateLeft(value, 13), 12);
    public static int WrongLog64(ulong value) => BitOperations.Log2(value) + 1;
}
