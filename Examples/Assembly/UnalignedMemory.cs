using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Examples;

internal static class UnalignedMemory
{
    public static unsafe ulong ReadAlignedWord(byte* source) => Unsafe.Read<ulong>(source);
    public static unsafe FourLimbs ReadAlignedAggregate(byte* source) => Unsafe.Read<FourLimbs>(source);
    public static unsafe Vector128<byte> ReadAligned128(byte* source) => Unsafe.Read<Vector128<byte>>(source);
    public static unsafe void WriteAlignedWord(byte* destination, ulong value) => Unsafe.Write(destination, value);
    public static unsafe void WriteAlignedAggregate(byte* destination, FourLimbs value) =>
        Unsafe.Write(destination, value);
    public static unsafe void WriteAligned128(byte* destination, Vector128<byte> value) =>
        Unsafe.Write(destination, value);
    public static unsafe ulong ReadPointerWord(byte* source) => Unsafe.ReadUnaligned<ulong>(source);
    public static unsafe FourLimbs ReadPointerAggregate(byte* source) => Unsafe.ReadUnaligned<FourLimbs>(source);
    public static unsafe void WritePointerWord(byte* destination, ulong value) => Unsafe.WriteUnaligned(destination, value);
    public static unsafe void WritePointerAggregate(byte* destination, FourLimbs value) =>
        Unsafe.WriteUnaligned(destination, value);
    public static sbyte ReadSigned(in byte source) => Unsafe.ReadUnaligned<sbyte>(in source);
    public static short ReadHalf(in byte source) => Unsafe.ReadUnaligned<short>(in source);
    public static ulong ReadWord(in byte source) => Unsafe.ReadUnaligned<ulong>(in source);
    public static FourLimbs ReadAggregate(in byte source) => Unsafe.ReadUnaligned<FourLimbs>(in source);
    public static Vector128<byte> Read128(in byte source) => Unsafe.ReadUnaligned<Vector128<byte>>(in source);
    public static Vector512<uint> Read512(in byte source) => Unsafe.ReadUnaligned<Vector512<uint>>(in source);
    public static void WriteSigned(ref byte destination, sbyte value) => Unsafe.WriteUnaligned(ref destination, value);
    public static void WriteHalf(ref byte destination, short value) => Unsafe.WriteUnaligned(ref destination, value);
    public static void WriteWord(ref byte destination, ulong value) => Unsafe.WriteUnaligned(ref destination, value);
    public static void WriteAggregate(ref byte destination, FourLimbs value) =>
        Unsafe.WriteUnaligned(ref destination, value);
    public static void Write128(ref byte destination, Vector128<byte> value) =>
        Unsafe.WriteUnaligned(ref destination, value);
    public static void Write512(ref byte destination, Vector512<uint> value) =>
        Unsafe.WriteUnaligned(ref destination, value);
}
