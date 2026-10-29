using System;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;

namespace Examples;

internal static class MarshaledMemory
{
    public static ulong Read(ReadOnlySpan<byte> source) => MemoryMarshal.Read<ulong>(source);
    public static bool TryRead(ReadOnlySpan<byte> source, out ulong value) =>
        MemoryMarshal.TryRead(source, out value);
    public static void Write(Span<byte> destination, in ulong value) => MemoryMarshal.Write(destination, in value);
    public static bool TryWrite(Span<byte> destination, in ulong value) =>
        MemoryMarshal.TryWrite(destination, in value);
    public static FourLimbs ReadAggregate(ReadOnlySpan<byte> source) => MemoryMarshal.Read<FourLimbs>(source);
    public static bool TryReadAggregate(ReadOnlySpan<byte> source, out FourLimbs value) =>
        MemoryMarshal.TryRead(source, out value);
    public static void WriteAggregate(Span<byte> destination, in FourLimbs value) =>
        MemoryMarshal.Write(destination, in value);
    public static Vector128<byte> ReadVector(ReadOnlySpan<byte> source) => MemoryMarshal.Read<Vector128<byte>>(source);
}
