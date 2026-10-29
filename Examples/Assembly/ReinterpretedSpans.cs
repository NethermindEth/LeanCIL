using System;
using System.Runtime.InteropServices;

namespace Examples;

internal static class ReinterpretedSpans
{
    public static Span<byte> Bytes(Span<uint> source) => MemoryMarshal.AsBytes(source);
    public static ReadOnlySpan<byte> ReadOnlyBytes(ReadOnlySpan<ulong> source) => MemoryMarshal.AsBytes(source);
    public static Span<uint> Words(Span<byte> source) => MemoryMarshal.Cast<byte, uint>(source);
    public static ReadOnlySpan<ushort> ReadOnlyWords(ReadOnlySpan<byte> source) =>
        MemoryMarshal.Cast<byte, ushort>(source);
    public static Span<byte> Expanded(Span<ulong> source) => MemoryMarshal.Cast<ulong, byte>(source);
    public static Span<int> SameWidth(Span<uint> source) => MemoryMarshal.Cast<uint, int>(source);
    public static Span<byte> EnumBytes(Span<EnumBuffers.Small> source) => MemoryMarshal.AsBytes(source);
    public static Span<EnumBuffers.Small> EnumWords(Span<byte> source) =>
        MemoryMarshal.Cast<byte, EnumBuffers.Small>(source);
    public static uint Aliased(Span<uint> source)
    {
        MemoryMarshal.AsBytes(source)[0] = 255;
        return source[0];
    }
}
