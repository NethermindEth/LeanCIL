using System;

namespace Examples;

public enum CopyCode : ushort { Zero, One }

public static class SpanCopies
{
    public static void Copy(Span<byte> source, Span<byte> destination) => source.CopyTo(destination);

    public static void CopyReadOnly(ReadOnlySpan<byte> source, Span<byte> destination) => source.CopyTo(destination);

    public static bool TryCopy(Span<byte> source, Span<byte> destination) => source.TryCopyTo(destination);

    public static bool TryCopyReadOnly(ReadOnlySpan<byte> source, Span<byte> destination) =>
        source.TryCopyTo(destination);

    public static bool TryCopyEnum(ReadOnlySpan<CopyCode> source, Span<CopyCode> destination) =>
        source.TryCopyTo(destination);

    public static void CopyLongs(ReadOnlySpan<long> source, Span<long> destination) => source.CopyTo(destination);
}
