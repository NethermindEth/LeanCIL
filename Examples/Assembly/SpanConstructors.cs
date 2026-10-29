using System;
using System.Runtime.Intrinsics;

namespace Examples;

internal static class SpanConstructors
{
    public static Span<int> Empty() => Span<int>.Empty;

    public static ReadOnlySpan<AggregateSpans.Words> ReadOnlyEmpty() =>
        ReadOnlySpan<AggregateSpans.Words>.Empty;

    static Span<int> Pass(Span<int> value) => value;
    static ReadOnlySpan<AggregateSpans.Words> PassReadOnly(ReadOnlySpan<AggregateSpans.Words> value) => value;

    public static Span<int> DefaultReset(ref int value)
    {
        var span = new Span<int>(ref value);
        if (span.Length != 1) return span;
        span = default;
        return Pass(span).Slice(0, 0);
    }

    public static ReadOnlySpan<AggregateSpans.Words> ReadOnlyDefaultReset(in AggregateSpans.Words value)
    {
        var span = new ReadOnlySpan<AggregateSpans.Words>(in value);
        if (span.Length != 1) return span;
        span = default;
        return PassReadOnly(span).Slice(0);
    }

    public static Span<int> Single(ref int value) => new(ref value);
    public static ReadOnlySpan<int> ReadOnlySingle(in int value) => new(in value);
    public static Span<AggregateSpans.Words> Aggregate(ref AggregateSpans.Words value) => new(ref value);
    public static ReadOnlySpan<Vector128<ulong>> Vector(in Vector128<ulong> value) => new(in value);

    public static unsafe Span<AggregateSpans.Words> Pointer(AggregateSpans.Words* value, int length) =>
        new(value, length);
    public static unsafe ReadOnlySpan<Vector128<ulong>> VectorPointer(Vector128<ulong>* value, int length) =>
        new(value, length);

    public static int Local(ref int value)
    {
        var span = new Span<int>(ref value);
        return span.Length;
    }

    public static int AggregateLocal(in AggregateSpans.Words value)
    {
        var span = new ReadOnlySpan<AggregateSpans.Words>(in value);
        return span.Length;
    }

    public static unsafe int LayoutLocal(AggregateSpans.VectorRecord* value, int length)
    {
        var span = new Span<AggregateSpans.VectorRecord>(value, length);
        return span.Length;
    }
}
