using System;
using System.Runtime.Intrinsics;

namespace Examples;

internal static class AggregateSpanFill
{
    public static void Words(Span<AggregateSpans.Words> target, AggregateSpans.Words value) =>
        target.Fill(value);

    public static void Vector128(Span<Vector128<ulong>> target, Vector128<ulong> value) => target.Fill(value);
    public static void Vector256(Span<Vector256<ulong>> target, Vector256<ulong> value) => target.Fill(value);
    public static void Vector512(Span<Vector512<ulong>> target, Vector512<ulong> value) => target.Fill(value);

    public static void Aliased(Span<AggregateSpans.Words> target) => target.Fill(target[0]);
}
