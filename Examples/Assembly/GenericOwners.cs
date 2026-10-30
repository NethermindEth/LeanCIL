using System;

namespace Examples;

public static class GenericOwners
{
    public static uint Identity(uint value) => OwnerHelper<uint>.Identity(value);

    public static uint Combined(uint value) => OwnerHelper<ulong>.Select<uint>(value, 0);

    public static uint Nested(uint value) => OwnerOuter<ulong>.Inner<uint>.Identity(value);

    public static uint Repeated(uint value) =>
        OwnerHelper<uint>.Identity(value) + OwnerHelper<uint>.Identity(value);

    public static unsafe uint Address(uint value) =>
        ((delegate* managed<uint, uint>)&OwnerHelper<uint>.Identity)(value);

    public static ulong SpanFirst(in ReadOnlySpan<ulong> values) => SpanHelpers.First(values);

    public static int SpanCount(ReadOnlySpan<ulong> values) => SpanHelpers.Count(values);

    public static ulong SpanSecond(ReadOnlySpan<ulong> values) => SpanHelpers.Second(values);

    public static ulong OwnerSpanFirst(ReadOnlySpan<ulong> values) => OwnerHelper<ulong>.First(values);

    public static ulong NestedSpanFirst(ReadOnlySpan<ulong> values) =>
        OwnerOuter<uint>.Inner<ulong>.First(values);
}

/// <summary>Method-generic span members: the call owner is `ReadOnlySpan<!!0>`.</summary>
public static class SpanHelpers
{
    public static T First<T>(in ReadOnlySpan<T> values) where T : unmanaged => values[0];

    public static int Count<T>(ReadOnlySpan<T> values) => values.Length;

    public static T Second<T>(ReadOnlySpan<T> values) where T : unmanaged => values.Slice(1)[0];
}

public static class OwnerHelper<T> where T : unmanaged
{
    public static T Identity(T value) => value;

    public static U Select<U>(U value, T unused) where U : unmanaged => value;

    public static T First(ReadOnlySpan<T> values) => values[0];
}

public static class OwnerOuter<T> where T : unmanaged
{
    public static class Inner<U> where U : unmanaged
    {
        public static U Identity(U value) => value;

        public static U First(ReadOnlySpan<U> values) => values[0];
    }
}
