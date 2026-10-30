using System;

namespace Examples;

/// <summary>Interface members encode their <c>in</c> parameters as <c>modreq(InAttribute)</c> references.</summary>
public interface IInWord<T> where T : struct
{
    void Add(in T other, out T result);

    ulong Sum(in ReadOnlySpan<ulong> values);
}

/// <summary>Explicit implementations repeat the interface's <c>in</c> modifier.</summary>
public struct InWord : IInWord<InWord>
{
    public ulong Value;

    void IInWord<InWord>.Add(in InWord other, out InWord result) => result.Value = Value + other.Value;

    ulong IInWord<InWord>.Sum(in ReadOnlySpan<ulong> values) => Value + values[0] + values[1];
}

public static class InParameters
{
    public static void Add<T>(ref T left, in InWord right, out InWord result) where T : struct, IInWord<InWord> =>
        left.Add(in right, out result);

    public static ulong Constrained(ref InWord left, in InWord right)
    {
        Add(ref left, in right, out InWord result);
        return result.Value;
    }
}
