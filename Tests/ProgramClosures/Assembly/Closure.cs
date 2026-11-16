using System.Runtime.CompilerServices;

/// <summary>
/// <c>AddTwo</c> calls <c>Bump</c> and <c>Nudge</c>, whose bodies are the same, so a program may hold
/// both at one index.
/// </summary>
public static class Closure
{
    [MethodImpl(MethodImplOptions.NoInlining)]
    static ulong Bump(ulong value) => unchecked(value + 1);

    [MethodImpl(MethodImplOptions.NoInlining)]
    static ulong Nudge(ulong value) => unchecked(value + 1);

    [MethodImpl(MethodImplOptions.NoInlining)]
    static ulong AddTwo(ulong value) => Nudge(Bump(value));

    /// <summary>Returns <paramref name="x"/> plus two through <c>AddTwo</c>.</summary>
    public static ulong Entry(ulong x) => AddTwo(x);
}
