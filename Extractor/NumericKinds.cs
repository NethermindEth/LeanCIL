namespace Nethermind.LeanCIL;

/// <summary>The width and signedness a narrow integer is truncated to when it is read.</summary>
internal enum Narrowing { Signed8, Unsigned8, Signed16, Unsigned16 }

internal static class NarrowingText
{
    /// <summary>The Lean constructor name.</summary>
    internal static string LeanName(this Narrowing narrowing) => narrowing switch
    {
        Narrowing.Signed8 => "signed8", Narrowing.Unsigned8 => "unsigned8",
        Narrowing.Signed16 => "signed16", Narrowing.Unsigned16 => "unsigned16",
        _ => throw new ArgumentOutOfRangeException(nameof(narrowing))
    };
}

/// <summary>
/// The integer element an <c>ldind</c>, <c>stind</c>, <c>ldelem</c> or <c>stelem</c> opcode names; <c>I</c> is
/// native-sized.
/// </summary>
internal enum NumericKind { I1, U1, I2, U2, I4, U4, I8, I }

/// <summary>The width, sign extension and Lean term of a <see cref="NumericKind"/>.</summary>
internal static class NumericKinds
{
    /// <summary>Bytes an access of the kind moves; native int is eight bytes on every admitted profile.</summary>
    internal static int Width(this NumericKind kind) => kind switch
    {
        NumericKind.I1 or NumericKind.U1 => 1,
        NumericKind.I2 or NumericKind.U2 => 2,
        NumericKind.I4 or NumericKind.U4 => 4,
        _ => 8
    };

    /// <summary>A load sign-extends: only the one- and two-byte signed kinds.</summary>
    internal static bool Signed(this NumericKind kind) => kind is NumericKind.I1 or NumericKind.I2;

    /// <summary>The Lean term of the kind, such as <c>.i4</c>.</summary>
    internal static string Term(this NumericKind kind) => "." + kind.ToString().ToLowerInvariant();
}
