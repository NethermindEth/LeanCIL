namespace Nethermind.LeanCIL;

/// <summary>
/// What a local, argument home or evaluation stack slot holds, as the interpreter's value model distinguishes it.
/// <see cref="ToLean"/> renders the Lean kind term.
/// </summary>
internal abstract record LocalKind
{
    internal abstract string ToLean();

    /// <summary>The value a local of this kind holds before its first assignment.</summary>
    internal virtual InitialValue Initial() =>
        throw new InvalidOperationException("A stack-only kind has no local initial value: " + ToLean());

    internal sealed record Reference : LocalKind
    {
        internal override string ToLean() => ".reference";

        internal override InitialValue Initial() => InitialValue.NullRef;
    }

    internal sealed record Object : LocalKind
    {
        internal override string ToLean() => ".object";

        internal override InitialValue Initial() => InitialValue.NullRef;
    }

    internal sealed record Array(Arrays.Element Element) : LocalKind
    {
        internal override string ToLean() => $".array {Element.Expression}";

        internal override InitialValue Initial() => InitialValue.NullRef;
    }

    internal sealed record Span(int Width, bool Writable) : LocalKind
    {
        internal override string ToLean() => $".span {Width} {LeanText.Bool(Writable)}";

        internal override InitialValue Initial() => InitialValue.NullRef;
    }

    internal sealed record Aggregate(int Size) : LocalKind
    {
        internal override string ToLean() => $".aggregate {Size}";

        internal override InitialValue Initial() => new(InitialKind.Aggregate, Size);
    }

    internal sealed record Narrow(Narrowing Narrowing) : LocalKind
    {
        internal override string ToLean() => $".narrow .{Narrowing.LeanName()}";

        internal override InitialValue Initial() => InitialValue.Int32;
    }

    internal sealed record Word32 : LocalKind
    {
        internal override string ToLean() => ".word32";

        internal override InitialValue Initial() => InitialValue.Int32;
    }

    internal sealed record Word64 : LocalKind
    {
        internal override string ToLean() => ".word64";

        internal override InitialValue Initial() => InitialValue.Int64;
    }

    /// <summary>A 128, 256 or 512 bit integer vector.</summary>
    internal sealed record Vector(int Bits) : LocalKind
    {
        internal override string ToLean() => $".vector{Bits}";

        internal override InitialValue Initial() => Bits switch
        {
            128 => new(InitialKind.Vector128, 0),
            256 => new(InitialKind.Vector256, 0),
            512 => new(InitialKind.Vector512, 0),
            _ => throw new InvalidOperationException($"Unsupported vector width: {Bits}")
        };
    }

    /// <summary>A callable pointer of the given signature (a Lean term).</summary>
    internal sealed record MethodPointer(string Signature) : LocalKind
    {
        internal override string ToLean() => $".methodPointer {Signature}";

        internal override InitialValue Initial() => InitialValue.NullRef;
    }

    /// <summary>A table of callable pointers of the given signature.</summary>
    internal sealed record MethodTable(string Signature) : LocalKind
    {
        internal override string ToLean() => $".methodTable {Signature}";

        internal override InitialValue Initial() => InitialValue.NullRef;
    }

    /// <summary>A native address into a table of callable pointers; only the evaluation stack holds one.</summary>
    internal sealed record NativeMethodTable(string Signature) : LocalKind
    {
        internal override string ToLean() => $".nativeMethodTable {Signature}";
    }

    /// <summary>A span or span reference over an enumeration element; only the evaluation stack holds one.</summary>
    internal sealed record EnumSpan(Arrays.Element Element, bool Writable, bool ByReference) : LocalKind
    {
        internal override string ToLean() =>
            $".enumSpan {Element.Expression} {LeanText.Bool(Writable)} {LeanText.Bool(ByReference)}";
    }
}

internal enum InitialKind { NullRef, Int32, Int64, Vector128, Vector256, Vector512, Aggregate, Unmodeled }

/// <summary>A local's value before its first assignment; <paramref name="Size"/> is an aggregate's size.</summary>
internal readonly record struct InitialValue(InitialKind Kind, int Size)
{
    internal static readonly InitialValue NullRef = new(InitialKind.NullRef, 0);
    internal static readonly InitialValue Int32 = new(InitialKind.Int32, 0);
    internal static readonly InitialValue Int64 = new(InitialKind.Int64, 0);
    internal static readonly InitialValue Unmodeled = new(InitialKind.Unmodeled, 0);

    internal string ToLean() => Kind switch
    {
        InitialKind.NullRef => ".nullRef",
        InitialKind.Int32 => ".i32 0",
        InitialKind.Int64 => ".i64 0",
        InitialKind.Vector128 => ".v128 0",
        InitialKind.Vector256 => ".v256 0",
        InitialKind.Vector512 => ".v512 0",
        InitialKind.Aggregate => $".aggregate (List.replicate {Size} 0)",
        _ => ".unmodeled"
    };
}
