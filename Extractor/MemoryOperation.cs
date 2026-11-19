using System.Text.Json;

namespace Nethermind.LeanCIL;

/// <summary>
/// A runtime memory operation of the interpreter. The cases are the operations consumers inspect or build from
/// typed parts; every other operation is held as <see cref="Other"/>.
/// </summary>
internal abstract record MemoryOperation
{
    /// <summary>The Lean term, with the parentheses an argument position needs.</summary>
    internal abstract string ToLean();

    /// <summary>An operation no consumer inspects, given by its Lean term including its parentheses.</summary>
    internal static Operation Other(string lean) => new Memory(new OtherMemory(lean));

    internal static Operation Of(MemoryOperation operation) => new Memory(operation);
}

/// <summary>A memory operation no consumer inspects, held as its rendered Lean term.</summary>
internal sealed record OtherMemory : MemoryOperation
{
    readonly string lean;

    internal OtherMemory(string lean) => this.lean = lean;

    internal override string ToLean() => lean;
}

/// <summary>
/// The pointer addition of a reference and an offset scaled by <paramref name="Stride"/>. A negative stride is
/// its two's complement.
/// </summary>
internal sealed record AddOffset(ulong Stride, bool Signed) : MemoryOperation
{
    internal override string ToLean() => $"(.add {Stride} {LeanText.Bool(Signed)})";
}

internal sealed record SpanLength : MemoryOperation
{
    internal override string ToLean() => ".spanLength";
}

/// <summary>A slice of a span; <paramref name="Counted"/> says a length operand follows the start.</summary>
internal sealed record SpanSlice(bool Counted) : MemoryOperation
{
    internal override string ToLean() => $"(.spanSlice {LeanText.Bool(Counted)})";
}

internal sealed record SpanItem(int Width) : MemoryOperation
{
    internal override string ToLean() => $"(.spanItem {Width})";
}

/// <summary>A memory operation a span constructor runs, which names the Lean span constructor.</summary>
internal abstract record SpanSource : MemoryOperation
{
    /// <summary>The Lean <c>SpanConstructor</c> of the overload.</summary>
    internal abstract string SpanDescriptor { get; }
}

/// <summary>The span over a native pointer and a length, which has byte elements.</summary>
internal sealed record SpanCreate : SpanSource
{
    internal override string SpanDescriptor => ".staticBytes";

    internal override string ToLean() => ".spanCreate";
}

internal sealed record ArraySpan(Arrays.Element Element, bool Writable, ArrayRange Range) : SpanSource
{
    internal override string SpanDescriptor =>
        $".array {Element.Expression} {LeanText.Bool(Writable)} {Range.LeanName()}";

    internal override string ToLean()
        => $"(.arraySpan {Element.Expression} {LeanText.Bool(Writable)} {Range.LeanName()})";
}

internal sealed record SpanFromReference(int Width, bool Writable) : SpanSource
{
    internal override string SpanDescriptor => $".reference {Width} {LeanText.Bool(Writable)}";

    internal override string ToLean() => $"(.spanFromReference {Width} {LeanText.Bool(Writable)})";
}

internal sealed record SpanSingleReference(int Width, bool Writable) : SpanSource
{
    internal override string SpanDescriptor => $".singleReference {Width} {LeanText.Bool(Writable)}";

    internal override string ToLean() => $"(.spanSingleReference {Width} {LeanText.Bool(Writable)})";
}

/// <summary>The empty span of elements of the given width.</summary>
internal sealed record SpanEmpty(int Width, bool Writable) : MemoryOperation
{
    internal override string ToLean() => $"(.spanEmpty {Width} {LeanText.Bool(Writable)})";
}

/// <summary>The view queries a span answers without reading memory.</summary>
internal enum ViewQuery { SpanEmpty, SpanPinnable, ArrayData }

internal sealed record ObserveView(ViewQuery Query) : MemoryOperation
{
    internal override string ToLean() => Query switch
    {
        ViewQuery.SpanEmpty => "(.observeView .spanEmpty)",
        ViewQuery.SpanPinnable => "(.observeView .spanPinnable)",
        _ => "(.observeView .arrayData)"
    };
}

internal sealed record StringLiteral(string Text) : MemoryOperation
{
    internal override string ToLean() => $"(.stringLiteral {JsonSerializer.Serialize(Text)})";
}
