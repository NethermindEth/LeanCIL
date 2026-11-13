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

internal sealed record NullObject : MemoryOperation
{
    internal override string ToLean() => ".nullObject";
}

internal sealed record ArrayLength : MemoryOperation
{
    internal override string ToLean() => ".arrayLength";
}

/// <summary>
/// The address of an array element. <paramref name="ReadOnly"/> says the address follows a readonly prefix, which
/// the term spells with a trailing flag.
/// </summary>
internal sealed record ArrayAddress(Arrays.Element Element, bool ReadOnly) : MemoryOperation
{
    internal override string ToLean() => $"(.arrayAddress {Element.Expression}" + (ReadOnly ? " false)" : ")");
}

internal sealed record ArrayLoad(int Width, bool Signed) : MemoryOperation
{
    internal override string ToLean() => $"(.arrayLoad {Width} {LeanText.Bool(Signed)})";
}

internal sealed record ArrayStore(int Width) : MemoryOperation
{
    internal override string ToLean() => $"(.arrayStore {Width})";
}

/// <summary>A load or store of a composite array element through a transfer of the whole element.</summary>
internal sealed record ArrayTransfer(Arrays.Element Element, bool Store) : MemoryOperation
{
    internal override string ToLean() => $"(.arrayTransfer {Element.Expression} {LeanText.Bool(Store)})";
}

internal enum ReferenceArrayAccess { Length, Load, Store }

internal sealed record ReferenceArrayOperation(ReferenceArrayAccess Access) : MemoryOperation
{
    internal override string ToLean() => Access switch
    {
        ReferenceArrayAccess.Length => ".referenceArrayLength",
        ReferenceArrayAccess.Load => ".referenceArrayLoad",
        _ => ".referenceArrayStore"
    };
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

/// <summary>The span over a native pointer and a length, which has byte elements.</summary>
internal sealed record SpanCreate : MemoryOperation
{
    internal override string ToLean() => ".spanCreate";
}

/// <summary>A memory operation that makes a span, and how an in-place constructor of a span local builds it.</summary>
internal abstract record SpanSource : MemoryOperation
{
    /// <summary>The Lean descriptor of the span's source.</summary>
    internal abstract string SpanDescriptor { get; }
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
internal sealed record SpanEmpty(int Width, bool Writable) : SpanSource
{
    internal override string SpanDescriptor => $".empty {Width} {LeanText.Bool(Writable)}";

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

internal sealed record StaticValue(ValueList<byte> Bytes) : MemoryOperation
{
    internal override string ToLean() => $"(.staticValue {StaticData.LeanBytes(Bytes)})";
}

internal sealed record StaticAddress(ValueList<byte> Bytes) : MemoryOperation
{
    internal override string ToLean() => $"(.staticAddress {StaticData.LeanBytes(Bytes)})";
}

internal sealed record StringLiteral(string Text) : MemoryOperation
{
    internal override string ToLean() => $"(.stringLiteral {JsonSerializer.Serialize(Text)})";
}
