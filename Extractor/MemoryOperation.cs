namespace Nethermind.LeanCIL;

/// <summary>
/// A runtime memory operation of the interpreter. The cases are the operations consumers inspect or build from
/// typed parts; every other operation is held as <see cref="Other"/>.
/// </summary>
internal abstract record MemoryOperation
{
    /// <summary>An operation no consumer inspects, given by its Lean term including its parentheses.</summary>
    internal static Operation Other(string lean) => new Memory(new OtherMemory(lean));

    internal static Operation Of(MemoryOperation operation) => new Memory(operation);
}

/// <summary>A memory operation no consumer inspects, held as its rendered Lean term.</summary>
internal sealed record OtherMemory : MemoryOperation
{
    readonly string lean;

    internal OtherMemory(string lean) => this.lean = lean;
}

/// <summary>
/// The pointer addition of a reference and an offset scaled by <paramref name="Stride"/>. A negative stride is
/// its two's complement.
/// </summary>
internal sealed record AddOffset(ulong Stride, bool Signed) : MemoryOperation;

internal sealed record SpanLength : MemoryOperation;

/// <summary>A slice of a span; <paramref name="Counted"/> says a length operand follows the start.</summary>
internal sealed record SpanSlice(bool Counted) : MemoryOperation;

internal sealed record SpanItem(int Width) : MemoryOperation;

/// <summary>A memory operation a span constructor runs, which names the Lean span constructor.</summary>
internal abstract record SpanSource : MemoryOperation;

/// <summary>The span over a native pointer and a length, which has byte elements.</summary>
internal sealed record SpanCreate : SpanSource;

internal sealed record ArraySpan(Arrays.Element Element, bool Writable, ArrayRange Range) : SpanSource;

internal sealed record SpanFromReference(int Width, bool Writable) : SpanSource;

internal sealed record SpanSingleReference(int Width, bool Writable) : SpanSource;

/// <summary>The empty span of elements of the given width.</summary>
internal sealed record SpanEmpty(int Width, bool Writable) : MemoryOperation;

/// <summary>The view queries a span answers without reading memory.</summary>
internal enum ViewQuery { SpanEmpty, SpanPinnable, ArrayData }

internal sealed record ObserveView(ViewQuery Query) : MemoryOperation;

internal sealed record StringLiteral(string Text) : MemoryOperation;
