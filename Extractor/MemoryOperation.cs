namespace Nethermind.LeanCIL;

/// <summary>
/// The pointer addition of a reference and an offset scaled by <paramref name="Stride"/>. A negative stride is
/// its two's complement.
/// </summary>
internal sealed record AddOffset(ulong Stride, bool Signed) : Operation;

internal sealed record SpanLength : Operation;

/// <summary>A slice of a span; <paramref name="Counted"/> says a length operand follows the start.</summary>
internal sealed record SpanSlice(bool Counted) : Operation;

internal sealed record SpanItem(int Width) : Operation;

/// <summary>The source a span constructor uses in a proof outline.</summary>
internal abstract record SpanSource : Operation;

/// <summary>The span over a native pointer and a length, which has byte elements.</summary>
internal sealed record SpanCreate : SpanSource;

internal sealed record ArraySpan(Arrays.Element Element, bool Writable, ArrayRange Range) : SpanSource;

internal sealed record SpanFromReference(int Width, bool Writable) : SpanSource;

internal sealed record SpanSingleReference(int Width, bool Writable) : SpanSource;

/// <summary>The empty span of elements of the given width.</summary>
internal sealed record SpanEmpty(int Width, bool Writable) : Operation;

/// <summary>The view queries a span answers without reading memory.</summary>
internal enum ViewQuery { SpanEmpty, SpanPinnable, ArrayData }

internal sealed record ObserveView(ViewQuery Query) : Operation;

internal sealed record StringLiteral(string Text) : Operation;
