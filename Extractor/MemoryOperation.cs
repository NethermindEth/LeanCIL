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

/// <summary>The array element storage, mutability and range used by a span proof outline.</summary>
internal sealed record ArraySpan(Arrays.Element Element, bool Writable, ArrayRange Range) : Operation;
