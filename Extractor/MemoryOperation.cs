namespace Nethermind.LeanCIL;

/// <summary>
/// The pointer addition of a reference and an offset scaled by <paramref name="Stride"/>. A negative stride is
/// its two's complement.
/// </summary>
internal sealed record AddOffset(ulong Stride, bool Signed) : Operation;
