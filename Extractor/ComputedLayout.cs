namespace Nethermind.LeanCIL;

/// <summary>A field of a computed layout: its byte offset, its size, and whether it is itself an aggregate.</summary>
internal sealed record LayoutField(int Offset, int Width, bool IsAggregate)
{
    internal string ToLean() => $"⟨{Offset}, {Width}, {LeanText.Bool(IsAggregate)}⟩";
}

/// <summary>
/// The size of the aggregate of identity <paramref name="Identity"/> and the placement of its fields, as the
/// extraction computed them. Its position among the emitted layouts is the number of its `layout{n}` definition.
/// </summary>
internal sealed record ComputedLayout(string Identity, int Size, ValueList<LayoutField> Fields)
{
    internal string ToLean() => $"⟨{Size}, [{string.Join(", ", Fields.Select(field => field.ToLean()))}]⟩";
}
