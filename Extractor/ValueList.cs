using System.Collections;
using System.Runtime.CompilerServices;

namespace Nethermind.LeanCIL;

/// <summary>Builds a <see cref="ValueList{T}"/> from a collection expression.</summary>
internal static class ValueList
{
    internal static ValueList<T> Create<T>(ReadOnlySpan<T> items) => new(items);
}

/// <summary>
/// An immutable list that compares by its elements, for the collection members of records, which would
/// otherwise compare by reference. It copies what it is built from, so the list never changes. A class
/// rather than a struct keeps the copy constructors of the records that hold it admitted by the self-scan.
/// </summary>
[CollectionBuilder(typeof(ValueList), nameof(ValueList.Create))]
internal sealed class ValueList<T> : IReadOnlyList<T>, IEquatable<ValueList<T>>
{
    readonly T[] items;

    public ValueList(ReadOnlySpan<T> source) => items = source.ToArray();

    public ValueList(T[]? source) : this(new ReadOnlySpan<T>(source))
    {
    }

    public int Count => items.Length;

    public T this[int index] => items[index];

    public IEnumerator<T> GetEnumerator() => ((IEnumerable<T>)items).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => items.GetEnumerator();

    public bool Equals(ValueList<T>? other) => other is not null && items.SequenceEqual(other.items);

    public override bool Equals(object? obj) => Equals(obj as ValueList<T>);

    public override int GetHashCode()
    {
        var hash = new HashCode();
        foreach (var item in items) hash.Add(item);
        return hash.ToHashCode();
    }

    public static bool operator ==(ValueList<T>? left, ValueList<T>? right) =>
        left is null ? right is null : left.Equals(right);

    public static bool operator !=(ValueList<T>? left, ValueList<T>? right) => !(left == right);

    public static implicit operator ValueList<T>(T[] source) => new(source);
}
