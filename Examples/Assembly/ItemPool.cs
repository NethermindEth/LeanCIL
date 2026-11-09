using System;
using System.Diagnostics.CodeAnalysis;

namespace Examples;

/// <summary>
/// An item an <see cref="ItemPool"/> hands out and takes back; while idle it links into the pool's free list.
/// </summary>
public sealed class PooledItem
{
    internal PooledItem(ItemPool owner, int id)
    {
        Owner = owner;
        Id = id;
    }

    /// <summary>The pool that created this item; only that pool takes it back.</summary>
    public ItemPool Owner { get; }

    /// <summary>An identifier unique among the items the owning pool has created.</summary>
    public int Id { get; }

    /// <summary>Caller data, cleared when the item returns to its pool.</summary>
    public long Payload { get; set; }

    /// <summary>Whether the item is rented out rather than idle in its pool.</summary>
    public bool IsRented { get; internal set; }

    /// <summary>The next idle item in the owning pool's free list, or null at its end.</summary>
    internal PooledItem? NextFree;
}

/// <summary>
/// A bounded pool of reusable items. Idle items form an intrusive singly linked free list, so renting and
/// returning allocate nothing once the pool is warm; at most <see cref="Capacity"/> items are alive at once.
/// </summary>
public sealed class ItemPool
{
    private readonly int _capacity;
    private PooledItem? _free;
    private int _freeCount;
    private int _live;
    private int _nextId;

    /// <summary>Creates an empty pool that keeps at most <paramref name="capacity"/> items alive.</summary>
    public ItemPool(int capacity)
    {
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(capacity);
        _capacity = capacity;
    }

    /// <summary>The most items the pool keeps alive at once.</summary>
    public int Capacity => _capacity;

    /// <summary>The idle items ready to rent without allocating.</summary>
    public int Available => _freeCount;

    /// <summary>The items currently rented out.</summary>
    public int Rented => _live - _freeCount;

    /// <summary>Rents the most recently returned idle item, or creates one while under capacity.</summary>
    /// <exception cref="InvalidOperationException">Every item the capacity allows is rented out.</exception>
    public PooledItem Rent()
    {
        var item = _free;
        if (item is null)
        {
            if (_live == _capacity)
                throw new InvalidOperationException("The pool is exhausted.");
            item = new PooledItem(this, _nextId++);
            _live++;
        }
        else
        {
            _free = item.NextFree;
            item.NextFree = null;
            _freeCount--;
        }
        item.IsRented = true;
        return item;
    }

    /// <summary>Rents an item as <see cref="Rent"/> does, or returns false when the pool is exhausted.</summary>
    public bool TryRent([NotNullWhen(true)] out PooledItem? item)
    {
        if (_free is null && _live == _capacity)
        {
            item = null;
            return false;
        }
        item = Rent();
        return true;
    }

    /// <summary>Takes back a rented item, clearing its payload so the next renter starts clean.</summary>
    /// <exception cref="ArgumentException">The item belongs to another pool.</exception>
    /// <exception cref="InvalidOperationException">The item is already idle in this pool.</exception>
    public void Return(PooledItem item)
    {
        ArgumentNullException.ThrowIfNull(item);
        if (item.Owner != this)
            throw new ArgumentException("The item belongs to another pool.", nameof(item));
        if (!item.IsRented)
            throw new InvalidOperationException("The item was already returned.");
        item.IsRented = false;
        item.Payload = 0;
        item.NextFree = _free;
        _free = item;
        _freeCount++;
    }

    /// <summary>Creates idle items until <paramref name="count"/> are alive, or the capacity is reached.</summary>
    public void Prewarm(int count)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(count);
        var target = Math.Min(count, _capacity);
        while (_live < target)
        {
            var item = new PooledItem(this, _nextId++);
            _live++;
            item.NextFree = _free;
            _free = item;
            _freeCount++;
        }
    }

    /// <summary>
    /// Releases idle items until at most <paramref name="keep"/> remain; returns how many it released.
    /// </summary>
    public int Trim(int keep)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(keep);
        var released = 0;
        while (_freeCount > keep)
        {
            var item = _free!;
            _free = item.NextFree;
            item.NextFree = null;
            _freeCount--;
            _live--;
            released++;
        }
        return released;
    }

    /// <summary>Whether <paramref name="item"/> is idle in this pool's free list.</summary>
    public bool IsIdle(PooledItem item)
    {
        for (var node = _free; node is not null; node = node.NextFree)
        {
            if (node == item)
                return true;
        }
        return false;
    }
}
