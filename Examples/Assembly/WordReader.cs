namespace Examples;

/// <summary>A forward cursor over a caller-owned word buffer.</summary>
public sealed class WordReader
{
    /// <summary>The position of the next word.</summary>
    public uint Position;

    /// <summary>The number of words remaining in the cursor's range.</summary>
    public uint Remaining;

    /// <summary>Advances the position, wrapping at 32 bits.</summary>
    public void Advance() => Position++;

    /// <summary>Consumes the next word; callers must supply a consistent, nonempty cursor range.</summary>
    public int Read(int[] values)
    {
        Advance();
        Remaining--;
        return values[Position - 1];
    }

    /// <summary>Consumes one position and peeks at the next word; at least two words must remain.</summary>
    public int SkipAndPeek(int[] values)
    {
        Advance();
        Remaining--;
        return values[Position];
    }

    /// <summary>Advances the cursor and returns its previous position, wrapping at 32 bits.</summary>
    public uint Reserve()
    {
        var position = Position;
        Position = position + 1;
        return position;
    }

    /// <summary>Consumes one word from a consistent, nonempty cursor range.</summary>
    public int ReadSaved(int[] values)
    {
        var remaining = Remaining;
        var position = Reserve();
        Remaining = remaining - 1;
        return values[position];
    }

    /// <summary>The end of the current range, wrapping at 32 bits.</summary>
    public uint RangeEnd()
    {
        var position = Position;
        return Remaining + position;
    }

    /// <summary>Replaces the remaining count and returns the previous range end.</summary>
    public uint ReplaceRemaining(uint remaining)
    {
        var end = RangeEnd();
        Remaining = remaining;
        return end;
    }

    /// <summary>Replaces the remaining count and returns the previous range end without wrapping.</summary>
    public ulong ReplaceRemainingWide(uint remaining)
    {
        var position = (ulong)Position;
        var previous = Remaining;
        Remaining = remaining;
        return previous + position;
    }
}
