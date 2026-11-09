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
}
