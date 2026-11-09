namespace Examples;

/// <summary>Independent fields whose values are read between writes to the receiver.</summary>
public struct OutlineCounters
{
    public ulong First;
    public ulong Second;

    public long SignedLiteral()
    {
        First = unchecked((ulong)-1L);
        return (long)First;
    }

    public ulong UnsignedLiteral()
    {
        First = uint.MaxValue;
        return First;
    }

    public ulong ExchangeAdd(ulong value)
    {
        First = value;
        Second = First + Second;
        First = Second + 1;
        return First + Second;
    }

    public ulong WrongExchangeAdd(ulong value)
    {
        First = value;
        Second = First + Second;
        First = Second + 2;
        return First + Second;
    }
}

/// <summary>Scalar fields with truncating stores and signed or unsigned loads.</summary>
public struct NarrowTotals
{
    public byte Small;
    public short Signed;
    public uint Count;

    public readonly uint ReadSum() => Small + (uint)Signed + Count;

    public uint WriteRead(uint value)
    {
        Small = (byte)value;
        Signed = (short)value;
        Count = Small + (uint)Signed;
        return Count;
    }
}
