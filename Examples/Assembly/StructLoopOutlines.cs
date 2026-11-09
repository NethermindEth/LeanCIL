namespace Examples;

/// <summary>A receiver loop that transfers its remaining count into a second field.</summary>
public struct OutlineCountdown
{
    public ulong Remaining;
    public ulong Count;

    /// <summary>Consumes the remaining count and returns the accumulated count modulo 2^64.</summary>
    public ulong Drain()
    {
        while (Remaining != 0)
        {
            Remaining--;
            Count++;
        }
        return Count;
    }

    /// <summary>Consumes the remaining count without returning a value.</summary>
    public void Clear()
    {
        while (Remaining != 0)
        {
            Remaining--;
            Count++;
        }
    }

    /// <summary>Consumes at least one count before testing the receiver's remaining field.</summary>
    public ulong DrainAtLeastOnce()
    {
        do
        {
            Remaining--;
            Count++;
        } while (Remaining != 0);
        return Count;
    }
}
