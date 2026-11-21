namespace Nethermind.LeanCIL;

/// <summary>A field enumeration whose carried prefix grows once, in metadata order.</summary>
internal sealed class MetadataFieldPrefix(IEnumerable<uint> fields)
{
    readonly IEnumerator<uint> remaining = fields.GetEnumerator();
    readonly HashSet<uint> reached = [];
    readonly List<uint> carried = [];
    bool complete;

    internal IReadOnlyList<uint> Carried => carried;

    bool Advance(Action<uint> carry)
    {
        if (complete) return false;
        if (!remaining.MoveNext())
        {
            complete = true;
            remaining.Dispose();
            return false;
        }
        var token = remaining.Current;
        reached.Add(token);
        carried.Add(token);
        carry(token);
        return true;
    }

    /// <summary>Carry exactly the fields through the requested token, retaining any longer prefix.</summary>
    internal void Through(uint token, Action<uint> carry)
    {
        if (reached.Contains(token)) return;
        while (Advance(carry))
            if (carried[^1] == token) return;
        throw new InvalidDataException($"Field 0x{token:X8} is absent from its declaring type.");
    }

    /// <summary>Carry all remaining fields without visiting the existing prefix again.</summary>
    internal void All(Action<uint> carry)
    {
        while (Advance(carry)) { }
    }
}
