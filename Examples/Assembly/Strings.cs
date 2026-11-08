namespace Examples;

/// <summary>A counter with a label: the label is a string the model holds, compares and tests for null.</summary>
public sealed class Labelled
{
    /// <summary>The count.</summary>
    public ulong Count;

    /// <summary>The label, or null.</summary>
    public string? Label;
}

/// <summary>
/// Strings as opaque references: they are passed, returned, stored, compared by identity and tested for null,
/// and nothing reads their characters.
/// </summary>
public static class Strings
{
    /// <summary>The first label when <paramref name="first"/> holds, otherwise the second.</summary>
    public static string? Pick(bool first, string? left, string? right)
    {
        string? chosen = right;
        if (first) chosen = left;
        return chosen;
    }

    /// <summary>Whether two labels are the same string instance, or both absent.</summary>
    public static bool SameLabel(string? left, string? right) => ReferenceEquals(left, right);

    /// <summary>Replaces the label of <paramref name="item"/> and returns the label it held.</summary>
    public static string? Relabel(Labelled item, string? label)
    {
        var previous = item.Label;
        item.Label = label;
        return previous;
    }
}
