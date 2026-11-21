using System.Text.RegularExpressions;

/// <summary>
/// Names of methods that survive unrelated edits: a method written in source, or the source method a generated
/// one belongs to.
/// </summary>
static partial class StableNames
{
    /// <summary>
    /// <paramref name="signature"/> itself for a method written in source. A compiler-generated method
    /// (closure, lambda, local function, iterator or async state machine) is named by the source method
    /// it was generated for, since the compiler numbers it by positions that shift with unrelated edits.
    /// Generated top-level types share one name, as their numbers count across the assembly.
    /// </summary>
    internal static string Of(string signature)
    {
        if (signature.EndsWith(Generated, StringComparison.Ordinal)) return signature;
        var member = signature[(signature.IndexOf(' ', StringComparison.Ordinal) + 1)..];
        var separator = member.IndexOf("::", StringComparison.Ordinal);
        var declaring = member[..separator];
        if (declaring.StartsWith('<')) return GeneratedTypes;
        var nested = declaring.IndexOf("/<", StringComparison.Ordinal);
        var method = member[(separator + 2)..];
        if (nested < 0 && !method.StartsWith('<')) return signature;
        var outer = nested < 0 ? declaring : declaring[..nested];
        var source = SourceName.Match((nested < 0 ? "" : declaring[nested..]) + "::" + method).Groups["name"].Value;
        return source.Length == 0 ? $"{outer} closure classes{Generated}" : $"{outer}::{source}{Generated}";
    }

    /// <summary>The suffix of every name that stands for compiler-generated methods.</summary>
    const string Generated = " (compiler-generated)";

    /// <summary>The one name of every method of a compiler-generated top-level type.</summary>
    const string GeneratedTypes = "top-level types" + Generated;

    /// <summary>How many times each name occurs.</summary>
    internal static Dictionary<string, int> Counts(IEnumerable<string> names) =>
        names.GroupBy(name => name, StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.Count(), StringComparer.Ordinal);

    // The first nonempty bracketed name, which the compiler sets to the method it generated code for;
    // a closure class's own constructor has none and counts toward its outer type's closure classes.
    [GeneratedRegex(@"<(?<name>[^<>]+)>")]
    private static partial Regex SourceName { get; }
}
