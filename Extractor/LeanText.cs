namespace Nethermind.LeanCIL;

/// <summary>The spellings of Lean values that several renderers share.</summary>
internal static class LeanText
{
    /// <summary>A Lean `Bool` literal.</summary>
    internal static string Bool(bool value) => value ? "true" : "false";

    /// <summary>A method index written as its number, which a template replaces with a callee parameter.</summary>
    internal static string MethodNumber(int method) => $"{method}";

    /// <summary>The Lean list of the parenthesized class types a class derives from, nearest first.</summary>
    internal static string ClassList(IEnumerable<string> classes) =>
        "[" + string.Join(", ", classes.Select(type => $"({type})")) + "]";
}
