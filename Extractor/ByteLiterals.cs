using System.Text;

namespace Nethermind.LeanCIL;

/// <summary>Byte lists as the extractor writes them into Lean.</summary>
internal static class ByteLiterals
{
    /// <summary>
    /// A Lean byte list as one <c>CIL.Extraction.fixedBytes</c> literal: its length and its big-endian code, as
    /// <see cref="NumeralCode.Append"/> writes it. The elaborator reads numerals where a list literal costs a numeral
    /// and a constructor per byte; the qualified names resolve wherever the text is pasted.
    /// </summary>
    internal static string Of(IEnumerable<byte> bytes)
    {
        var data = bytes.ToArray();
        if (data.Length == 0) return "[]";
        var text = new StringBuilder($"(CIL.Extraction.fixedBytes {data.Length} ");
        NumeralCode.Append(text, data);
        return text.Append(')').ToString();
    }
}
