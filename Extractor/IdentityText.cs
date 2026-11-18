using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Globalization;
using System.Numerics;
using System.Text;
using System.Text.Encodings.Web;

namespace Nethermind.LeanCIL;

/// <summary>The codes, escapes and fallbacks CIL/Identity.lean gives names and literals.</summary>
internal static class IdentityText
{
    static readonly UTF8Encoding StrictUtf8 = new(false, true);

    /// <summary>The UTF-8 bytes of a name; a lone surrogate, which no <c>#Strings</c> entry decodes to, fails.
    /// </summary>
    internal static byte[] Utf8(string text)
    {
        try
        {
            return StrictUtf8.GetBytes(text);
        }
        catch (EncoderFallbackException error)
        {
            throw new InvalidDataException($"Metadata name without UTF-8 bytes: {error.Message}", error);
        }
    }

    /// <summary>The text of UTF-8 bytes, or null when they are not UTF-8, as <c>String.fromUTF8?</c> decides.
    /// </summary>
    internal static string? DecodeUtf8(byte[] bytes)
    {
        try
        {
            return StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException)
        {
            return null;
        }
    }

    /// <summary>Whether every surrogate in <paramref name="units"/> is a high one followed by a low one.</summary>
    internal static bool WellFormed(ReadOnlySpan<char> units)
    {
        for (int index = 0; index < units.Length; index++)
        {
            if (!char.IsSurrogate(units[index])) continue;
            if (!char.IsHighSurrogate(units[index]) || index + 1 == units.Length ||
                !char.IsLowSurrogate(units[index + 1])) return false;
            index++;
        }
        return true;
    }

    /// <summary>The bytes after a leading 1 as one big-endian number.</summary>
    internal static BigInteger Code(ReadOnlySpan<byte> bytes)
    {
        byte[] digits = new byte[bytes.Length + 1];
        digits[0] = 1;
        bytes.CopyTo(digits.AsSpan(1));
        return new(digits, isUnsigned: true, isBigEndian: true);
    }

    /// <summary>The UTF-16 code units after a leading 1 as one big-endian number in base 65536.</summary>
    internal static BigInteger Code(ReadOnlySpan<char> units)
    {
        byte[] digits = new byte[2 * units.Length + 2];
        digits[1] = 1;
        for (int index = 0; index < units.Length; index++)
            BinaryPrimitives.WriteUInt16BigEndian(digits.AsSpan(2 * index + 2), units[index]);
        return new(digits, isUnsigned: true, isBigEndian: true);
    }

    /// <summary>The raw structure of a code, <c>rawCodeDisplay</c>.</summary>
    internal static string RawCode(BigInteger code) =>
        $$"""{ code := 0x{{Hex(code)}} }""";

    /// <summary>The minimal lowercase unsigned hexadecimal digits of a natural code.</summary>
    internal static string Hex(BigInteger code)
    {
        string digits = Convert.ToHexStringLower(code.ToByteArray(isUnsigned: true, isBigEndian: true));
        return digits[0] == '0' && digits.Length > 1 ? digits[1..] : digits;
    }

    /// <summary>The number of characters Lean counts in <paramref name="text"/>: its Unicode scalar values.
    /// </summary>
    internal static int Columns(string text)
    {
        int count = 0;
        foreach (Rune _ in text.EnumerateRunes()) count++;
        return count;
    }

    /// <summary>Inclusive code point ranges of <c>CIL.invisibleRanges</c>: Unicode categories Cc, Cf, Zl and Zp
    /// and the non-ASCII characters of Zs.</summary>
    internal static readonly ImmutableArray<(int Low, int High)> InvisibleRanges =
    [
        (0x0000, 0x001F), (0x007F, 0x00A0), (0x00AD, 0x00AD), (0x0600, 0x0605), (0x061C, 0x061C),
        (0x06DD, 0x06DD), (0x070F, 0x070F), (0x0890, 0x0891), (0x08E2, 0x08E2), (0x1680, 0x1680),
        (0x180E, 0x180E), (0x2000, 0x200F), (0x2028, 0x202F), (0x205F, 0x2064), (0x2066, 0x206F),
        (0x3000, 0x3000), (0xFEFF, 0xFEFF), (0xFFF9, 0xFFFB), (0x110BD, 0x110BD), (0x110CD, 0x110CD),
        (0x13430, 0x1343F), (0x1BCA0, 0x1BCA3), (0x1D173, 0x1D17A), (0xE0001, 0xE0001), (0xE0020, 0xE007F)
    ];

    static bool Invisible(Rune rune)
    {
        foreach (var (low, high) in InvisibleRanges)
            if (low <= rune.Value && rune.Value <= high) return true;
        return false;
    }

    const int UnicodeEscapeLimit = 0x10000;

    // escapedText?: null when an invisible character lies above U+FFFF, which a Lean string cannot escape.
    static string? Escaped(string text, bool quoted, bool sourceLiteral = false)
    {
        StringBuilder escaped = new(text.Length);
        foreach (Rune rune in text.EnumerateRunes())
        {
            // Lean accepts four hex digits per escape. A supplementary scalar is one source character.
            bool escape = sourceLiteral ? rune.IsBmp && JavaScriptEncoder.Default.WillEncode(rune.Value)
                : Invisible(rune);
            if (escape && rune.Value >= UnicodeEscapeLimit) return null;
            if (rune.Value == '\\') escaped.Append(@"\\");
            else if (quoted && rune.Value == '"') escaped.Append("\\\"");
            else if (escape) escaped.Append(CultureInfo.InvariantCulture, $"\\u{rune.Value:X4}");
            else if (rune.IsBmp) escaped.Append((char)rune.Value);
            else escaped.Append(rune.ToString());
        }
        return escaped.ToString();
    }

    /// <summary>The text <c>readableText?</c> writes: escaped, with a leading <c>{</c> written <c>\{</c>.
    /// </summary>
    internal static string? Readable(string text) =>
        Escaped(text, false) is { } escaped ? (text.StartsWith('{') ? $"""\{escaped}""" : escaped) : null;

    /// <summary>The Lean string literal <c>quotedText?</c> writes for <paramref name="text"/>.</summary>
    internal static string? Quoted(string text) => Escaped(text, true) is { } escaped ? $"\"{escaped}\"" : null;

    /// <summary>A Lean source literal preserving every Unicode scalar of its input.</summary>
    internal static string Quote(string text) => WellFormed(text)
        ? $"\"{Escaped(text, quoted: true, sourceLiteral: true)}\""
        : throw new InvalidDataException("A Lean string cannot represent an unpaired surrogate.");
}
