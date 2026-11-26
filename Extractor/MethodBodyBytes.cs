using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;

namespace Nethermind.LeanCIL;

/// <summary>
/// The raw bytes of a method body, read from the module image at the method's relative virtual address.
/// Lean re-checks the header, the code length and the exception section; the body's location in the image stays
/// trusted.
/// </summary>
internal static class MethodBodyBytes
{
    /// <summary>The header, code and exception section bytes of a body, and how many of them are header.</summary>
    internal sealed record Body(byte[] Bytes, int HeaderLength);

    /// <summary>The low two bits of a tiny header (II.25.4.2).</summary>
    const int TinyFormat = 2;

    /// <summary>The header, code and exception section of the body at <paramref name="rva"/>.</summary>
    internal static Body Read(PEReader image, int rva)
    {
        MethodBodyBlock body = image.GetMethodBody(rva);
        byte[] bytes = [.. image.GetSectionData(rva).GetContent(0, body.Size)];
        // A fat header states its size in four-byte words in the upper nibble of its second byte.
        var headerLength = (bytes[0] & 3) == TinyFormat ? 1 : (bytes[1] >> 4) * 4;
        return new(bytes, headerLength);
    }
}
