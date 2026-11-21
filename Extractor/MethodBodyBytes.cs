using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;

namespace Nethermind.LeanCIL;

/// <summary>
/// The raw bytes of a method body, read from the module image at the method's relative virtual address.
/// Lean re-checks the header and the code length; the body's location in the image stays trusted.
/// </summary>
internal static class MethodBodyBytes
{
    /// <summary>The header and code bytes of a body, and how many of them are header.</summary>
    internal sealed record Body(byte[] Bytes, int HeaderLength);

    /// <summary>
    /// The header and code of the body at <paramref name="rva"/>. A body with exception regions is refused,
    /// so its size is exactly its header and code.
    /// </summary>
    internal static Body Read(PEReader image, int rva)
    {
        MethodBodyBlock body = image.GetMethodBody(rva);
        if (body.ExceptionRegions.Length != 0)
            throw new InvalidDataException($"Method body at RVA 0x{rva:X} has exception regions.");
        byte[] bytes = [.. image.GetSectionData(rva).GetContent(0, body.Size)];
        return new(bytes, bytes.Length - body.GetILBytes()!.Length);
    }
}
