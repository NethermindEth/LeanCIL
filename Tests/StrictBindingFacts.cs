using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Text;
using System.Text.RegularExpressions;

/// <summary>
/// What System.Reflection.Metadata reads from an assembly file, as the facts and lines that
/// StrictBinding.Dump decodes with Lean from the same bytes. The two readers are independent, so
/// a difference is a defect in the Lean decoding.
/// </summary>
static partial class StrictBindingFacts
{
    /// <summary>The highest metadata table number the Lean schema covers.</summary>
    const int LastTable = 0x2C;

    /// <summary>The size from which a heap needs four-byte indexes.</summary>
    const int WideHeap = 1 << 16;

    internal sealed record Fact(string Kind, string Text, long[] Numbers)
    {
        /// <summary>The line `StrictBinding.Fact.line` prints for the same fact.</summary>
        internal string Line() => Kind == "identity" ? "identity " + Text
            : Kind + " " + (Text.Length == 0 ? "" : Text + " ") + string.Join(' ', Numbers);

        /// <summary>The Lean constructor application for the fact.</summary>
        internal string Lean()
        {
            var numbers = string.Join(' ', Numbers);
            return Kind switch
            {
                "section" => $".sectionHeader {numbers}",
                "stream" => $".stream \"{Text}\" {numbers}",
                "identity" => $".identity\n     (StrictBinding.asciiOf\n       \"{Text}\")",
                _ => $".{Kind} {numbers}"
            };
        }
    }

    /// <summary>A method with a body: its full name, its MethodDef token and the bytes of header and code.</summary>
    internal sealed record Body(string Name, int Token, byte[] Bytes);

    /// <summary>The facts of an image in the order `StrictBinding.facts` lists them.</summary>
    internal static List<Fact> Read(byte[] file)
    {
        using PEReader pe = new(ImmutableArray.Create(file));
        var headers = pe.PEHeaders;
        var reader = pe.GetMetadataReader();
        var metadata = (long)headers.MetadataStartOffset;
        List<Fact> facts = [];
        facts.AddRange(headers.SectionHeaders.Select(section => new Fact("section", "",
            [section.VirtualSize, section.VirtualAddress, section.SizeOfRawData, section.PointerToRawData])));
        facts.Add(new("metadata", "", [metadata, headers.MetadataSize]));
        var streams = Streams(file, (int)metadata);
        (string Name, string Header, HeapIndex? Heap)[] kinds =
            [("tables", "#~", null), ("strings", "#Strings", HeapIndex.String),
                ("userStrings", "#US", HeapIndex.UserString), ("guids", "#GUID", HeapIndex.Guid),
                ("blobs", "#Blob", HeapIndex.Blob)];
        foreach (var (name, header, heap) in kinds)
        {
            if (!streams.TryGetValue(header, out var stream) || stream.Size == 0) continue;
            facts.Add(new("stream", name, [stream.Start, stream.Size]));
            if (heap is { } index) RequireSameHeap(reader, index, metadata, header, stream);
        }
        // Wide indexes follow the stream header sizes, which a heap-trimming reader cannot supply.
        long Size(string header) => streams.TryGetValue(header, out var stream) ? stream.Size : 0;
        facts.Add(new("heapSizes", "", [(Size("#Strings") >= WideHeap ? 1 : 0) | (Size("#GUID") >= WideHeap ? 2 : 0) |
            (Size("#Blob") >= WideHeap ? 4 : 0)]));
        for (var table = 0; table <= LastTable; table++)
        {
            var index = (TableIndex)table;
            if (reader.GetTableRowCount(index) > 0)
                facts.Add(new("table", "", [table, reader.GetTableRowCount(index), reader.GetTableRowSize(index),
                    metadata + reader.GetTableMetadataOffset(index)]));
        }
        foreach (var handle in reader.MethodDefinitions)
        {
            var rva = reader.GetMethodDefinition(handle).RelativeVirtualAddress;
            if (rva != 0 && headers.TryGetDirectoryOffset(new DirectoryEntry(rva, 1), out var offset))
                facts.Add(new("method", "", [MetadataTokens.GetRowNumber(handle), rva, offset]));
            else if (rva != 0)
                throw new InvalidDataException($"System.Reflection.Metadata does not map RVA 0x{rva:x}");
        }
        facts.Add(new("identity", reader.GetAssemblyDefinition().GetAssemblyName().FullName, []));
        return facts;
    }

    /// <summary>
    /// The stream headers of the metadata root, read directly: System.Reflection.Metadata does not expose
    /// the table stream and reports a heap shorter than its header states when the heap ends in padding.
    /// </summary>
    static Dictionary<string, (long Start, long Size)> Streams(byte[] file, int root)
    {
        var versionLength = BitConverter.ToInt32(file, root + 12);
        var count = BitConverter.ToUInt16(file, root + 18 + versionLength);
        var offset = root + 20 + versionLength;
        Dictionary<string, (long Start, long Size)> streams = [];
        for (var stream = 0; stream < count; stream++)
        {
            var end = Array.IndexOf(file, (byte)0, offset + 8);
            var name = Encoding.ASCII.GetString(file, offset + 8, end - offset - 8);
            streams.Add(name, (root + BitConverter.ToInt32(file, offset), BitConverter.ToInt32(file, offset + 4)));
            offset += 8 + (end - offset - 8 + 4) / 4 * 4;
        }
        return streams;
    }

    /// <summary>
    /// The reader and the stream header agree on where a heap starts and, up to padding, its length.
    /// </summary>
    static void RequireSameHeap(MetadataReader reader, HeapIndex heap, long metadata, string name,
        (long Start, long Size) stream)
    {
        const int padding = 3;
        var size = reader.GetHeapSize(heap);
        if (metadata + reader.GetHeapMetadataOffset(heap) != stream.Start || size > stream.Size ||
            stream.Size - size > padding)
            throw new InvalidDataException($"System.Reflection.Metadata disagrees with the header of {name}: " +
                $"offset {metadata + reader.GetHeapMetadataOffset(heap)}, size {size}; header offset " +
                $"{stream.Start}, size {stream.Size}");
    }

    /// <summary>Every method that has a body, with the bytes of its header and code.</summary>
    internal static List<Body> Bodies(byte[] file)
    {
        using PEReader pe = new(ImmutableArray.Create(file));
        var reader = pe.GetMetadataReader();
        List<Body> bodies = [];
        foreach (var handle in reader.MethodDefinitions)
        {
            var method = reader.GetMethodDefinition(handle);
            if (method.RelativeVirtualAddress == 0) continue;
            var type = reader.GetTypeDefinition(method.GetDeclaringType());
            var name = reader.GetString(type.Namespace) + "." + reader.GetString(type.Name) + "." +
                reader.GetString(method.Name);
            var size = pe.GetMethodBody(method.RelativeVirtualAddress).Size;
            var bytes = pe.GetSectionData(method.RelativeVirtualAddress).GetContent(0, size).ToArray();
            bodies.Add(new(name, MetadataTokens.GetToken(handle), bytes));
        }
        return bodies;
    }

    /// <summary>The Lean module for an image: its digest, the facts a reader found and its method bodies.</summary>
    internal static string Module(byte[] file)
    {
        var text = new StringBuilder("""
            import StrictBinding.Dump

            /-!
            # Strict binding fixture

            An SDK-built library with a tiny-header method, a fat-header method with locals, a byte
            enum, an explicit-layout struct with static data and a class with a virtual method and two
            derived classes. The bytes, the facts System.Reflection.Metadata reads from them and the
            method bodies are generated by `Tests/StrictBindingFixture.cs`; do not edit them.
            -/

            namespace StrictFixture

            /-- A 64-byte chunk written as its high and low 32 bytes, so that no row is longer than a line. -/
            def joinHalves (high low : Nat) : Nat := high * 2 ^ 256 + low


            """);
        text.Append(ChunkRow().Replace(BindingImage.Definitions(file), "  joinHalves 0x${high}\n    0x${low}${end}"))
            .Append('\n');
        text.Append(BindingImage.SingleDigestTheorem(file)).Append("#print axioms digest\n\n");
        var identity = Read(file).Last().Text;
        text.Append("/-- The identity of the assembly the image holds. -/\ndef identity : String :=\n")
            .Append($"  \"{identity}\"\n\n");
        text.Append("/-- What System.Reflection.Metadata reads from the image. -/\n");
        text.Append("def expectedFacts : List StrictBinding.Fact :=\n  [");
        text.Append(string.Join(",\n   ", Read(file).Select(fact => fact.Lean()))).Append("]\n\n");
        text.Append("/-- The method bodies of the image: name, MethodDef token and the bytes of header and code. "
            + "-/\n");
        text.Append("def bodies : List (String × Nat × List Nat) :=\n  [");
        text.Append(string.Join(",\n   ", Bodies(file).Select(body =>
            $"(\"{body.Name}\", 0x{body.Token:x8},\n     [{string.Join(",\n      ", body.Bytes.Chunk(BodyBytesPerRow)
                .Select(row => string.Join(", ", row.Select(Hex))))}])")));
        text.Append("]\n\nend StrictFixture\n");
        return text.ToString();
    }

    /// <summary>The bytes of the image a fixture module holds.</summary>
    internal static byte[] ReadImage(string module)
    {
        var length = int.Parse(Length().Match(module).Groups[1].Value);
        var chunks = Chunk().Matches(module).Select(match => match.Groups[1].Value + match.Groups[2].Value);
        var bytes = Convert.FromHexString(string.Concat(chunks));
        return bytes[..length];
    }

    const int BodyBytesPerRow = 12;

    static string Hex(byte value) => "0x" + value.ToString("x2");

    [GeneratedRegex(@"length := (\d+),")]
    private static partial Regex Length();

    [GeneratedRegex(@"^  joinHalves 0x([0-9a-f]{64})\n    0x([0-9a-f]{64}),?$", RegexOptions.Multiline)]
    private static partial Regex Chunk();

    [GeneratedRegex(@"^  0x(?<high>[0-9a-f]{64})(?<low>[0-9a-f]{64})(?<end>,?)$", RegexOptions.Multiline)]
    private static partial Regex ChunkRow();
}
