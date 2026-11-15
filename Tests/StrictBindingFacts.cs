using System.Collections.Immutable;
using System.Numerics;
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

    /// <summary>
    /// The Lean module for an image: its digest, the facts a reader found, its method bodies and the assembly block
    /// an extraction carries for it.
    /// </summary>
    internal static string Module(byte[] file)
    {
        var text = new StringBuilder("""
            import StrictBinding.Dump
            import StrictBinding.Sha256
            import CIL.Extraction.MetadataBytes

            /-!
            # Strict binding fixture

            An SDK-built library with a tiny-header method, a fat-header method with locals, a byte
            enum, an explicit-layout struct with static data and a class with a virtual method and two
            derived classes. The bytes, the facts System.Reflection.Metadata reads from them, the
            method bodies and the assembly block an extraction carries are generated by
            `Tests/StrictBindingFixture.cs`; do not edit them.
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
        text.Append("]\n\n");
        text.Append("/-- The assembly block an extraction carries for the image. -/\n")
            .Append("def assemblyBlock : CIL.Extraction.AssemblyMetadata :=\n  ").Append(AssemblyBlock(file))
            .Append("\n\nend StrictFixture\n");
        return text.ToString();
    }

    // The fixed fields of a table stream header before its row counts, and the bytes of each row count.
    const int TableHeaderFixedBytes = 24;
    const int RowCountBytes = 4;

    // The Assembly row's PublicKey, Name and Culture columns follow its hash algorithm, four version numbers and
    // flags.
    const int AssemblyHeapColumns = 4 + 4 * 2 + 4;

    // The widest a generated Lean line may be.
    const int LeanLineWidth = 96;

    /// <summary>
    /// The assembly block an extraction carries for an image, as a Lean `CIL.Extraction.AssemblyMetadata`: the table
    /// stream header through its last row count, the header decoded, the Assembly row with each heap offset replaced
    /// by its key, and the entries the row names. A key is 0 for offset 0 and otherwise the rank of the entry's bytes
    /// among the block's entries of its heap, as the extractor numbers them.
    /// </summary>
    internal static string AssemblyBlock(byte[] file)
    {
        using PEReader pe = new(ImmutableArray.Create(file));
        var reader = pe.GetMetadataReader();
        var metadata = pe.PEHeaders.MetadataStartOffset;
        var streams = Streams(file, metadata);
        var tables = (int)streams["#~"].Start;
        var valid = BitConverter.ToUInt64(file, tables + 8);
        var header = file[tables..(tables + TableHeaderFixedBytes + RowCountBytes * BitOperations.PopCount(valid))];
        var heapSizes = header[6];
        List<string> counts = [];
        var countAt = TableHeaderFixedBytes;
        for (var table = 0; table < 64; table++)
        {
            if ((valid >> table & 1) == 0) continue;
            counts.Add($"({table}, {BitConverter.ToUInt32(header, countAt)})");
            countAt += RowCountBytes;
        }
        var assembly = reader.GetAssemblyDefinition();
        var row = file.AsSpan(metadata + reader.GetTableMetadataOffset(TableIndex.Assembly),
            reader.GetTableRowSize(TableIndex.Assembly)).ToArray();
        var stringsStart = (int)streams["#Strings"].Start;
        var blobsStart = (int)streams["#Blob"].Start;
        byte[] StringEntry(int offset) =>
            file[(stringsStart + offset)..(Array.IndexOf(file, (byte)0, stringsStart + offset) + 1)];
        byte[] BlobEntry(int offset)
        {
            var start = blobsStart + offset;
            int first = file[start];
            var (prefix, length) = first < 0x80 ? (1, first)
                : first < 0xC0 ? (2, (first & 0x3F) << 8 | file[start + 1])
                : (4, (first & 0x1F) << 24 | file[start + 1] << 16 | file[start + 2] << 8 | file[start + 3]);
            return file[start..(start + prefix + length)];
        }
        var key = reader.GetHeapOffset(assembly.PublicKey);
        var name = reader.GetHeapOffset(assembly.Name);
        var culture = reader.GetHeapOffset(assembly.Culture);
        var (blobKeys, blobs) = Ranked([key], BlobEntry);
        var (stringKeys, strings) = Ranked([name, culture], StringEntry);
        var stringWidth = (heapSizes & 1) != 0 ? 4 : 2;
        var blobWidth = (heapSizes & 4) != 0 ? 4 : 2;
        var column = AssemblyHeapColumns;
        foreach (var (offset, keys, width) in new[]
                     { (key, blobKeys, blobWidth), (name, stringKeys, stringWidth), (culture, stringKeys, stringWidth) })
        {
            Array.Copy(BitConverter.GetBytes(keys[offset]), 0, row, column, width);
            column += width;
        }
        var token = KeyToken(reader, assembly);
        var keyToken = token is null ? ""
            : $"keyToken := {Packed(Encoding.ASCII.GetBytes(token), "      ")},\n    ";
        string Entries(SortedDictionary<int, byte[]> entries) => Packed(entries.Select(entry =>
            $"({entry.Key}, {Packed(entry.Value, "         ")})"), "      ", oneEach: true);
        return $$"""
            { identity := "{{Identity(reader, assembly)}}",
                {{keyToken}}tableHeader :=
                  {{Packed(header, "      ")}},
                header := .ofCounts {{heapSizes}}
                  {{Packed(counts, "      ")}},
                assemblyRow :=
                  {{Packed(row, "      ")}},
                strings :=
                  {{Entries(strings)}},
                blobs :=
                  {{Entries(blobs)}} }
            """;
    }

    /// <summary>
    /// The public key token of an Assembly row as Lean spells it: the last eight bytes of the key's SHA-1 digest in
    /// reverse when the PublicKey flag is set, the key itself otherwise, and none without a key. The runtime's own
    /// computation refuses keys that are not well-formed strong-name keys, which a synthetic image need not have.
    /// </summary>
    static string? KeyToken(MetadataReader reader, AssemblyDefinition assembly)
    {
        var key = reader.GetBlobBytes(assembly.PublicKey);
        if (key.Length == 0) return null;
        var token = (assembly.Flags & System.Reflection.AssemblyFlags.PublicKey) != 0
            ? System.Security.Cryptography.SHA1.HashData(key)[^8..].Reverse().ToArray() : key;
        return Convert.ToHexStringLower(token);
    }

    /// <summary>The identity of an Assembly row as Lean spells it, with the token of <see cref="KeyToken"/>.</summary>
    static string Identity(MetadataReader reader, AssemblyDefinition assembly)
    {
        var culture = reader.GetString(assembly.Culture);
        return $"{reader.GetString(assembly.Name)}, Version={assembly.Version}, " +
            $"Culture={(culture.Length == 0 ? "neutral" : culture)}, PublicKeyToken={KeyToken(reader, assembly) ?? "null"}";
    }

    /// <summary>The identity of the assembly an image defines, as Lean spells it.</summary>
    internal static string Identity(byte[] file)
    {
        using PEReader pe = new(ImmutableArray.Create(file));
        var reader = pe.GetMetadataReader();
        return Identity(reader, reader.GetAssemblyDefinition());
    }

    /// <summary>
    /// Keys for heap offsets, as the extractor numbers an assembly block: 0 for offset 0, and the rank from 1 of each
    /// other entry's bytes in hexadecimal order. The entries are keyed the same way.
    /// </summary>
    static (Dictionary<int, int> Keys, SortedDictionary<int, byte[]> Entries) Ranked(int[] offsets,
        Func<int, byte[]> entry)
    {
        var keys = new Dictionary<int, int> { [0] = 0 };
        SortedDictionary<int, byte[]> entries = [];
        var rank = 1;
        foreach (var offset in offsets.Where(offset => offset != 0).Distinct()
                     .OrderBy(offset => Convert.ToHexString(entry(offset)), StringComparer.Ordinal))
        {
            keys[offset] = rank;
            entries[rank++] = entry(offset);
        }
        if (offsets.Contains(0)) entries[0] = entry(0);
        return (keys, entries);
    }

    /// <summary>A Lean list of bytes, wrapped so that no line is wider than a generated line may be.</summary>
    static string Packed(IEnumerable<byte> bytes, string indent) =>
        Packed(bytes.Select(value => value.ToString(System.Globalization.CultureInfo.InvariantCulture)), indent);

    /// <summary>A Lean list of items, wrapped below the line width, or one item to a line.</summary>
    static string Packed(IEnumerable<string> items, string indent, bool oneEach = false)
    {
        List<string> lines = [];
        var line = new StringBuilder();
        foreach (var item in items)
        {
            if (line.Length > 0 && (oneEach || indent.Length + line.Length + item.Length + 3 > LeanLineWidth))
            {
                lines.Add(line.Append(',').ToString());
                line.Clear();
            }
            else if (line.Length > 0) line.Append(", ");
            line.Append(item);
        }
        if (line.Length > 0) lines.Add(line.ToString());
        return "[" + string.Join("\n" + indent + " ", lines) + "]";
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
