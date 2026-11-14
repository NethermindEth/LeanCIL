using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Globalization;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;

namespace Nethermind.LeanCIL;

/// <summary>
/// The metadata tables and heaps of one module image, read with System.Reflection.Metadata: the raw bytes of
/// a table row or heap entry at the position the image gives it.
/// </summary>
internal sealed class MetadataImage
{
    readonly ImmutableArray<byte> bytes;
    byte[]? tableHeader;
    string? decodedHeader;

    internal MetadataImage(PEReader image)
    {
        Reader = image.GetMetadataReader();
        bytes = image.GetMetadata().GetContent();
    }

    internal MetadataReader Reader { get; }

    const int NamePageSize = 256;
    MetadataName?[]?[]? names;

    /// <summary>The exact bytes at a heap offset, materialized only for identity output.</summary>
    internal MetadataName Name(int offset)
    {
        int size = Reader.GetHeapSize(HeapIndex.String);
        if ((uint)offset >= (uint)size) throw new BadImageFormatException("String offset outside its heap");
        names ??= new MetadataName?[(size - 1) / NamePageSize + 1][];
        var page = names[offset / NamePageSize] ??= new MetadataName?[NamePageSize];
        if (page[offset % NamePageSize] is { } name) return name;
        byte[] entry = StringEntry(offset);
        return page[offset % NamePageSize] = MetadataName.FromBytes(entry.AsSpan(0, entry.Length - 1));
    }

    /// <summary>One bounded byte of the raw string heap, including terminators.</summary>
    internal byte StringByte(int offset)
    {
        int size = Reader.GetHeapSize(HeapIndex.String);
        if ((uint)offset >= (uint)size) throw new BadImageFormatException("String offset outside its heap");
        return bytes[Reader.GetHeapMetadataOffset(HeapIndex.String) + offset];
    }

    /// <summary>A raw named row's own columns and its immediate nesting or assembly edge.</summary>
    internal sealed record NamedRow(int Namespace, int Name, uint Parent, uint Assembly);

    readonly SortedDictionary<uint, NamedRow> namedRows = [];

    /// <summary>The immutable raw row; nesting edges are retained without flattening their ancestors.</summary>
    internal NamedRow NamedType(uint token)
    {
        if (namedRows.TryGetValue(token, out var cached)) return cached;
        uint table = token >> 24;
        int number = (int)(token & 0xffffff);
        if (table is not (1 or 2) || number == 0 || number > Count((int)table))
            throw new InvalidDataException("Type identity requires a valid TypeDef or TypeRef row");
        StringHandle space;
        StringHandle name;
        uint parent = 0;
        uint assembly = 0;
        if (table == 2)
        {
            var row = Reader.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle(number));
            space = row.Namespace;
            name = row.Name;
            if (NestedClassRow(number) is { } nestingToken)
            {
                byte[] nestingRow = Row(nestingToken);
                int width = nestingRow.Length / 2;
                uint enclosing = 0;
                for (int index = nestingRow.Length - 1; index >= width; index--)
                    enclosing = enclosing * 256 + nestingRow[index];
                if (enclosing == 0 || enclosing > Count(2))
                    throw new InvalidDataException("Nested type has an invalid enclosing row");
                parent = 0x02000000 | enclosing;
            }
            else assembly = 0x20000001;
        }
        else
        {
            var row = Reader.GetTypeReference(MetadataTokens.TypeReferenceHandle(number));
            space = row.Namespace;
            name = row.Name;
            uint scope = (uint)MetadataTokens.GetToken(row.ResolutionScope);
            if (row.ResolutionScope.IsNil) throw new InvalidDataException("Type reference has no scope");
            if (scope >> 24 == 1) parent = scope;
            else if (scope >> 24 == 0x23 && (scope & 0xffffff) <= Count(0x23)) assembly = scope;
            else if (scope == 1) assembly = 0x20000001;
            else throw new InvalidDataException("Type reference has an unsupported resolution scope");
        }
        cached = new(MetadataTokens.GetHeapOffset(space), MetadataTokens.GetHeapOffset(name), parent, assembly);
        namedRows.Add(token, cached);
        return cached;
    }

    readonly Dictionary<uint, AssemblyName?> assemblyIdentities = [];
    readonly SortedDictionary<uint, AssemblyName.Columns?> assemblyColumns = [];
    readonly SortedDictionary<(int Offset, bool FullKey), AssemblyName.KeyColumns> signingKeys = [];

    internal long SigningBytes { get; private set; }
    internal long SigningReads { get; private set; }

    internal void RecordSigningBytes(int count) { SigningBytes += count; SigningReads++; }

    /// <summary>The normalized signing column for a raw blob and its full-key or token interpretation.</summary>
    internal AssemblyName.KeyColumns SigningKey(BlobHandle handle, bool fullKey)
    {
        var key = (MetadataTokens.GetHeapOffset(handle), fullKey);
        if (signingKeys.TryGetValue(key, out var columns)) return columns;
        columns = AssemblyName.ReadKey(this, handle, fullKey);
        signingKeys.Add(key, columns);
        return columns;
    }

    internal AssemblyName.Columns? AssemblyColumns(uint token)
    {
        if (assemblyColumns.TryGetValue(token, out var columns)) return columns;
        assemblyColumns.Add(token, columns = AssemblyName.ReadColumns(this, token));
        return columns;
    }

    /// <summary>The immutable identity of an assembly row in this image, including invalid null results.</summary>
    internal AssemblyName? AssemblyIdentity(uint token)
    {
        if (assemblyIdentities.TryGetValue(token, out var identity)) return identity;
        identity = AssemblyName.Read(this, token);
        assemblyIdentities.Add(token, identity);
        return identity;
    }

    /// <summary>A top-level type's raw name columns and resolution scope.
    /// Definitions have no reference scope.</summary>
    internal sealed record TypeNameRow(TypeLevel Level, uint ResolutionScope);

    readonly Dictionary<uint, TypeNameRow?> typeNames = [];

    /// <summary>The cached raw name of a top-level TypeDef or TypeRef; nested types have no top-level name.</summary>
    internal TypeNameRow? TopLevelTypeName(uint token)
    {
        if (typeNames.TryGetValue(token, out var cached)) return cached;
        uint table = token >> 24;
        int rowNumber = (int)(token & 0xffffff);
        if (table is not (1 or 2) || rowNumber == 0 || rowNumber > Count((int)table))
            throw new InvalidDataException("Modifier identity requires a valid TypeDef or TypeRef row");
        uint scope = 0;
        bool nested;
        if (table == 1)
        {
            var row = Reader.GetTypeReference(MetadataTokens.TypeReferenceHandle(rowNumber));
            scope = (uint)MetadataTokens.GetToken(row.ResolutionScope);
            nested = row.ResolutionScope.Kind == HandleKind.TypeReference;
        }
        else nested = NestedClassRow(rowNumber) is not null;
        var name = nested ? null : new TypeNameRow(
            IdentityRows.Level(this, new Mono.Cecil.MetadataToken(token)), scope);
        typeNames.Add(token, name);
        return name;
    }

    internal int Count(int table) => Reader.GetTableRowCount((TableIndex)table);

    Dictionary<int, uint>? nesting;

    /// <summary>The NestedClass row of a nested type, from a map of the table built on first use.</summary>
    internal uint? NestedClassRow(int typeRow)
    {
        if (nesting is null)
        {
            var entries = new Dictionary<int, uint>();
            var width = Reader.GetTableRowSize(TableIndex.NestedClass) / 2;
            for (var row = 1; row <= Count(0x29); row++)
            {
                var bytes = Row(0x29000000 + (uint)row);
                var nested = 0;
                for (var index = width - 1; index >= 0; index--) nested = nested * 256 + bytes[index];
                if (!entries.TryAdd(nested, 0x29000000 + (uint)row))
                    throw new InvalidDataException("Type has duplicate NestedClass rows");
            }
            nesting = entries;
        }
        return nesting.TryGetValue(typeRow, out var found) ? found : null;
    }

    /// <summary>The bytes of the row a token names.</summary>
    internal byte[] Row(uint token)
    {
        var table = (TableIndex)(token >> 24);
        var size = Reader.GetTableRowSize(table);
        var at = Reader.GetTableMetadataOffset(table) + ((int)(token & 0xFFFFFF) - 1) * size;
        return bytes.AsSpan(at, size).ToArray();
    }

    /// <summary>The first <c>Field</c> row of a <c>TypeDef</c> row: its <c>FieldList</c> column.</summary>
    internal uint FieldList(byte[] typeDefRow)
    {
        var width = Reader.GetTableRowCount(TableIndex.Field) < 0x10000 ? 2 : 4;
        var methodWidth = Reader.GetTableRowCount(TableIndex.MethodDef) < 0x10000 ? 2 : 4;
        var at = typeDefRow.Length - width - methodWidth;
        return width == 2 ? BitConverter.ToUInt16(typeDefRow, at) : BitConverter.ToUInt32(typeDefRow, at);
    }

    /// <summary>A <c>#Strings</c> entry through its terminating zero.</summary>
    internal byte[] StringEntry(int offset)
    {
        var size = Reader.GetHeapSize(HeapIndex.String);
        if ((uint)offset >= (uint)size) throw new BadImageFormatException("String offset outside its heap");
        var start = Reader.GetHeapMetadataOffset(HeapIndex.String) + offset;
        var length = bytes.AsSpan(start, size - offset).IndexOf((byte)0);
        if (length < 0) throw new BadImageFormatException("String entry without a terminator in its heap");
        return bytes.AsSpan(start, length + 1).ToArray();
    }

    /// <summary>A <c>#Blob</c> or <c>#US</c> entry with its compressed length.</summary>
    internal byte[] SizedEntry(HeapIndex heap, int offset)
    {
        if (heap is not (HeapIndex.Blob or HeapIndex.UserString))
            throw new BadImageFormatException("Sized entry requires a blob or user-string heap");
        var size = Reader.GetHeapSize(heap);
        if ((uint)offset >= (uint)size) throw new BadImageFormatException("Sized offset outside its heap");
        var start = Reader.GetHeapMetadataOffset(heap) + offset;
        var first = bytes[start];
        var header = first switch
        {
            < 0x80 => 1,
            < 0xC0 => 2,
            < 0xE0 => 4,
            _ => throw new BadImageFormatException("Invalid compressed length prefix")
        };
        var remaining = size - offset;
        if (header > remaining) throw new BadImageFormatException("Compressed length crosses its heap boundary");
        var length = header switch
        {
            1 => first,
            2 => ((first & 0x3F) << 8) | bytes[start + 1],
            _ => ((first & 0x1F) << 24) | (bytes[start + 1] << 16) | (bytes[start + 2] << 8) | bytes[start + 3]
        };
        if (length > remaining - header) throw new BadImageFormatException("Sized entry crosses its heap boundary");
        return bytes.AsSpan(start, header + length).ToArray();
    }

    /// <summary>
    /// The decoded table stream header as a Lean <c>TableHeader</c>: the heap sizes and each present table's row
    /// count, in table order. Lean proves once per assembly that <see cref="TableHeader"/> decodes to it.
    /// </summary>
    internal string DecodedHeader()
    {
        if (decodedHeader is not null) return decodedHeader;
        var header = CachedTableHeader();
        ulong valid = BinaryPrimitives.ReadUInt64LittleEndian(header.AsSpan(8));
        var counts = new List<string>();
        int countOffset = 24;
        for (int table = 0; table < 64; table++)
        {
            if ((valid & (1UL << table)) == 0) continue;
            uint count = BinaryPrimitives.ReadUInt32LittleEndian(header.AsSpan(countOffset));
            counts.Add(string.Create(CultureInfo.InvariantCulture, $"({table}, {count})"));
            countOffset += sizeof(uint);
        }
        return decodedHeader = string.Create(CultureInfo.InvariantCulture,
            $".ofCounts {header[HeapSizesOffset]} [{string.Join(", ", counts)}]");
    }

    // The `HeapSizes` byte's offset in the table stream header (II.24.2.6).
    const int HeapSizesOffset = 6;

    /// <summary>The table stream header: the bytes from the reserved word through the last row count.</summary>
    internal byte[] TableHeader() => [.. CachedTableHeader()];

    /// <summary>The heap index width recorded in the table stream, including explicitly wide small heaps.</summary>
    internal int HeapIndexWidth(HeapIndex heap)
    {
        var mask = heap switch
        {
            HeapIndex.String => 1,
            HeapIndex.Blob => 4,
            _ => throw new ArgumentOutOfRangeException(nameof(heap))
        };
        return (CachedTableHeader()[HeapSizesOffset] & mask) == 0 ? 2 : 4;
    }

    byte[] CachedTableHeader() => tableHeader ??= ReadTableHeader(bytes.AsSpan());

    /// <summary>The original table header located by the metadata root's stream directory.</summary>
    internal static byte[] ReadTableHeader(ReadOnlySpan<byte> metadata)
    {
        RequireRange(metadata, 0, 16);
        if (BinaryPrimitives.ReadUInt32LittleEndian(metadata) != 0x424A5342)
            throw new BadImageFormatException("Invalid metadata root signature");
        uint versionLength = BinaryPrimitives.ReadUInt32LittleEndian(metadata[12..]);
        if (versionLength > int.MaxValue - 16)
            throw new BadImageFormatException("Metadata version length is too large");
        int directory = 16 + (int)versionLength;
        RequireRange(metadata, directory, 4);
        int streamCount = BinaryPrimitives.ReadUInt16LittleEndian(metadata[(directory + 2)..]);
        directory += 4;
        byte[]? found = null;
        for (int stream = 0; stream < streamCount; stream++)
        {
            RequireRange(metadata, directory, 8);
            uint offset = BinaryPrimitives.ReadUInt32LittleEndian(metadata[directory..]);
            uint size = BinaryPrimitives.ReadUInt32LittleEndian(metadata[(directory + 4)..]);
            directory += 8;
            int nameLength = metadata[directory..].IndexOf((byte)0);
            if (nameLength < 0 || nameLength >= 32)
                throw new BadImageFormatException("Invalid metadata stream name");
            var name = metadata.Slice(directory, nameLength);
            int paddedLength = (nameLength + 4) & ~3;
            RequireRange(metadata, directory, paddedLength);
            directory += paddedLength;
            if (!name.SequenceEqual("#~"u8) && !name.SequenceEqual("#-"u8)) continue;
            if (found is not null) throw new BadImageFormatException("Duplicate metadata table stream");
            if (offset > int.MaxValue || size > int.MaxValue)
                throw new BadImageFormatException("Metadata table stream is too large");
            RequireRange(metadata, (int)offset, (int)size);
            var tableStream = metadata.Slice((int)offset, (int)size);
            RequireRange(tableStream, 0, 24);
            if (tableStream[4] != 2 || tableStream[5] != 0 || tableStream[HeapSizesOffset] >= 8)
                throw new BadImageFormatException("Unsupported metadata table stream header");
            ulong valid = BinaryPrimitives.ReadUInt64LittleEndian(tableStream[8..]);
            int length = 24 + sizeof(uint) * System.Numerics.BitOperations.PopCount(valid);
            RequireRange(tableStream, 0, length);
            found = tableStream[..length].ToArray();
        }
        return found ?? throw new BadImageFormatException("Missing metadata table stream");
    }

    static void RequireRange(ReadOnlySpan<byte> source, int offset, int length)
    {
        if (offset < 0 || length < 0 || offset > source.Length || length > source.Length - offset)
            throw new BadImageFormatException("Metadata header crosses its container boundary");
    }
}
