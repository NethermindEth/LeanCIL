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

    internal MetadataImage(PEReader image)
    {
        Reader = image.GetMetadataReader();
        bytes = image.GetMetadata().GetContent();
    }

    internal MetadataReader Reader { get; }

    internal int Count(int table) => Reader.GetTableRowCount((TableIndex)table);

    Dictionary<int, uint>? nesting;

    /// <summary>The NestedClass row of a nested type, from a map of the table built on first use.</summary>
    internal uint? NestedClassRow(int typeRow)
    {
        if (nesting is null)
        {
            nesting = [];
            var width = Reader.GetTableRowSize(TableIndex.NestedClass) / 2;
            for (var row = 1; row <= Count(0x29); row++)
            {
                var bytes = Row(0x29000000 + (uint)row);
                var nested = 0;
                for (var index = width - 1; index >= 0; index--) nested = nested * 256 + bytes[index];
                nesting.TryAdd(nested, 0x29000000 + (uint)row);
            }
        }
        return nesting.TryGetValue(typeRow, out var found) ? found : null;
    }

    /// <summary>The bytes of the row a token names.</summary>
    internal byte[] Row(uint token)
    {
        var table = (TableIndex)(token >> 24);
        var size = Reader.GetTableRowSize(table);
        var at = Reader.GetTableMetadataOffset(table) + ((int)(token & 0xFFFFFF) - 1) * size;
        var row = bytes.AsSpan(at, size).ToArray();
        // A MethodDef row's first column is the body's address, which moves whenever an earlier body changes
        // size; the carried row has it zeroed so that no method's evidence depends on another method's body.
        if (table == TableIndex.MethodDef) row.AsSpan(0, sizeof(uint)).Clear();
        return row;
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
        var counts = Enumerable.Range(0, 64).Where(table => Count(table) > 0)
            .Select(table => string.Create(CultureInfo.InvariantCulture, $"({table}, {Count(table)})"));
        return string.Create(CultureInfo.InvariantCulture,
            $".ofCounts {TableHeader()[HeapSizesOffset]} [{string.Join(", ", counts)}]");
    }

    // The `HeapSizes` byte's offset in the table stream header (II.24.2.6).
    const int HeapSizesOffset = 6;

    /// <summary>The table stream header: the bytes from the reserved word through the last row count.</summary>
    internal byte[] TableHeader()
    {
        var tables = Enumerable.Range(0, 64).Where(table => Count(table) > 0).ToArray();
        var length = 24 + 4 * tables.Length;
        var start = tables.Min(table => Reader.GetTableMetadataOffset((TableIndex)table)) - length;
        var header = bytes.AsSpan(start, length).ToArray();
        if (header[4] != 2 || header[5] != 0)
            throw new InvalidDataException("The metadata table stream header was not found where its tables imply.");
        return header;
    }
}
