using System;
using System.Buffers.Binary;

namespace Examples;

public static class BinarySpans
{
    public static ulong ReadLittle(ReadOnlySpan<byte> source) => unchecked(
        (ulong)BinaryPrimitives.ReadInt16LittleEndian(source) +
        3UL * BinaryPrimitives.ReadUInt16LittleEndian(source) +
        5UL * (ulong)BinaryPrimitives.ReadInt32LittleEndian(source) +
        7UL * BinaryPrimitives.ReadUInt32LittleEndian(source) +
        11UL * (ulong)BinaryPrimitives.ReadInt64LittleEndian(source) +
        13UL * BinaryPrimitives.ReadUInt64LittleEndian(source));

    public static ulong ReadBig(ReadOnlySpan<byte> source) => unchecked(
        (ulong)BinaryPrimitives.ReadInt16BigEndian(source) +
        3UL * BinaryPrimitives.ReadUInt16BigEndian(source) +
        5UL * (ulong)BinaryPrimitives.ReadInt32BigEndian(source) +
        7UL * BinaryPrimitives.ReadUInt32BigEndian(source) +
        11UL * (ulong)BinaryPrimitives.ReadInt64BigEndian(source) +
        13UL * BinaryPrimitives.ReadUInt64BigEndian(source));

    public static ulong TryReadLittle(ReadOnlySpan<byte> source)
    {
        var flags = BinaryPrimitives.TryReadInt16LittleEndian(source, out var signed16) ? 1UL : 0;
        flags += BinaryPrimitives.TryReadUInt16LittleEndian(source, out var unsigned16) ? 2UL : 0;
        flags += BinaryPrimitives.TryReadInt32LittleEndian(source, out var signed32) ? 4UL : 0;
        flags += BinaryPrimitives.TryReadUInt32LittleEndian(source, out var unsigned32) ? 8UL : 0;
        flags += BinaryPrimitives.TryReadInt64LittleEndian(source, out var signed64) ? 16UL : 0;
        flags += BinaryPrimitives.TryReadUInt64LittleEndian(source, out var unsigned64) ? 32UL : 0;
        return unchecked(flags + (ulong)signed16 + 3UL * unsigned16 + 5UL * (ulong)signed32 +
            7UL * unsigned32 + 11UL * (ulong)signed64 + 13UL * unsigned64);
    }

    public static ulong TryReadBig(ReadOnlySpan<byte> source)
    {
        var flags = BinaryPrimitives.TryReadInt16BigEndian(source, out var signed16) ? 1UL : 0;
        flags += BinaryPrimitives.TryReadUInt16BigEndian(source, out var unsigned16) ? 2UL : 0;
        flags += BinaryPrimitives.TryReadInt32BigEndian(source, out var signed32) ? 4UL : 0;
        flags += BinaryPrimitives.TryReadUInt32BigEndian(source, out var unsigned32) ? 8UL : 0;
        flags += BinaryPrimitives.TryReadInt64BigEndian(source, out var signed64) ? 16UL : 0;
        flags += BinaryPrimitives.TryReadUInt64BigEndian(source, out var unsigned64) ? 32UL : 0;
        return unchecked(flags + (ulong)signed16 + 3UL * unsigned16 + 5UL * (ulong)signed32 +
            7UL * unsigned32 + 11UL * (ulong)signed64 + 13UL * unsigned64);
    }

    public static void WriteLittle(Span<byte> destination)
    {
        BinaryPrimitives.WriteInt16LittleEndian(destination, -1234);
        BinaryPrimitives.WriteUInt16LittleEndian(destination.Slice(2), 0xabcd);
        BinaryPrimitives.WriteInt32LittleEndian(destination.Slice(4), -123456789);
        BinaryPrimitives.WriteUInt32LittleEndian(destination.Slice(8), 0x87654321);
        BinaryPrimitives.WriteInt64LittleEndian(destination.Slice(12), -1234567890123456789);
        BinaryPrimitives.WriteUInt64LittleEndian(destination.Slice(20), 0xfedcba9876543210);
    }

    public static void WriteBig(Span<byte> destination)
    {
        BinaryPrimitives.WriteInt16BigEndian(destination, -1234);
        BinaryPrimitives.WriteUInt16BigEndian(destination.Slice(2), 0xabcd);
        BinaryPrimitives.WriteInt32BigEndian(destination.Slice(4), -123456789);
        BinaryPrimitives.WriteUInt32BigEndian(destination.Slice(8), 0x87654321);
        BinaryPrimitives.WriteInt64BigEndian(destination.Slice(12), -1234567890123456789);
        BinaryPrimitives.WriteUInt64BigEndian(destination.Slice(20), 0xfedcba9876543210);
    }

    public static int TryWriteLittle(Span<byte> destination)
    {
        var flags = BinaryPrimitives.TryWriteInt16LittleEndian(destination, -1234) ? 1 : 0;
        flags += BinaryPrimitives.TryWriteUInt16LittleEndian(destination, 0xabcd) ? 2 : 0;
        flags += BinaryPrimitives.TryWriteInt32LittleEndian(destination, -123456789) ? 4 : 0;
        flags += BinaryPrimitives.TryWriteUInt32LittleEndian(destination, 0x87654321) ? 8 : 0;
        flags += BinaryPrimitives.TryWriteInt64LittleEndian(destination, -1234567890123456789) ? 16 : 0;
        flags += BinaryPrimitives.TryWriteUInt64LittleEndian(destination, 0xfedcba9876543210) ? 32 : 0;
        return flags;
    }

    public static int TryWriteBig(Span<byte> destination)
    {
        var flags = BinaryPrimitives.TryWriteInt16BigEndian(destination, -1234) ? 1 : 0;
        flags += BinaryPrimitives.TryWriteUInt16BigEndian(destination, 0xabcd) ? 2 : 0;
        flags += BinaryPrimitives.TryWriteInt32BigEndian(destination, -123456789) ? 4 : 0;
        flags += BinaryPrimitives.TryWriteUInt32BigEndian(destination, 0x87654321) ? 8 : 0;
        flags += BinaryPrimitives.TryWriteInt64BigEndian(destination, -1234567890123456789) ? 16 : 0;
        flags += BinaryPrimitives.TryWriteUInt64BigEndian(destination, 0xfedcba9876543210) ? 32 : 0;
        return flags;
    }
}
