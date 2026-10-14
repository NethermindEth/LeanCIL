using System.Runtime.InteropServices;

namespace Examples;

internal struct Record
{
    public byte Tag;
    public uint Value;
}

[StructLayout(LayoutKind.Sequential, Pack = 1)]
internal struct PackedRecord
{
    public byte Tag;
    public ulong Value;
    public ushort Flags;
}

internal static class Sequential
{
    public static uint ReadWrite(ref Record record, uint value)
    {
        record.Value = value;
        return record.Value;
    }

    public static ulong Packed(ulong value)
    {
        PackedRecord record = default;
        record.Tag = 3;
        record.Value = value;
        record.Flags = 7;
        return record.Value;
    }

    public static unsafe int RecordSize() => sizeof(Record);
    public static unsafe int PackedSize() => sizeof(PackedRecord);
}
