namespace Examples;

public enum AllocationTag : byte { One = 1 }

public static class PrimitiveArrays
{
    public static int Length(int[] values) => values.Length;
    public static sbyte ReadSByte(sbyte[] values, int index) => values[index];
    public static byte ReadByte(byte[] values, int index) => values[index];
    public static short ReadInt16(short[] values, int index) => values[index];
    public static ushort ReadUInt16(ushort[] values, int index) => values[index];
    public static int ReadInt32(int[] values, int index) => values[index];
    public static uint ReadUInt32(uint[] values, int index) => values[index];
    public static long ReadInt64(long[] values, int index) => values[index];
    public static ulong ReadUInt64(ulong[] values, int index) => values[index];
    public static nint ReadIntPtr(nint[] values, int index) => values[index];
    public static nuint ReadUIntPtr(nuint[] values, int index) => values[index];
    public static bool ReadBoolean(bool[] values, int index) => values[index];
    public static char ReadChar(char[] values, int index) => values[index];

    public static void WriteSByte(sbyte[] values, int index, sbyte value) => values[index] = value;
    public static void WriteByte(byte[] values, int index, byte value) => values[index] = value;
    public static void WriteInt16(short[] values, int index, short value) => values[index] = value;
    public static void WriteUInt16(ushort[] values, int index, ushort value) => values[index] = value;
    public static void WriteInt32(int[] values, int index, int value) => values[index] = value;
    public static void WriteUInt32(uint[] values, int index, uint value) => values[index] = value;
    public static void WriteInt64(long[] values, int index, long value) => values[index] = value;
    public static void WriteUInt64(ulong[] values, int index, ulong value) => values[index] = value;
    public static void WriteIntPtr(nint[] values, int index, nint value) => values[index] = value;
    public static void WriteUIntPtr(nuint[] values, int index, nuint value) => values[index] = value;
    public static void WriteBoolean(bool[] values, int index, bool value) => values[index] = value;
    public static void WriteChar(char[] values, int index, char value) => values[index] = value;

    public static int ReadHelper(int[] values, int index) => ReadInt32(values, index);
    public static T ReadGeneric<T>(T[] values, int index) => values[index];
    public static void WriteGeneric<T>(T[] values, int index, T value) => values[index] = value;
    public static int ReadGenericHelper(int[] values, int index) => ReadGeneric(values, index);
    public static int WriteGenericHelper(int[] values, int index, int value)
    {
        WriteGeneric(values, index, value);
        return ReadGeneric(values, index);
    }
    public static int[] Identity(int[] values) => values;
    public static int ReadAlias(int[] values, int index, int value)
    {
        var alias = values;
        WriteInt32(alias, index, value);
        return ReadInt32(values, index);
    }

    public static int[] Allocate(int length) => new int[length];
    public static byte[] AllocateBytes(int length) => new byte[length];
    public static short[] AllocateShorts(int length) => new short[length];
    public static long[] AllocateLongs(int length) => new long[length];
    public static PackedLeaf[] AllocatePacked(int length) => new PackedLeaf[length];
    public static NestedRecord[] AllocateNested(int length) => new NestedRecord[length];
    public static System.Runtime.Intrinsics.Vector256<ulong>[] AllocateVector(int length) =>
        new System.Runtime.Intrinsics.Vector256<ulong>[length];
    public static int AllocatePackedAndWrite(int length, int index, int value)
    {
        var values = AllocatePacked(length);
        values[index].Value = (uint)value;
        return (int)values[index].Value;
    }
    public static int AllocateAndWrite(int length, int index, int value)
    {
        var values = Allocate(length);
        WriteInt32(values, index, value);
        return ReadInt32(values, index);
    }

    public static Signed8[] AllocateSigned8(int length) => new Signed8[length];
    public static Unsigned8[] AllocateUnsigned8(int length) => new Unsigned8[length];
    public static Signed16[] AllocateSigned16(int length) => new Signed16[length];
    public static Unsigned16[] AllocateUnsigned16(int length) => new Unsigned16[length];
    public static Signed32[] AllocateSigned32(int length) => new Signed32[length];
    public static Unsigned32[] AllocateUnsigned32(int length) => new Unsigned32[length];
    public static Signed64[] AllocateSigned64(int length) => new Signed64[length];
    public static Unsigned64[] AllocateUnsigned64(int length) => new Unsigned64[length];
    public static AllocationTag[] AllocateUnnamedZero(int length) => new AllocationTag[length];

    public static float[] AllocateSingles(int length) => new float[length];
    public static object ReadObject(object[] values, int index) => values[index];
    public static float ReadSingle(float[] values, int index) => values[index];
    public static int[] ReadJagged(int[][] values, int index) => values[index];
    public static int ReadRectangular(int[,] values, int row, int column) => values[row, column];
}
