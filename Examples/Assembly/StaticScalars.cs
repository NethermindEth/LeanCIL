namespace Examples;

public enum StaticSigned : sbyte { Negative = -7 }
public enum StaticUnsigned : ulong { High = 0x8000000000000001 }

public static class StaticScalars
{
    public static readonly sbyte SignedByte = -128;
    public static readonly byte Byte = 255;
    public static readonly short SignedShort = -32768;
    public static readonly ushort Short = 65535;
    public static readonly int SignedInt = int.MinValue;
    public static readonly uint Int = uint.MaxValue;
    public static readonly long SignedLong = long.MinValue;
    public static readonly ulong Long = ulong.MaxValue;
    public static readonly nint SignedNative = -1;
    public static readonly nuint Native = unchecked((nuint)0x8000000000000001);
    public static readonly bool Boolean = true;
    public static readonly char Character = '\uffff';
    public static readonly StaticSigned SignedEnum = StaticSigned.Negative;
    public static readonly StaticUnsigned UnsignedEnum = StaticUnsigned.High;
    public static readonly int Called = Identity(-7);
    public static readonly int Copied = Called;

    static int Identity(int value) => value;
    public static sbyte ReadSignedByte() => SignedByte;
    public static byte ReadByte() => Byte;
    public static short ReadSignedShort() => SignedShort;
    public static ushort ReadShort() => Short;
    public static int ReadSignedInt() => SignedInt;
    public static uint ReadInt() => Int;
    public static long ReadSignedLong() => SignedLong;
    public static ulong ReadLong() => Long;
    public static nint ReadSignedNative() => SignedNative;
    public static nuint ReadNative() => Native;
    public static bool ReadBoolean() => Boolean;
    public static char ReadCharacter() => Character;
    public static StaticSigned ReadSignedEnum() => SignedEnum;
    public static StaticUnsigned ReadUnsignedEnum() => UnsignedEnum;
    public static int ReadCalled() => Called;
    public static int ReadCopied() => Copied;
}
