using System.Runtime.CompilerServices;

namespace Examples;

public enum Signed8 : sbyte { Zero, One }
public enum Unsigned8 : byte { Zero, One }
public enum Signed16 : short { Zero, One }
public enum Unsigned16 : ushort { Zero, One }
public enum Signed32 : int { Zero, One }
public enum Unsigned32 : uint { Zero, One }
public enum Signed64 : long { Zero, One }
public enum Unsigned64 : ulong { Zero, One }

public struct EnumRecord
{
    public Signed8 Tag;
    public Unsigned64 Flags;
}

public static class Enums
{
    public static Signed8 IdentityS8(Signed8 value) => value;
    public static Unsigned8 IdentityU8(Unsigned8 value) => value;
    public static Signed16 IdentityS16(Signed16 value) => value;
    public static Unsigned16 IdentityU16(Unsigned16 value) => value;
    public static Signed32 IdentityS32(Signed32 value) => value;
    public static Unsigned32 IdentityU32(Unsigned32 value) => value;
    public static Signed64 IdentityS64(Signed64 value) => value;
    public static Unsigned64 IdentityU64(Unsigned64 value) => value;

    public static Unsigned64 SetFlag(Unsigned64 value) => value | Unsigned64.One;
    public static Unsigned64 WrongSetFlag(Unsigned64 value) => value & Unsigned64.One;

    public static int Branch(Signed8 value) => value == Signed8.One ? 7 : -3;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static Signed16 ThroughCall(Signed16 value) => IdentityS16(value);

    public static Signed8 Field(Signed8 value)
    {
        var record = new EnumRecord { Tag = value };
        return Read(ref record);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static Signed8 Read(ref EnumRecord record) => record.Tag;

    public static Unsigned64 Local(Unsigned64 value)
    {
        var local = Unsigned64.Zero;
        Assign(ref local, value);
        return local;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static void Assign(ref Unsigned64 destination, Unsigned64 value) => destination = value;
}
