using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Examples;

static class UnsafeLayouts
{
    public static int Size0() => Unsafe.SizeOf<bool>();
    public static ref bool Add0int(ref bool value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure0int(int count)
    {
        var buffer = new bool[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref bool Add0nint(ref bool value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure0nint(nint count)
    {
        var buffer = new bool[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref bool Add0nuint(ref bool value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure0nuint(nuint count)
    {
        var buffer = new bool[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size1() => Unsafe.SizeOf<char>();
    public static ref char Add1int(ref char value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure1int(int count)
    {
        var buffer = new char[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref char Add1nint(ref char value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure1nint(nint count)
    {
        var buffer = new char[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref char Add1nuint(ref char value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure1nuint(nuint count)
    {
        var buffer = new char[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size2() => Unsafe.SizeOf<sbyte>();
    public static ref sbyte Add2int(ref sbyte value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure2int(int count)
    {
        var buffer = new sbyte[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref sbyte Add2nint(ref sbyte value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure2nint(nint count)
    {
        var buffer = new sbyte[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref sbyte Add2nuint(ref sbyte value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure2nuint(nuint count)
    {
        var buffer = new sbyte[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size3() => Unsafe.SizeOf<byte>();
    public static ref byte Add3int(ref byte value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure3int(int count)
    {
        var buffer = new byte[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref byte Add3nint(ref byte value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure3nint(nint count)
    {
        var buffer = new byte[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref byte Add3nuint(ref byte value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure3nuint(nuint count)
    {
        var buffer = new byte[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size4() => Unsafe.SizeOf<short>();
    public static ref short Add4int(ref short value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure4int(int count)
    {
        var buffer = new short[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref short Add4nint(ref short value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure4nint(nint count)
    {
        var buffer = new short[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref short Add4nuint(ref short value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure4nuint(nuint count)
    {
        var buffer = new short[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size5() => Unsafe.SizeOf<ushort>();
    public static ref ushort Add5int(ref ushort value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure5int(int count)
    {
        var buffer = new ushort[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref ushort Add5nint(ref ushort value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure5nint(nint count)
    {
        var buffer = new ushort[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref ushort Add5nuint(ref ushort value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure5nuint(nuint count)
    {
        var buffer = new ushort[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size6() => Unsafe.SizeOf<int>();
    public static ref int Add6int(ref int value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure6int(int count)
    {
        var buffer = new int[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref int Add6nint(ref int value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure6nint(nint count)
    {
        var buffer = new int[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref int Add6nuint(ref int value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure6nuint(nuint count)
    {
        var buffer = new int[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size7() => Unsafe.SizeOf<uint>();
    public static ref uint Add7int(ref uint value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure7int(int count)
    {
        var buffer = new uint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref uint Add7nint(ref uint value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure7nint(nint count)
    {
        var buffer = new uint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref uint Add7nuint(ref uint value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure7nuint(nuint count)
    {
        var buffer = new uint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size8() => Unsafe.SizeOf<long>();
    public static ref long Add8int(ref long value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure8int(int count)
    {
        var buffer = new long[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref long Add8nint(ref long value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure8nint(nint count)
    {
        var buffer = new long[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref long Add8nuint(ref long value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure8nuint(nuint count)
    {
        var buffer = new long[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size9() => Unsafe.SizeOf<ulong>();
    public static ref ulong Add9int(ref ulong value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure9int(int count)
    {
        var buffer = new ulong[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref ulong Add9nint(ref ulong value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure9nint(nint count)
    {
        var buffer = new ulong[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref ulong Add9nuint(ref ulong value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure9nuint(nuint count)
    {
        var buffer = new ulong[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size10() => Unsafe.SizeOf<nint>();
    public static ref nint Add10int(ref nint value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure10int(int count)
    {
        var buffer = new nint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref nint Add10nint(ref nint value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure10nint(nint count)
    {
        var buffer = new nint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref nint Add10nuint(ref nint value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure10nuint(nuint count)
    {
        var buffer = new nint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size11() => Unsafe.SizeOf<nuint>();
    public static ref nuint Add11int(ref nuint value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure11int(int count)
    {
        var buffer = new nuint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref nuint Add11nint(ref nuint value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure11nint(nint count)
    {
        var buffer = new nuint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref nuint Add11nuint(ref nuint value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure11nuint(nuint count)
    {
        var buffer = new nuint[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size12() => Unsafe.SizeOf<Signed8>();
    public static ref Signed8 Add12int(ref Signed8 value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure12int(int count)
    {
        var buffer = new Signed8[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Signed8 Add12nint(ref Signed8 value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure12nint(nint count)
    {
        var buffer = new Signed8[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Signed8 Add12nuint(ref Signed8 value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure12nuint(nuint count)
    {
        var buffer = new Signed8[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size13() => Unsafe.SizeOf<Unsigned64>();
    public static ref Unsigned64 Add13int(ref Unsigned64 value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure13int(int count)
    {
        var buffer = new Unsigned64[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Unsigned64 Add13nint(ref Unsigned64 value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure13nint(nint count)
    {
        var buffer = new Unsigned64[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Unsigned64 Add13nuint(ref Unsigned64 value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure13nuint(nuint count)
    {
        var buffer = new Unsigned64[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size14() => Unsafe.SizeOf<PackedLeaf>();
    public static ref PackedLeaf Add14int(ref PackedLeaf value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure14int(int count)
    {
        var buffer = new PackedLeaf[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref PackedLeaf Add14nint(ref PackedLeaf value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure14nint(nint count)
    {
        var buffer = new PackedLeaf[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref PackedLeaf Add14nuint(ref PackedLeaf value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure14nuint(nuint count)
    {
        var buffer = new PackedLeaf[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size15() => Unsafe.SizeOf<NestedRecord>();
    public static ref NestedRecord Add15int(ref NestedRecord value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure15int(int count)
    {
        var buffer = new NestedRecord[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref NestedRecord Add15nint(ref NestedRecord value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure15nint(nint count)
    {
        var buffer = new NestedRecord[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref NestedRecord Add15nuint(ref NestedRecord value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure15nuint(nuint count)
    {
        var buffer = new NestedRecord[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size16() => Unsafe.SizeOf<Packet>();
    public static ref Packet Add16int(ref Packet value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure16int(int count)
    {
        var buffer = new Packet[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Packet Add16nint(ref Packet value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure16nint(nint count)
    {
        var buffer = new Packet[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Packet Add16nuint(ref Packet value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure16nuint(nuint count)
    {
        var buffer = new Packet[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size17() => Unsafe.SizeOf<Vector128<ulong>>();
    public static ref Vector128<ulong> Add17int(ref Vector128<ulong> value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure17int(int count)
    {
        var buffer = new Vector128<ulong>[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Vector128<ulong> Add17nint(ref Vector128<ulong> value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure17nint(nint count)
    {
        var buffer = new Vector128<ulong>[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Vector128<ulong> Add17nuint(ref Vector128<ulong> value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure17nuint(nuint count)
    {
        var buffer = new Vector128<ulong>[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

    public static int Size18() => Unsafe.SizeOf<Vector256<ulong>>();
    public static ref Vector256<ulong> Add18int(ref Vector256<ulong> value, int count) => ref Unsafe.Add(ref value, count);
    public static long Measure18int(int count)
    {
        var buffer = new Vector256<ulong>[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Vector256<ulong> Add18nint(ref Vector256<ulong> value, nint count) => ref Unsafe.Add(ref value, count);
    public static long Measure18nint(nint count)
    {
        var buffer = new Vector256<ulong>[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }
    public static ref Vector256<ulong> Add18nuint(ref Vector256<ulong> value, nuint count) => ref Unsafe.Add(ref value, count);
    public static long Measure18nuint(nuint count)
    {
        var buffer = new Vector256<ulong>[4];
        return Unsafe.ByteOffset(ref buffer[0], ref Unsafe.Add(ref buffer[0], count));
    }

}
