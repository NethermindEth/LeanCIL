namespace Examples;

public static class IntegerMath
{
    public static sbyte MinInt8(sbyte x, sbyte y) => System.Math.Min(x, y);
    public static sbyte MaxInt8(sbyte x, sbyte y) => System.Math.Max(x, y);
    public static sbyte ClampInt8(sbyte x, sbyte lower, sbyte upper) => System.Math.Clamp(x, lower, upper);
    public static sbyte AbsInt8(sbyte x) => System.Math.Abs(x);
    public static int SignInt8(sbyte x) => System.Math.Sign(x);

    public static byte MinUInt8(byte x, byte y) => System.Math.Min(x, y);
    public static byte MaxUInt8(byte x, byte y) => System.Math.Max(x, y);
    public static byte ClampUInt8(byte x, byte lower, byte upper) => System.Math.Clamp(x, lower, upper);

    public static short MinInt16(short x, short y) => System.Math.Min(x, y);
    public static short MaxInt16(short x, short y) => System.Math.Max(x, y);
    public static short ClampInt16(short x, short lower, short upper) => System.Math.Clamp(x, lower, upper);
    public static short AbsInt16(short x) => System.Math.Abs(x);
    public static int SignInt16(short x) => System.Math.Sign(x);

    public static ushort MinUInt16(ushort x, ushort y) => System.Math.Min(x, y);
    public static ushort MaxUInt16(ushort x, ushort y) => System.Math.Max(x, y);
    public static ushort ClampUInt16(ushort x, ushort lower, ushort upper) => System.Math.Clamp(x, lower, upper);

    public static int MinInt32(int x, int y) => System.Math.Min(x, y);
    public static int MaxInt32(int x, int y) => System.Math.Max(x, y);
    public static int ClampInt32(int x, int lower, int upper) => System.Math.Clamp(x, lower, upper);
    public static int AbsInt32(int x) => System.Math.Abs(x);
    public static int SignInt32(int x) => System.Math.Sign(x);

    public static uint MinUInt32(uint x, uint y) => System.Math.Min(x, y);
    public static uint MaxUInt32(uint x, uint y) => System.Math.Max(x, y);
    public static uint ClampUInt32(uint x, uint lower, uint upper) => System.Math.Clamp(x, lower, upper);

    public static long MinInt64(long x, long y) => System.Math.Min(x, y);
    public static long MaxInt64(long x, long y) => System.Math.Max(x, y);
    public static long ClampInt64(long x, long lower, long upper) => System.Math.Clamp(x, lower, upper);
    public static long AbsInt64(long x) => System.Math.Abs(x);
    public static int SignInt64(long x) => System.Math.Sign(x);

    public static ulong MinUInt64(ulong x, ulong y) => System.Math.Min(x, y);
    public static ulong MaxUInt64(ulong x, ulong y) => System.Math.Max(x, y);
    public static ulong ClampUInt64(ulong x, ulong lower, ulong upper) => System.Math.Clamp(x, lower, upper);

    public static nint MinNative(nint x, nint y) => System.Math.Min(x, y);
    public static nint MaxNative(nint x, nint y) => System.Math.Max(x, y);
    public static nint ClampNative(nint x, nint lower, nint upper) => System.Math.Clamp(x, lower, upper);
    public static nint AbsNative(nint x) => System.Math.Abs(x);
    public static int SignNative(nint x) => System.Math.Sign(x);

    public static nuint MinUNative(nuint x, nuint y) => System.Math.Min(x, y);
    public static nuint MaxUNative(nuint x, nuint y) => System.Math.Max(x, y);
    public static nuint ClampUNative(nuint x, nuint lower, nuint upper) => System.Math.Clamp(x, lower, upper);

    public static long WrongMin(long x, long y) => System.Math.Max(x, y);
}
