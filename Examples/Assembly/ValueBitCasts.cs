using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Examples;

public static class ValueBitCasts
{
    public struct Pair { public ulong A, B; }
    public struct Limbs { public ulong A, B, C, D; }
    public struct ContainsReference { public object Value; }

    public static Vector256<ulong> To256UInt64(Limbs value) => Unsafe.BitCast<Limbs, Vector256<ulong>>(value);
    public static Vector256<uint> To256UInt32(Limbs value) => Unsafe.BitCast<Limbs, Vector256<uint>>(value);
    public static Limbs From256UInt64(Vector256<ulong> value) => Unsafe.BitCast<Vector256<ulong>, Limbs>(value);
    public static Limbs From256UInt32(Vector256<uint> value) => Unsafe.BitCast<Vector256<uint>, Limbs>(value);
    public static Vector128<ulong> To128UInt64(Pair value) => Unsafe.BitCast<Pair, Vector128<ulong>>(value);
    public static Vector128<uint> To128UInt32(Pair value) => Unsafe.BitCast<Pair, Vector128<uint>>(value);
    public static Pair From128UInt64(Vector128<ulong> value) => Unsafe.BitCast<Vector128<ulong>, Pair>(value);
    public static Pair From128UInt32(Vector128<uint> value) => Unsafe.BitCast<Vector128<uint>, Pair>(value);
    public static Limbs RoundTrip(Limbs value) => From256UInt64(To256UInt64(value));
    public static Vector256<ulong> CopyLocal(Limbs value)
    {
        var local = To256UInt64(value);
        return ReadLocal(ref local);
    }
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static Vector256<ulong> ReadLocal(ref Vector256<ulong> value) => value;
    public static Limbs ParameterCopy(Limbs value) => ReadAggregate(ref value);
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static Limbs ReadAggregate(ref Limbs value) => value;
    public static Vector256<ulong> WrongSize(Pair value) => Unsafe.BitCast<Pair, Vector256<ulong>>(value);
    public static Vector128<ulong> ReferenceLayout(ContainsReference value) => Unsafe.BitCast<ContainsReference, Vector128<ulong>>(value);
}
