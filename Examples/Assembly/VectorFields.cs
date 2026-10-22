using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;

namespace Examples;

public static class VectorFields
{
    [StructLayout(LayoutKind.Sequential)]
    public struct Holder128 { public byte Prefix; public Vector128<ulong> Value; }

    [StructLayout(LayoutKind.Sequential)]
    public struct Holder256 { public byte Prefix; public Vector256<ulong> Value; }

    [StructLayout(LayoutKind.Explicit, Pack = 1, Size = 35)]
    public struct Packed256 { [FieldOffset(3)] public Vector256<ulong> Value; }

    public struct Words256 { public ulong A, B, C, D; }
    [StructLayout(LayoutKind.Sequential)]
    public struct Single256 { public Vector256<ulong> Value; }

    public static Vector128<ulong> Read128(Holder128 value) => value.Value;
    public static Vector256<ulong> Read256(Holder256 value) => value.Value;
    public static Vector128<ulong> Write128(ref Holder128 holder, Vector128<ulong> value)
    {
        holder.Value = value;
        return holder.Value;
    }
    public static Vector256<ulong> Write256(ref Holder256 holder, Vector256<ulong> value)
    {
        holder.Value = value;
        return holder.Value;
    }
    public static Vector256<ulong> WritePacked(ref Packed256 holder, Vector256<ulong> value)
    {
        holder.Value = value;
        return holder.Value;
    }
    public static Vector256<ulong> Reinterpret(ref Words256 holder, Vector256<ulong> value)
    {
        ref Single256 vector = ref Unsafe.As<Words256, Single256>(ref holder);
        vector.Value = value;
        return Unsafe.As<Words256, Vector256<ulong>>(ref holder);
    }
    public static ref Vector256<ulong> Address256(ref Holder256 value) => ref value.Value;
}
