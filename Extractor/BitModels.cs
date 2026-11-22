using Mono.Cecil;

namespace Nethermind.LeanCIL;

/// <summary>The exact integer bit and byte-order calls admitted by CIL/Extraction/BitModels.lean.</summary>
internal static class BitModels
{
    const string BinaryPrimitives = "System.Buffers.Binary.BinaryPrimitives";
    static readonly string[] Counts = ["PopCount", "LeadingZeroCount", "TrailingZeroCount", "Log2"];
    static readonly HashSet<string> Calls = Build();

    /// <summary>Whether the static bit helper binds its platform declaration and exact signature.</summary>
    internal static bool Admits(MethodReference reference, FeatureProfile profile)
    {
        if (reference.HasThis || reference.ExplicitThis || reference.HasGenericParameters ||
            reference is GenericInstanceMethod || reference.CallingConvention != MethodCallingConvention.Default ||
            !Calls.Contains(reference.FullName)) return false;
        var scope = reference.DeclaringType.FullName == BinaryPrimitives
            ? PlatformAssemblies.SystemMemory : PlatformAssemblies.SystemRuntime;
        if (!RuntimeModels.ExactScope(reference.DeclaringType, scope)) return false;
        RuntimeModels.ValidateSignature(reference, profile.Architecture);
        return true;
    }

    /// <summary>The stack width of a bit count's declared result, including native integers.</summary>
    internal static int? CountWidth(MethodReference reference, FeatureProfile profile)
    {
        if (!Counts.Contains(reference.Name) || !Admits(reference, profile)) return null;
        return reference.ReturnType.MetadataType is MetadataType.Int64 or MetadataType.UInt64 or
            MetadataType.IntPtr or MetadataType.UIntPtr ? 64 : 32;
    }

    // Signed Log2 can throw on a negative input. Signed narrow rotations have no model.
    static HashSet<string> Build()
    {
        var calls = new HashSet<string>(StringComparer.Ordinal);
        const string Bits = "System.Numerics.BitOperations";
        foreach (var (type, width, signed) in RuntimeModels.MathIntegers)
        {
            var wide = width is 32 or 64;
            calls.Add($"System.Boolean {type}::IsPow2({type})");
            if (wide) calls.Add($"System.Boolean {Bits}::IsPow2({type})");
            calls.Add($"{type} {BinaryPrimitives}::ReverseEndianness({type})");
            foreach (var name in Counts)
            {
                if (name == "Log2" && signed) continue;
                calls.Add($"{type} {type}::{name}({type})");
                if (wide && !signed) calls.Add($"System.Int32 {Bits}::{name}({type})");
            }
            if (wide && !signed) calls.Add($"{type} {Bits}::RoundUpToPowerOf2({type})");
            foreach (var name in new[] { "RotateLeft", "RotateRight" })
            {
                if (wide || !signed) calls.Add($"{type} {type}::{name}({type},System.Int32)");
                if (wide && !signed) calls.Add($"{type} {Bits}::{name}({type},System.Int32)");
            }
        }
        return calls;
    }
}
