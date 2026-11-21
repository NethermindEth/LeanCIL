using Mono.Cecil;

namespace Nethermind.LeanCIL;

/// <summary>
/// The bit and byte-order helpers the Lean model table models (CIL/Extraction/BitModels.lean): those of
/// <c>System.Numerics.BitOperations</c>, the same helpers each integer type declares, and
/// <c>System.Buffers.Binary.BinaryPrimitives.ReverseEndianness</c>. A call keeps its call and runs the scalar
/// intrinsic of its exact signature.
/// </summary>
internal static class BitModels
{
    const string BinaryPrimitives = "System.Buffers.Binary.BinaryPrimitives";

    private static readonly (string Name, ScalarFunction Function)[] Rotations =
        [("RotateLeft", ScalarFunction.RotateLeft), ("RotateRight", ScalarFunction.RotateRight)];
    private static readonly (string Name, ScalarFunction Function)[] Counts =
    [
        ("PopCount", ScalarFunction.PopCount), ("LeadingZeroCount", ScalarFunction.LeadingZeroCount),
        ("TrailingZeroCount", ScalarFunction.TrailingZeroCount), ("Log2", ScalarFunction.Log2)
    ];

    private static readonly Dictionary<string, ScalarIntrinsic> Calls = Build();

    /// <summary>
    /// The scalar intrinsic a call of a modelled bit helper runs as, or null: a static, non-generic reference of the
    /// exact assembly that declares its owner, <c>System.Memory</c> for <c>BinaryPrimitives</c> and
    /// <c>System.Runtime</c> otherwise.
    /// </summary>
    internal static Operation? Call(MethodReference reference, FeatureProfile profile)
    {
        if (reference.HasThis || reference.ExplicitThis || reference.HasGenericParameters ||
            reference is GenericInstanceMethod ||
            reference.CallingConvention != MethodCallingConvention.Default ||
            !Calls.TryGetValue(reference.FullName, out var model)) return null;
        var scope = reference.DeclaringType.FullName == BinaryPrimitives
            ? PlatformAssemblies.SystemMemory : PlatformAssemblies.SystemRuntime;
        if (!RuntimeModels.ExactScope(reference.DeclaringType, scope)) return null;
        RuntimeModels.ValidateSignature(reference, profile.Architecture);
        return model;
    }

    static ScalarIntrinsic Scalar(ScalarFunction function, int width, bool signed, int arguments, int result = 32) =>
        new(function, width, signed, result, arguments);

    // BitOperations counts return an int; a count an integer type declares returns the type, a 64-bit word only
    // at 64 bits. Signed Log2 throws on a negative value and signed narrow rotations have no model.
    static Dictionary<string, ScalarIntrinsic> Build()
    {
        var calls = new Dictionary<string, ScalarIntrinsic>(StringComparer.Ordinal);
        const string Bits = "System.Numerics.BitOperations";
        foreach (var (type, width, signed) in RuntimeModels.MathIntegers)
        {
            var wide = width is 32 or 64;
            var isPow2 = Scalar(ScalarFunction.IsPow2, width, signed, 1);
            calls.Add($"System.Boolean {type}::IsPow2({type})", isPow2);
            if (wide) calls.Add($"System.Boolean {Bits}::IsPow2({type})", isPow2);
            calls.Add($"{type} {BinaryPrimitives}::ReverseEndianness({type})",
                Scalar(ScalarFunction.ReverseEndianness, width, signed, 1));
            foreach (var (name, function) in Counts)
            {
                if (name == "Log2" && signed) continue;
                calls.Add($"{type} {type}::{name}({type})",
                    Scalar(function, width, false, 1, result: width == 64 ? 64 : 32));
                if (wide && !signed)
                    calls.Add($"System.Int32 {Bits}::{name}({type})", Scalar(function, width, false, 1));
            }
            if (wide && !signed)
                calls.Add($"{type} {Bits}::RoundUpToPowerOf2({type})",
                    Scalar(ScalarFunction.RoundUpToPowerOf2, width, false, 1));
            foreach (var (name, function) in Rotations)
            {
                if (wide || !signed)
                    calls.Add($"{type} {type}::{name}({type},System.Int32)", Scalar(function, width, false, 2));
                if (wide && !signed)
                    calls.Add($"{type} {Bits}::{name}({type},System.Int32)", Scalar(function, width, false, 2));
            }
        }
        return calls;
    }
}
