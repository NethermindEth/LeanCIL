using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Value reinterpretation is distinct from Unsafe.As<TFrom,TTo>'s byref identity.
internal static class ValueBitCasts
{
    internal static string? Translate(MethodReference reference)
    {
        if (reference.Name != "BitCast" || reference.DeclaringType.FullName != "System.Runtime.CompilerServices.Unsafe" ||
            !RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") ||
            reference is not GenericInstanceMethod generic || generic.GenericArguments.Count != 2 ||
            generic.ElementMethod.GenericParameters.Count != 2 || reference.HasThis || reference.ExplicitThis ||
            (generic.ElementMethod.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default ||
            reference.Parameters.Count != 1)
            return null;

        bool Parameter(TypeReference type, int index) => type is GenericParameter parameter &&
            parameter.Type == GenericParameterType.Method && parameter.Position == index &&
            parameter.Owner == generic.ElementMethod;
        if (!Parameter(reference.Parameters[0].ParameterType, 0) || !Parameter(reference.ReturnType, 1)) return null;

        (string Shape, int Width)? Shape(TypeReference type)
        {
            MetadataValidation.Type(type, reference.Module);
            RuntimeModels.ValidateTypeIdentity(type, reference.Module);
            if (MetadataValidation.IsAggregate(type, reference.Module))
            {
                var width = MetadataValidation.Layout(type, reference.Module);
                return ($"(.aggregate {width})", width);
            }
            if (type is GenericInstanceType vector && vector.GenericArguments.Count == 1 &&
                vector.GenericArguments[0].FullName is "System.UInt64" or "System.UInt32")
                return vector.ElementType.FullName switch
                {
                    "System.Runtime.Intrinsics.Vector128`1" => (".vector128", 16),
                    "System.Runtime.Intrinsics.Vector256`1" => (".vector256", 32),
                    "System.Runtime.Intrinsics.Vector512`1" => (".vector512", 64),
                    _ => null
                };
            return null;
        }

        // Leave existing independently validated scalar overloads to their matcher.
        if (!generic.GenericArguments.Any(t => MetadataValidation.IsAggregate(t, reference.Module) ||
            t is GenericInstanceType)) return null;
        var source = Shape(generic.GenericArguments[0]);
        var target = Shape(generic.GenericArguments[1]);
        if (source is null || target is null || source.Value.Width != target.Value.Width)
            throw new InvalidDataException($"Unsupported Unsafe.BitCast value layouts: {reference.FullName}");
        RuntimeModels.ValidateSignature(reference);
        return $".memory (.bitcastValue {source.Value.Shape} {target.Value.Shape})";
    }
}
