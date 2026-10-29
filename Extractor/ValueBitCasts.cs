using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Value reinterpretation is distinct from Unsafe.As<TFrom,TTo>'s byref identity.
internal static class ValueBitCasts
{
    internal static string? Translate(MethodReference reference, string architecture = "scalar")
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
            MetadataValidation.Type(type, reference.Module, architecture: architecture);
            RuntimeModels.ValidateTypeIdentity(type, reference.Module, architecture);
            if (MetadataValidation.IsAggregate(type, reference.Module))
            {
                int width = MetadataValidation.Layout(type, reference.Module, architecture);
                return ($"(.aggregate {width})", width);
            }
            if (MetadataValidation.IntegerVectorWidth(type) is int vectorWidth)
                return ($".vector{vectorWidth * 8}", vectorWidth);
            return null;
        }

        // Leave existing independently validated scalar overloads to their matcher.
        if (!generic.GenericArguments.Any(t => MetadataValidation.IsAggregate(t, reference.Module) ||
            t is GenericInstanceType)) return null;
        var source = Shape(generic.GenericArguments[0]);
        var target = Shape(generic.GenericArguments[1]);
        if (source is null || target is null || source.Value.Width != target.Value.Width)
            throw new InvalidDataException($"Unsupported Unsafe.BitCast value layouts: {reference.FullName}");
        RuntimeModels.ValidateSignature(reference, architecture);
        return $".memory (.bitcastValue {source.Value.Shape} {target.Value.Shape})";
    }
}
