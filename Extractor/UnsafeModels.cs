using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Generic runtime helpers share the same validated managed layout as CIL storage.
internal static class UnsafeModels
{
    internal static string? Translate(MethodReference reference)
    {
        if (reference.DeclaringType.FullName != "System.Runtime.CompilerServices.Unsafe" ||
            !RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") ||
            reference is not GenericInstanceMethod generic || generic.GenericArguments.Count != 1 ||
            generic.ElementMethod.GenericParameters.Count != 1 || reference.HasThis || reference.ExplicitThis ||
            (generic.ElementMethod.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default)
            return null;

        var element = generic.GenericArguments[0];
        var definition = generic.ElementMethod;
        bool Parameter(TypeReference type) => type is GenericParameter parameter &&
            parameter.Type == GenericParameterType.Method && parameter.Position == 0 && parameter.Owner == definition;
        bool Reference(TypeReference type) => type is ByReferenceType byRef && Parameter(byRef.ElementType);

        var sizeOf = reference.Name == "SizeOf" && reference.Parameters.Count == 0 &&
            reference.ReturnType.FullName == "System.Int32";
        var add = reference.Name == "Add" && reference.Parameters.Count == 2 &&
            Reference(reference.ReturnType) && Reference(reference.Parameters[0].ParameterType) &&
            reference.Parameters[1].ParameterType.FullName is "System.Int32" or "System.IntPtr" or "System.UIntPtr";
        var skipInit = reference.Name == "SkipInit" && reference.Parameters.Count == 1 &&
            Reference(reference.Parameters[0].ParameterType) && reference.ReturnType.MetadataType == MetadataType.Void;
        if (!sizeOf && !add && !skipInit) return null;

        if (element is ByReferenceType || element is PointerType || element is GenericParameter)
            throw new InvalidDataException($"Unsupported Unsafe element type: {element.FullName}");
        MetadataValidation.Type(element, reference.Module);
        RuntimeModels.ValidateSignature(reference);
        if (skipInit) return ".skipInit";
        var width = element is GenericInstanceType vector && RuntimeModels.SupportedType(vector)
            ? vector.ElementType.FullName switch
            {
                "System.Runtime.Intrinsics.Vector128`1" => 16,
                "System.Runtime.Intrinsics.Vector256`1" => 32,
                _ => throw new InvalidDataException($"Unsupported Unsafe element layout: {element.FullName}")
            }
            : MetadataValidation.FieldSize(element, reference.Module);

        if (sizeOf) return $".const32 {width}";
        var signed = reference.Parameters[1].ParameterType.FullName != "System.UIntPtr";
        return $".memory (.add {width} {signed.ToString().ToLowerInvariant()})";
    }
}
