using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Generic runtime helpers share the same validated managed layout as CIL storage.
internal static class UnsafeModels
{
    internal static string? Translate(MethodReference reference, string architecture = "scalar")
    {
        if (MemoryTransfers.Unsafe(reference, architecture) is { } transfer) return transfer;
        if (ReinterpretReference(reference, architecture) is { } cast) return cast;
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
        bool Pointer(TypeReference type) => type is PointerType { ElementType.MetadataType: MetadataType.Void };

        var sizeOf = reference.Name == "SizeOf" && reference.Parameters.Count == 0 &&
            reference.ReturnType.FullName == "System.Int32";
        var elementOffset = reference.Parameters.Count == 2 &&
            ((reference.Name is "Add" or "Subtract" && Reference(reference.ReturnType) &&
              Reference(reference.Parameters[0].ParameterType) &&
              reference.Parameters[1].ParameterType.FullName is "System.Int32" or "System.IntPtr" or "System.UIntPtr") ||
             (reference.Name is "Add" or "Subtract" && Pointer(reference.ReturnType) &&
              Pointer(reference.Parameters[0].ParameterType) &&
              reference.Parameters[1].ParameterType.FullName == "System.Int32"));
        var skipInit = reference.Name == "SkipInit" && reference.Parameters.Count == 1 &&
            Reference(reference.Parameters[0].ParameterType) && reference.ReturnType.MetadataType == MetadataType.Void;
        var nullRef = reference.Name == "NullRef" && reference.Parameters.Count == 0 && Reference(reference.ReturnType);
        var isNullRef = reference.Name == "IsNullRef" && reference.Parameters.Count == 1 &&
            Reference(reference.Parameters[0].ParameterType) && reference.ReturnType.MetadataType == MetadataType.Boolean;
        var referencePair = reference.Parameters.Count == 2 &&
            Reference(reference.Parameters[0].ParameterType) && Reference(reference.Parameters[1].ParameterType);
        var comparison = referencePair && reference.ReturnType.MetadataType == MetadataType.Boolean &&
            reference.Name is "AreSame" or "IsAddressLessThan" or "IsAddressGreaterThan";
        var byteOffset = referencePair && reference.Name == "ByteOffset" &&
            reference.ReturnType.FullName == "System.IntPtr";
        var addBytes = reference.Name == "AddByteOffset" && reference.Parameters.Count == 2 &&
            Reference(reference.ReturnType) && Reference(reference.Parameters[0].ParameterType) &&
            reference.Parameters[1].ParameterType.FullName is "System.IntPtr" or "System.UIntPtr";
        var subtractBytes = reference.Name == "SubtractByteOffset" && reference.Parameters.Count == 2 &&
            Reference(reference.ReturnType) && Reference(reference.Parameters[0].ParameterType) &&
            reference.Parameters[1].ParameterType.FullName is "System.IntPtr" or "System.UIntPtr";
        if (!sizeOf && !elementOffset && !skipInit && !nullRef && !isNullRef && !comparison && !byteOffset &&
            !addBytes && !subtractBytes) return null;

        if (element is ByReferenceType || element is PointerType || element is GenericParameter)
            throw new InvalidDataException($"Unsupported Unsafe element type: {element.FullName}");
        MetadataValidation.Type(element, reference.Module, architecture: architecture);
        RuntimeModels.ValidateSignature(reference, architecture);
        if (skipInit) return ".skipInit";
        if (nullRef) return ".memory .nullRef";
        if (isNullRef) return ".memory .isNullRef";
        var width = element is GenericInstanceType vector && RuntimeModels.SupportedType(vector)
            ? vector.ElementType.FullName switch
            {
                "System.Runtime.Intrinsics.Vector128`1" => 16,
                "System.Runtime.Intrinsics.Vector256`1" => 32,
                "System.Runtime.Intrinsics.Vector512`1" => 64,
                _ => throw new InvalidDataException($"Unsupported Unsafe element layout: {element.FullName}")
            }
            : MetadataValidation.FieldSize(element, reference.Module, architecture);

        if (comparison) return reference.Name switch
        {
            "AreSame" => ".eq",
            "IsAddressLessThan" => ".ltu",
            _ => ".gtu"
        };
        if (byteOffset) return ".memory .byteOffset";
        if (subtractBytes) return ".sub";
        if (sizeOf) return $".const32 {width}";
        var signed = reference.Parameters[1].ParameterType.FullName != "System.UIntPtr";
        // Native-width negative strides reuse the checked wrapping offset operation.
        var stride = reference.Name == "Subtract" ? unchecked(0UL - (ulong)width) : (ulong)(addBytes ? 1 : width);
        return $".memory (.add {stride} {signed.ToString().ToLowerInvariant()})";
    }

    // A byref reinterpretation changes only its static type, never the allocation,
    // offset, initialized bytes or access bounds used by checked memory operations.
    private static string? ReinterpretReference(MethodReference reference, string architecture)
    {
        if (reference.DeclaringType.FullName != "System.Runtime.CompilerServices.Unsafe" ||
            !RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") ||
            reference is not GenericInstanceMethod generic || reference.HasThis || reference.ExplicitThis ||
            (generic.ElementMethod.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default)
            return null;
        var definition = generic.ElementMethod;
        var arity = reference.Name switch { "As" => 2, "AsRef" => 1, _ => 0 };
        if (arity == 0 || generic.GenericArguments.Count != arity || definition.GenericParameters.Count != arity ||
            definition.Parameters.Count != 1) return null;
        bool Reference(TypeReference type, int position) => type is ByReferenceType byRef &&
            byRef.ElementType is GenericParameter parameter && parameter.Type == GenericParameterType.Method &&
            parameter.Position == position && parameter.Owner == definition;
        var pointer = reference.Name == "AsRef" &&
            definition.Parameters[0].ParameterType is PointerType { ElementType.MetadataType: MetadataType.Void };
        if ((!pointer && !Reference(definition.Parameters[0].ParameterType, 0)) ||
            !Reference(definition.ReturnType, arity - 1))
            return null;
        foreach (var type in generic.GenericArguments)
        {
            if (type is ByReferenceType or PointerType or GenericParameter)
                throw new InvalidDataException($"Unsupported Unsafe reference element: {type.FullName}");
            MetadataValidation.Type(type, reference.Module, architecture: architecture);
        }
        RuntimeModels.ValidateSignature(reference, architecture);
        return ".memory .asRef";
    }
}
