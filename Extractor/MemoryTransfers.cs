using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Managed-reference transfers share the exact layouts used by typed CIL loads and stores.
internal static class MemoryTransfers
{
    internal static string? Marshal(MethodReference reference, string architecture)
    {
        if (reference.DeclaringType.FullName != "System.Runtime.InteropServices.MemoryMarshal" ||
            !RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") ||
            reference is not GenericInstanceMethod generic || generic.GenericArguments.Count != 1 ||
            generic.ElementMethod.GenericParameters.Count != 1 || reference.HasThis || reference.ExplicitThis ||
            (generic.ElementMethod.CallingConvention & ~MethodCallingConvention.Generic) !=
                MethodCallingConvention.Default)
            return null;
        bool Parameter(TypeReference type) => type is GenericParameter parameter &&
            parameter.Type == GenericParameterType.Method && parameter.Position == 0 &&
            parameter.Owner == generic.ElementMethod;
        bool ParameterReference(TypeReference type) => type is ByReferenceType byRef && Parameter(byRef.ElementType);
        var read = reference.Name is "Read" or "TryRead";
        var trying = reference.Name is "TryRead" or "TryWrite";
        if (reference.Name is not ("Read" or "TryRead" or "Write" or "TryWrite") ||
            reference.Parameters.Count != (read && !trying ? 1 : 2)) return null;
        var span = read ? "System.ReadOnlySpan`1<System.Byte>" : "System.Span`1<System.Byte>";
        if (reference.Parameters[0].ParameterType.FullName != span ||
            (reference.Parameters.Count == 2 && !ParameterReference(reference.Parameters[1].ParameterType)) ||
            !(trying ? reference.ReturnType.FullName == "System.Boolean" : read ? Parameter(reference.ReturnType) :
                reference.ReturnType.MetadataType == MetadataType.Void)) return null;
        RuntimeModels.ValidateSignature(reference, architecture);
        var type = generic.GenericArguments[0];
        MetadataValidation.Type(type, reference.Module, architecture: architecture);
        string kind;
        if (MetadataValidation.IsAggregate(type, reference.Module))
            kind = $".snapshot (.aggregate {MetadataValidation.Layout(type, reference.Module, architecture)})";
        else if (MetadataValidation.IntegerVectorWidth(type) is { } vectorWidth)
            kind = $".snapshot .vector{vectorWidth * 8}";
        else
        {
            if (type is TypeSpecification)
                throw new InvalidDataException($"Unsupported marshaled value type: {type.FullName}");
            var storage = EnumTypes.Storage(type);
            var width = MetadataValidation.PrimitiveWidth(storage);
            var signed = storage.FullName is "System.SByte" or "System.Int16";
            kind = $".scalar {width} {signed.ToString().ToLowerInvariant()}";
        }
        return $".memory (.marshal{(read ? "Read" : "Write")} ({kind}) {trying.ToString().ToLowerInvariant()})";
    }

    internal static string? Unaligned(MethodReference reference, string architecture)
    {
        if (reference.DeclaringType.FullName != "System.Runtime.CompilerServices.Unsafe" ||
            !RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") ||
            reference is not GenericInstanceMethod generic || generic.GenericArguments.Count != 1 ||
            generic.ElementMethod.GenericParameters.Count != 1 || reference.HasThis || reference.ExplicitThis ||
            (generic.ElementMethod.CallingConvention & ~MethodCallingConvention.Generic) !=
                MethodCallingConvention.Default)
            return null;
        bool Parameter(TypeReference type) => type is GenericParameter parameter &&
            parameter.Type == GenericParameterType.Method && parameter.Position == 0 &&
            parameter.Owner == generic.ElementMethod;
        bool ByteReference(TypeReference type) => type is ByReferenceType byRef &&
            byRef.ElementType.FullName == "System.Byte";
        var read = reference.Name == "ReadUnaligned" && reference.Parameters.Count == 1 &&
            ByteReference(reference.Parameters[0].ParameterType) && Parameter(reference.ReturnType);
        var write = reference.Name == "WriteUnaligned" && reference.Parameters.Count == 2 &&
            ByteReference(reference.Parameters[0].ParameterType) && Parameter(reference.Parameters[1].ParameterType) &&
            reference.ReturnType.MetadataType == MetadataType.Void;
        if (!read && !write) return null;
        RuntimeModels.ValidateSignature(reference, architecture);
        var type = generic.GenericArguments[0];
        MetadataValidation.Type(type, reference.Module, architecture: architecture);
        if (MetadataValidation.IsAggregate(type, reference.Module))
        {
            var width = MetadataValidation.Layout(type, reference.Module, architecture);
            return read ? $".loadAggregate {width}" : $".storeAggregate {width}";
        }
        if (MetadataValidation.IntegerVectorWidth(type) is { } vectorWidth)
            return $".memory .{(read ? "load" : "store")}{vectorWidth * 8}";
        if (type is TypeSpecification)
            throw new InvalidDataException($"Unsupported unaligned value type: {type.FullName}");
        var storage = EnumTypes.Storage(type);
        var scalarWidth = MetadataValidation.PrimitiveWidth(storage);
        var signed = storage.FullName is "System.SByte" or "System.Int16";
        return read ? $".loadScalar {scalarWidth} {signed.ToString().ToLowerInvariant()}" :
            $".storeScalar {scalarWidth}";
    }
}
