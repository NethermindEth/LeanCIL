using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Managed-reference transfers share the exact layouts used by typed CIL loads and stores.
internal static class MemoryTransfers
{
    internal static void ValidateElement(TypeReference type, ModuleDefinition module,
        string architecture)
    {
        if (MetadataValidation.IsAggregate(type, module))
        {
            MetadataValidation.AggregateLayout(type, module, architecture);
            return;
        }
        MetadataValidation.Type(type, module, architecture: architecture);
        if (MetadataValidation.IntegerVectorWidth(type) is not null) return;
        if (type is TypeSpecification)
            throw new InvalidDataException($"Unsupported transferred value type: {type.FullName}");
        MetadataValidation.PrimitiveWidth(EnumTypes.Storage(type));
    }

    // The analyses use this transfer for the kept call of the validated generic Unsafe owner.
    internal static bool CallModel(GenericInstanceMethod reference, string architecture, out TypeReference? storage)
    {
        storage = null;
        bool Parameter(TypeReference type) => type is GenericParameter parameter &&
            parameter.Type == GenericParameterType.Method && parameter.Position == 0 &&
            parameter.Owner == reference.ElementMethod;
        bool Address(TypeReference type) => type is ByReferenceType { ElementType.MetadataType: MetadataType.Byte } ||
            type is PointerType { ElementType.MetadataType: MetadataType.Void };
        var aligned = reference.Name is "Read" or "Write";
        if (aligned && reference.Parameters.FirstOrDefault()?.ParameterType is not
            PointerType { ElementType.MetadataType: MetadataType.Void }) return false;
        var read = reference.Name is "ReadUnaligned" or "Read" && reference.Parameters.Count == 1 &&
            Address(reference.Parameters[0].ParameterType) && Parameter(reference.ReturnType);
        var write = reference.Name is "WriteUnaligned" or "Write" && reference.Parameters.Count == 2 &&
            Address(reference.Parameters[0].ParameterType) && Parameter(reference.Parameters[1].ParameterType) &&
            reference.ReturnType.MetadataType == MetadataType.Void;
        if (!read && !write) return false;
        RuntimeModels.ValidateSignature(reference, architecture);
        var type = reference.GenericArguments[0];
        if (aligned)
        {
            ValidateElement(type, reference.Module, architecture);
            return true;
        }
        MetadataValidation.Type(type, reference.Module, architecture: architecture);
        if (MetadataValidation.IsAggregate(type, reference.Module))
        {
            MetadataValidation.Layout(type, reference.Module, architecture);
            return true;
        }
        if (MetadataValidation.IntegerVectorWidth(type) is not null) return true;
        if (type is TypeSpecification)
            throw new InvalidDataException($"Unsupported unaligned value type: {type.FullName}");
        storage = EnumTypes.Storage(type);
        MetadataValidation.PrimitiveWidth(storage);
        return true;
    }
}
