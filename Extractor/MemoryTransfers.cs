using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Managed-reference transfers share the exact layouts used by typed CIL loads and stores.
internal static class MemoryTransfers
{
    internal static (string Kind, int Alignment) Describe(TypeReference type, ModuleDefinition module,
        string architecture)
    {
        if (MetadataValidation.IsAggregate(type, module))
        {
            var layout = MetadataValidation.AggregateLayout(type, module, architecture);
            return ($".snapshot (.aggregate {layout.Size})", layout.Alignment);
        }
        MetadataValidation.Type(type, module, architecture: architecture);
        if (MetadataValidation.IntegerVectorWidth(type) is { } vectorWidth)
            return ($".snapshot .vector{vectorWidth * 8}", vectorWidth);
        if (type is TypeSpecification)
            throw new InvalidDataException($"Unsupported transferred value type: {type.FullName}");
        var storage = EnumTypes.Storage(type);
        var width = MetadataValidation.PrimitiveWidth(storage);
        var signed = storage.FullName is "System.SByte" or "System.Int16";
        return ($".scalar {width} {signed.ToString().ToLowerInvariant()}", width);
    }

    // The analyses use this transfer for the kept call of the validated generic Unsafe owner.
    internal static Operation? CallModel(GenericInstanceMethod reference, string architecture)
    {
        bool Parameter(TypeReference type) => type is GenericParameter parameter &&
            parameter.Type == GenericParameterType.Method && parameter.Position == 0 &&
            parameter.Owner == reference.ElementMethod;
        bool Address(TypeReference type) => type is ByReferenceType { ElementType.MetadataType: MetadataType.Byte } ||
            type is PointerType { ElementType.MetadataType: MetadataType.Void };
        var aligned = reference.Name is "Read" or "Write";
        if (aligned && reference.Parameters.FirstOrDefault()?.ParameterType is not
            PointerType { ElementType.MetadataType: MetadataType.Void }) return null;
        var read = reference.Name is "ReadUnaligned" or "Read" && reference.Parameters.Count == 1 &&
            Address(reference.Parameters[0].ParameterType) && Parameter(reference.ReturnType);
        var write = reference.Name is "WriteUnaligned" or "Write" && reference.Parameters.Count == 2 &&
            Address(reference.Parameters[0].ParameterType) && Parameter(reference.Parameters[1].ParameterType) &&
            reference.ReturnType.MetadataType == MetadataType.Void;
        if (!read && !write) return null;
        RuntimeModels.ValidateSignature(reference, architecture);
        var type = reference.GenericArguments[0];
        if (aligned)
        {
            var (kind, alignment) = Describe(type, reference.Module, architecture);
            return MemoryOperation.Other(
                $"(.pointerTransfer ({kind}) {alignment} {write.ToString().ToLowerInvariant()})");
        }
        MetadataValidation.Type(type, reference.Module, architecture: architecture);
        if (MetadataValidation.IsAggregate(type, reference.Module))
        {
            var width = MetadataValidation.Layout(type, reference.Module, architecture);
            return new AggregateTransfer(read ? AggregateAccess.Load : AggregateAccess.Store, width);
        }
        if (MetadataValidation.IntegerVectorWidth(type) is { } vectorWidth)
            return MemoryOperation.Other($".{(read ? "load" : "store")}{vectorWidth * 8}");
        if (type is TypeSpecification)
            throw new InvalidDataException($"Unsupported unaligned value type: {type.FullName}");
        var storage = EnumTypes.Storage(type);
        var scalarWidth = MetadataValidation.PrimitiveWidth(storage);
        var signed = storage.FullName is "System.SByte" or "System.Int16";
        if (!read) return new StoreScalar(scalarWidth);
        return new LoadScalar(scalarWidth, signed ? LoadSign.Signed : LoadSign.UnsignedSpelled);
    }
}
