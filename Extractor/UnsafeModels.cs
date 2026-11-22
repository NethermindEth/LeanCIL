using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Generic runtime helpers share the same validated managed layout as CIL storage.
internal static class UnsafeModels
{
    static readonly TypeLevel Owner = new(MetadataName.OfText("System.Runtime.CompilerServices"),
        MetadataName.OfText("Unsafe"));

    // A modelled helper keeps its call. Extractor analyses read the operation selected for that call.
    internal static Operation? CallModel(MethodReference reference, string architecture) =>
        ClassifyCall(reference, architecture, out _, out _, out _);

    // Proof outlines read the closed storage type from the validated unaligned call at this site.
    internal static TypeReference? UnalignedStorage(Instruction site, string name, string architecture)
    {
        if (site.OpCode.Code != Code.Call || site.Operand is not GenericInstanceMethod call || call.Name != name)
            return null;
        ClassifyCall(call, architecture, out var storage, out _, out _);
        return storage;
    }

    /// <summary>The signedness and native-width stride of a retained Unsafe pointer addition.</summary>
    internal static (ulong Stride, bool Signed)? Offset(Instruction site, string architecture)
    {
        if (site.OpCode.Code != Code.Call || site.Operand is not GenericInstanceMethod
            { Name: "Add" or "Subtract" or "AddByteOffset" } call) return null;
        ClassifyCall(call, architecture, out _, out var offset, out _);
        return offset;
    }

    /// <summary>The element width of an admitted Unsafe.SizeOf call.</summary>
    internal static int? SizeOf(MethodReference reference, string architecture)
    {
        if (reference.Name != "SizeOf") return null;
        ClassifyCall(reference, architecture, out _, out _, out var size);
        return size;
    }

    static Operation? ClassifyCall(MethodReference reference, string architecture, out TypeReference? storage,
        out (ulong Stride, bool Signed)? offset, out int? size)
    {
        size = null;
        storage = null;
        offset = null;
        if (reference.Name is "As" or "AsRef" or "BitCast")
        {
            if (reference.DeclaringType is TypeSpecification ||
                !IdentityRows.TopLevelMatches(reference.DeclaringType, Owner, PlatformAssemblies.SystemRuntime))
                return null;
            return reference.Name == "BitCast" ? ValueBitCasts.CallModel(reference, architecture) :
                ReinterpretReference(reference, architecture);
        }
        if (reference.DeclaringType.FullName != "System.Runtime.CompilerServices.Unsafe" ||
            !RuntimeModels.ExactScope(reference.DeclaringType, PlatformAssemblies.SystemRuntime) ||
            reference is not GenericInstanceMethod generic || generic.GenericArguments.Count != 1 ||
            generic.ElementMethod.GenericParameters.Count != 1 || reference.HasThis || reference.ExplicitThis ||
            (generic.ElementMethod.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default)
            return null;

        var element = generic.GenericArguments[0];
        if (reference.Name is "Read" or "Write" or "ReadUnaligned" or "WriteUnaligned")
            return generic.ElementMethod.CallingConvention == MethodCallingConvention.Generic &&
                reference.DeclaringType is not TypeSpecification &&
                IdentityRows.TopLevelMatches(reference.DeclaringType, Owner, PlatformAssemblies.SystemRuntime)
                ? MemoryTransfers.CallModel(generic, architecture, out storage) : null;
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
        var nullRef = reference.Name == "NullRef" && reference.Parameters.Count == 0 &&
            Reference(reference.ReturnType);
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
        if (nullRef || isNullRef) return Unoutlined.Site;
        var width = ElementWidth(element, reference.Module, architecture);

        if (skipInit) return Unoutlined.Site;
        if (comparison) return reference.Name switch
        {
            "AreSame" => new StackOperation(Code.Ceq),
            "IsAddressLessThan" => new StackOperation(Code.Clt_Un),
            _ => new StackOperation(Code.Cgt_Un)
        };
        if (byteOffset) return Unoutlined.Site;
        if (subtractBytes) return new StackOperation(Code.Sub);
        if (sizeOf)
        {
            size = width;
            return Unoutlined.Site;
        }
        var signed = reference.Parameters[1].ParameterType.FullName != "System.UIntPtr";
        // Native-width negative strides reuse the checked wrapping offset operation.
        var stride = reference.Name == "Subtract" ? unchecked(0UL - (ulong)width) : (ulong)(addBytes ? 1 : width);
        offset = (stride, signed);
        return Unoutlined.Site;
    }

    // An element of field or vector storage has a width; any other element is unsupported.
    static int ElementWidth(TypeReference element, ModuleDefinition module, string architecture) =>
        element is GenericInstanceType vector && RuntimeModels.SupportedType(vector)
            ? vector.ElementType.FullName switch
            {
                "System.Runtime.Intrinsics.Vector128`1" => 16,
                "System.Runtime.Intrinsics.Vector256`1" => 32,
                "System.Runtime.Intrinsics.Vector512`1" => 64,
                _ => throw new InvalidDataException($"Unsupported Unsafe element layout: {element.FullName}")
            }
            : MetadataValidation.FieldSize(element, module, architecture);

    // A byref reinterpretation changes only its static type, never the allocation,
    // offset, initialized bytes or access bounds used by checked memory operations.
    private static Operation? ReinterpretReference(MethodReference reference, string architecture)
    {
        if (reference is not GenericInstanceMethod generic || reference.HasThis || reference.ExplicitThis ||
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
            // A span, array or class reference is not the address of bytes the other type can name.
            _ = ElementWidth(type, reference.Module, architecture);
        }
        RuntimeModels.ValidateSignature(reference, architecture);
        return Unoutlined.Site;
    }
}

// A value cast reads the closed pair's representations and preserves the snapshot's initialization flags.
internal static class ValueBitCasts
{
    internal static Operation? CallModel(MethodReference reference, string architecture)
    {
        if (reference is not GenericInstanceMethod generic || generic.GenericArguments.Count != 2 ||
            generic.ElementMethod.GenericParameters.Count != 2 || reference.HasThis || reference.ExplicitThis ||
            generic.ElementMethod.CallingConvention != MethodCallingConvention.Generic ||
            reference.Parameters.Count != 1) return null;

        bool Parameter(TypeReference type, int position) => type is GenericParameter parameter &&
            parameter.Type == GenericParameterType.Method && parameter.Position == position &&
            parameter.Owner == generic.ElementMethod;
        if (!Parameter(reference.Parameters[0].ParameterType, 0) || !Parameter(reference.ReturnType, 1)) return null;

        var source = generic.GenericArguments[0];
        var target = generic.GenericArguments[1];
        if (source.MetadataType == MetadataType.Byte && target.MetadataType == MetadataType.Boolean)
        {
            RuntimeModels.ValidateSignature(reference, architecture);
            return Unoutlined.Site;
        }
        if (!generic.GenericArguments.Any(type => MetadataValidation.IsAggregate(type, reference.Module) ||
            type is GenericInstanceType)) return null;
        var fromWidth = SnapshotWidth(source, reference.Module, architecture);
        var toWidth = SnapshotWidth(target, reference.Module, architecture);
        if (fromWidth is null || toWidth is null || fromWidth != toWidth)
            throw new InvalidDataException($"Unsupported Unsafe.BitCast value layouts: {reference.FullName}");
        RuntimeModels.ValidateSignature(reference, architecture);
        return Unoutlined.Site;
    }

    static int? SnapshotWidth(TypeReference type, ModuleDefinition module, string architecture)
    {
        MetadataValidation.Type(type, module, architecture: architecture);
        RuntimeModels.ValidateTypeIdentity(type, module, architecture);
        if (MetadataValidation.IsAggregate(type, module))
            return MetadataValidation.Layout(type, module, architecture);
        return MetadataValidation.IntegerVectorWidth(type);
    }
}
