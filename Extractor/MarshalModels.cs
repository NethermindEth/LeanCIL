using Mono.Cecil;

namespace Nethermind.LeanCIL;

// The open signature fixes each overload. Closed element types supply its storage widths.
internal static class MarshalModels
{
    internal static bool CallModel(MethodReference reference, string architecture)
    {
        if (reference is not GenericInstanceMethod method || reference.HasThis || reference.ExplicitThis ||
            reference.DeclaringType is TypeSpecification ||
            reference.DeclaringType.FullName != "System.Runtime.InteropServices.MemoryMarshal" ||
            !RuntimeModels.ExactScope(reference.DeclaringType, PlatformAssemblies.SystemRuntime) ||
            method.ElementMethod.CallingConvention != MethodCallingConvention.Generic) return false;
        var arity = reference.Name == "Cast" ? 2 : 1;
        if (method.GenericArguments.Count != arity || method.ElementMethod.GenericParameters.Count != arity ||
            method.Parameters.Count is < 1 or > 2) return false;

        var source = method.ElementMethod.GenericParameters[0];
        var input = method.Parameters[0].ParameterType;
        var output = method.ReturnType;
        var writable = Spans.Writable(input);
        var second = method.Parameters.Count == 2 ? method.Parameters[1].ParameterType : null;
        var byteType = method.Module.TypeSystem.Byte;
        bool Reference(TypeReference? type) => type is ByReferenceType address && address.ElementType == source;
        var matches = method.Name switch
        {
            "GetReference" => second is null && Span(input, writable, source) && Reference(output),
            "GetArrayDataReference" => second is null && Reference(output) &&
                input is ArrayType { IsVector: true } array && array.ElementType == source,
            "AsBytes" => second is null && Span(input, writable, source) && Span(output, writable, byteType),
            "Cast" => second is null && Span(input, writable, source) &&
                Span(output, writable, method.ElementMethod.GenericParameters[1]),
            "CreateSpan" or "CreateReadOnlySpan" => Reference(input) && second?.MetadataType == MetadataType.Int32 &&
                Span(output, method.Name == "CreateSpan", source),
            "Read" => second is null && Span(input, false, byteType) && output == source,
            "TryRead" => Span(input, false, byteType) && Reference(second) &&
                output.MetadataType == MetadataType.Boolean,
            "Write" => Span(input, true, byteType) && Reference(second) && output.MetadataType == MetadataType.Void,
            "TryWrite" => Span(input, true, byteType) && Reference(second) &&
                output.MetadataType == MetadataType.Boolean,
            _ => false
        };
        if (!matches) return false;
        RuntimeModels.ValidateSignature(reference, architecture);
        var element = method.GenericArguments[0];
        if (Spans.ElementWidth(element, architecture) is null) return false;
        switch (method.Name)
        {
            case "GetReference":
            case "GetArrayDataReference":
            case "CreateSpan":
            case "CreateReadOnlySpan":
                return true;
            case "AsBytes":
            case "Cast":
                var target = arity == 1 ? 1 : Spans.ElementWidth(method.GenericArguments[1], architecture);
                return target is not null;
            default:
                MemoryTransfers.ValidateElement(element, method.Module, architecture);
                return true;
        }
    }

    private static bool Span(TypeReference type, bool writable, TypeReference element)
    {
        if (type is not GenericInstanceType { GenericArguments.Count: 1 } span ||
            span.ElementType.FullName != (writable ? "System.Span`1" : "System.ReadOnlySpan`1")) return false;
        var definition = span.ElementType;
        if (!RuntimeModels.ExactScope(definition, PlatformAssemblies.SystemRuntime))
            throw new InvalidDataException($"Unsupported type identity: {definition.FullName} [{definition.Scope}]");
        var argument = span.GenericArguments[0];
        return element is GenericParameter ? argument == element : argument.MetadataType == MetadataType.Byte;
    }
}
