using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Reinterpretation retains the supplied storage; exact generic signatures determine both widths.
internal static class SpanReinterpretation
{
    internal static string? Translate(MethodReference reference, string architecture)
    {
        if (reference.DeclaringType.FullName != "System.Runtime.InteropServices.MemoryMarshal" ||
            !RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") ||
            reference is not GenericInstanceMethod generic || reference.HasThis || reference.ExplicitThis ||
            reference.Parameters.Count != 1 ||
            (generic.ElementMethod.CallingConvention & ~MethodCallingConvention.Generic) !=
                MethodCallingConvention.Default) return null;
        var asBytes = reference.Name == "AsBytes";
        var arity = asBytes ? 1 : 2;
        if ((!asBytes && reference.Name != "Cast") || generic.GenericArguments.Count != arity ||
            generic.ElementMethod.GenericParameters.Count != arity) return null;
        bool Parameter(TypeReference type, int position) => type is GenericParameter parameter &&
            parameter.Type == GenericParameterType.Method && parameter.Position == position &&
            parameter.Owner == generic.ElementMethod;
        if (reference.Parameters[0].ParameterType is not GenericInstanceType input ||
            input.ElementType.FullName is not ("System.Span`1" or "System.ReadOnlySpan`1") ||
            input.GenericArguments.Count != 1 || !Parameter(input.GenericArguments[0], 0) ||
            reference.ReturnType is not GenericInstanceType output ||
            output.ElementType.FullName != input.ElementType.FullName || output.GenericArguments.Count != 1 ||
            !(asBytes ? output.GenericArguments[0].FullName == "System.Byte" :
                Parameter(output.GenericArguments[0], 1))) return null;
        RuntimeModels.ValidateSignature(reference, architecture);
        var source = Spans.ElementWidth(generic.GenericArguments[0]);
        var target = asBytes ? 1 : Spans.ElementWidth(generic.GenericArguments[1]);
        if (source is null || target is null) return null;
        var writable = input.ElementType.FullName == "System.Span`1";
        return $".memory (.spanReinterpret {source} {target} {writable.ToString().ToLowerInvariant()})";
    }
}

