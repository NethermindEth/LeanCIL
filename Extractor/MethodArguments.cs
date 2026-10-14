using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class MethodArguments
{
    internal static TypeReference Type(MethodDefinition method, int index)
    {
        if (method.HasThis && index == 0) return new ByReferenceType(method.DeclaringType);
        var parameter = index - (method.HasThis ? 1 : 0);
        if (parameter < 0 || parameter >= method.Parameters.Count)
            throw new InvalidDataException($"Invalid argument index {index}: {method.FullName}");
        return method.Parameters[parameter].ParameterType;
    }

    internal static int Index(MethodDefinition method, ParameterDefinition parameter)
    {
        if (method.HasThis && parameter == method.Body.ThisParameter) return 0;
        if (parameter.Index < 0 || parameter.Index >= method.Parameters.Count ||
            method.Parameters[parameter.Index] != parameter)
            throw new InvalidDataException($"Invalid argument operand: {method.FullName}");
        return parameter.Index + (method.HasThis ? 1 : 0);
    }
}
