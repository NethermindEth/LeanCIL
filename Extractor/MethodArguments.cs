using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class MethodArguments
{
    internal static TypeReference Type(MethodDefinition method, int index)
    {
        if (method.HasThis && index == 0)
        {
            var receiver = MethodSpecialization.DeclaringType(method);
            return ObjectTypes.Is(receiver) ? receiver : new ByReferenceType(receiver);
        }
        var parameter = index - (method.HasThis ? 1 : 0);
        if (parameter < 0 || parameter >= method.Parameters.Count)
            throw new InvalidDataException($"Invalid argument index {index}: {method.FullName}");
        return InReferences.Parameter(method.Parameters[parameter].ParameterType);
    }

    /// <summary>Whether argument <paramref name="index"/> is read as the whole word it holds, its declared type
    /// being no narrow integer.</summary>
    internal static bool Plain(MethodDefinition method, int index) => LeanEmitter.Narrow(Type(method, index)) is null;

    /// <summary>The argument (including the instance receiver) loaded by this CIL instruction.</summary>
    internal static int? LoadIndex(MethodDefinition method, Instruction site) => site.OpCode.Code switch
    {
        Code.Ldarg_0 => 0, Code.Ldarg_1 => 1, Code.Ldarg_2 => 2, Code.Ldarg_3 => 3,
        Code.Ldarg or Code.Ldarg_S => Index(method, (ParameterDefinition)site.Operand),
        _ => null
    };

    internal static int Index(MethodDefinition method, ParameterDefinition parameter)
    {
        if (method.HasThis && parameter == method.Body.ThisParameter) return 0;
        if (parameter.Index < 0 || parameter.Index >= method.Parameters.Count ||
            method.Parameters[parameter.Index] != parameter)
            throw new InvalidDataException($"Invalid argument operand: {method.FullName}");
        return parameter.Index + (method.HasThis ? 1 : 0);
    }
}
