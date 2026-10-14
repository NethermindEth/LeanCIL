using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class ParameterStorage
{
    internal static int[] Analyze(MethodDefinition method, FeatureProfile profile)
    {
        var indices = new SortedSet<int>();
        foreach (var instruction in Reachability.Analyze(method, profile))
        {
            if (instruction.OpCode.Code is not (Code.Starg or Code.Starg_S or Code.Ldarga or Code.Ldarga_S)) continue;
            if (instruction.Operand is not ParameterDefinition parameter || parameter.Index < 0 ||
                parameter.Index >= method.Parameters.Count || method.Parameters[parameter.Index] != parameter)
                throw new InvalidDataException($"Invalid argument operand: {instruction}");
            if (instruction.OpCode.Code is Code.Ldarga or Code.Ldarga_S && parameter.ParameterType is ByReferenceType)
                throw new InvalidDataException("Address of managed-reference argument is unsupported");
            indices.Add(parameter.Index);
        }
        return [.. indices];
    }
}
