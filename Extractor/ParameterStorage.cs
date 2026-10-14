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
            if (instruction.Operand is not ParameterDefinition parameter)
                throw new InvalidDataException($"Invalid argument operand: {instruction}");
            var index = MethodArguments.Index(method, parameter);
            if (instruction.OpCode.Code is Code.Ldarga or Code.Ldarga_S && MethodArguments.Type(method, index) is ByReferenceType)
                throw new InvalidDataException("Address of managed-reference argument is unsupported");
            indices.Add(index);
        }
        return [.. indices];
    }
}
