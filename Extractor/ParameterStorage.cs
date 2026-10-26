using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class ParameterStorage
{
    internal static int[] Analyze(MethodDefinition method, IEnumerable<Instruction> reachable)
    {
        var indices = new SortedSet<int>();
        foreach (var instruction in reachable)
        {
            if (instruction.OpCode.Code is not (Code.Starg or Code.Starg_S or Code.Ldarga or Code.Ldarga_S)) continue;
            if (instruction.Operand is not ParameterDefinition parameter)
                throw new InvalidDataException($"Invalid argument operand: {instruction}");
            var index = MethodArguments.Index(method, parameter);
            var address = instruction.OpCode.Code is Code.Ldarga or Code.Ldarga_S;
            if (address && MethodArguments.Type(method, index) is ByReferenceType or ArrayType)
                throw new InvalidDataException("Address of managed-reference or array-root argument is unsupported");
            indices.Add(index);
        }
        return [.. indices];
    }
}
