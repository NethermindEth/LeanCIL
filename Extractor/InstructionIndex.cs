using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Scoped to one body traversal; rebuild after changing instruction order or branch operands.
internal sealed class InstructionIndex
{
    readonly Dictionary<Instruction, int> positions = new();
    readonly HashSet<Instruction> targets = [];

    internal InstructionIndex(MethodDefinition method)
    {
        for (var index = 0; index < method.Body.Instructions.Count; index++)
        {
            var instruction = method.Body.Instructions[index];
            positions.TryAdd(instruction, index);
            if (instruction.Operand is Instruction target) targets.Add(target);
            else if (instruction.Operand is Instruction[] destinations) targets.UnionWith(destinations);
        }
    }

    internal int Position(Instruction instruction) => positions.GetValueOrDefault(instruction, -1);
    internal bool IsTarget(Instruction instruction) => targets.Contains(instruction);
}
