using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Direct tail transfers bind the prefix, call and return as one indivisible instruction sequence.
internal static class TailCalls
{
    internal static bool IsCall(Instruction instruction) =>
        instruction.OpCode.Code == Code.Call && instruction.Previous?.OpCode.Code == Code.Tail;

    internal static bool IsInterior(Instruction instruction) =>
        instruction.Previous?.OpCode.Code == Code.Tail ||
        instruction.Previous?.Previous?.OpCode.Code == Code.Tail;

    internal static void Validate(MethodDefinition method)
    {
        foreach (var prefix in method.Body.Instructions)
        {
            if (prefix.OpCode.Code != Code.Tail) continue;
            if (prefix.Operand is not null ||
                prefix.Next is not { OpCode.Code: Code.Call, Operand: MethodReference target } call ||
                call.Next is not { OpCode.Code: Code.Ret, Operand: null } ||
                target.ReturnType.FullName != method.ReturnType.FullName ||
                target.DeclaringType.Scope != method.Module ||
                InstructionTranslation.RuntimeModel(target) is not null)
                throw new InvalidDataException("Unsupported tail prefix: requires same-assembly call; ret with matching return type");
        }
    }
}
