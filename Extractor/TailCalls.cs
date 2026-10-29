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

    internal static void ValidateStructure(MethodDefinition method)
    {
        foreach (var prefix in method.Body.Instructions)
        {
            if (prefix.OpCode.Code != Code.Tail) continue;
            if (prefix.Operand is not null || prefix.Next is not { } call ||
                call.OpCode.Code is not (Code.Call or Code.Callvirt or Code.Calli) ||
                call.Next is not { OpCode.Code: Code.Ret, Operand: null })
                throw new InvalidDataException("Unsupported tail prefix: requires an adjacent call and return");
        }
    }

    internal static void ValidateReachable(MethodDefinition method, Instruction prefix)
    {
        if (prefix.Next is not { OpCode.Code: Code.Call, Operand: MethodReference target } ||
            target.ReturnType.FullName != method.ReturnType.FullName ||
            target.DeclaringType.Scope != method.Module ||
            InstructionTranslation.RuntimeModel(target) is not null)
            throw new InvalidDataException(
                "Unsupported tail prefix: requires same-assembly direct call with matching return type");
    }
}
