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

    internal static void ValidateReachable(MethodDefinition method, Instruction prefix, string architecture = "scalar")
    {
        if (prefix.Next is { OpCode.Code: Code.Calli, Operand: Mono.Cecil.CallSite indirect })
        {
            ManagedPointers.Validate(indirect, method.Module, architecture);
            if (ManagedPointers.TypeEvidence(indirect.ReturnType) !=
                ManagedPointers.TypeEvidence(InitAccessors.Return(method.ReturnType)))
                throw new InvalidDataException("Unsupported tail prefix: mismatched indirect return type");
            return;
        }
        if (prefix.Next is not { OpCode.Code: Code.Call, Operand: MethodReference target } ||
            InitAccessors.Return(target.ReturnType).FullName !=
                InitAccessors.Return(method.ReturnType).FullName ||
            target.DeclaringType.Scope != method.Module)
            throw new InvalidDataException(
                "Unsupported tail prefix: requires same-assembly direct call with matching return type");
        RuntimeModels.ValidateCallScope(target);
    }
}
