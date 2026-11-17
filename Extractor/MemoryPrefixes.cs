using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class MemoryPrefixes
{
    static bool SupportedTarget(Code code) => code is Code.Cpblk or Code.Initblk or
        Code.Ldind_I1 or Code.Ldind_U1 or Code.Ldind_I2 or Code.Ldind_U2 or
        Code.Ldind_I4 or Code.Ldind_U4 or Code.Ldind_I8 or Code.Ldind_I or
        Code.Stind_I1 or Code.Stind_I2 or Code.Stind_I4 or Code.Stind_I8 or Code.Stind_I or
        Code.Ldfld or Code.Stfld or Code.Ldobj or Code.Stobj;

    internal static void Validate(MethodDefinition method)
    {
        foreach (var instruction in method.Body.Instructions)
        {
            if (instruction.OpCode.Code == Code.Unaligned &&
                (instruction.Operand is not byte alignment || alignment is not (1 or 2 or 4) ||
                 instruction.Next is null || !SupportedTarget(instruction.Next.OpCode.Code)))
                throw new InvalidDataException("Unsupported or malformed unaligned prefix");
        }
    }

    internal static int BlockAlignment(Instruction instruction) =>
        instruction.Previous?.OpCode.Code == Code.Unaligned ? (byte)instruction.Previous.Operand : 8;
}
