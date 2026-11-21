using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class MemoryPrefixes
{
    internal static bool SupportedTarget(Instruction instruction) => instruction.OpCode.Code switch
    {
        Code.Cpblk or Code.Initblk or Code.Ldind_I1 or Code.Ldind_U1 or Code.Ldind_I2 or Code.Ldind_U2 or
            Code.Ldind_I4 or Code.Ldind_U4 or Code.Ldind_I8 or Code.Ldind_I or Code.Stind_I1 or
            Code.Stind_I2 or Code.Stind_I4 or Code.Stind_I8 or Code.Stind_I => instruction.Operand is null,
        Code.Ldfld or Code.Stfld => instruction.Operand is Mono.Cecil.FieldReference,
        Code.Ldobj or Code.Stobj => instruction.Operand is Mono.Cecil.TypeReference,
        _ => false
    };

    internal static int BlockAlignment(Instruction instruction) =>
        instruction.Previous?.OpCode.Code == Code.Unaligned ? (byte)instruction.Previous.Operand : 8;
}
