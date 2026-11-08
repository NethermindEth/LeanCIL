using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Single-dimensional arrays of admitted class instances. An array is itself an object on the checked heap: its
// allocation records the runtime type `E[]`, and each element is a reference held in a slot, never in bytes.
internal static class ReferenceArrays
{
    /// <summary>The type is a zero-based, single-dimensional array of an admitted class.</summary>
    internal static bool Is(TypeReference type) =>
        type is ArrayType { IsVector: true } array && ObjectTypes.Is(array.ElementType);

    /// <summary>
    /// The checked operation for an array instruction over an array of class references, or null when the
    /// instruction is not one. <paramref name="arrayOperand"/> says whether <c>ldlen</c> reads such an array.
    /// </summary>
    internal static string? Translate(Instruction instruction, bool arrayOperand) => instruction.OpCode.Code switch
    {
        Code.Newarr when instruction.Operand is TypeReference element && ObjectTypes.Is(element) =>
            $".newReferenceArray ({GenericEvidence.ObjectType(element)})",
        Code.Ldlen when arrayOperand => ".memory .referenceArrayLength",
        Code.Ldelem_Ref => ".memory .referenceArrayLoad",
        Code.Stelem_Ref => ".memory .referenceArrayStore",
        Code.Ldelema or Code.Ldelem_Any or Code.Stelem_Any
            when instruction.Operand is TypeReference element && ObjectTypes.Candidate(element) =>
            throw new InvalidDataException("Unsupported typed element access on an array of class references: " +
                instruction.OpCode.Name + " " + element.FullName +
                "\n  Element addresses would expose a reference slot; only ldelem.ref and stelem.ref are modelled."),
        _ => null
    };
}
