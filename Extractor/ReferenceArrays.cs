using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Single-dimensional arrays of class references. An array is itself an object on the checked heap: its allocation
// records the runtime type `E[]`, and each element is a reference held in a slot, never in bytes.
internal static class ReferenceArrays
{
    /// <summary>The type is a zero-based, single-dimensional array whose element type is an admitted element.</summary>
    internal static bool Is(TypeReference type) =>
        type is ArrayType { IsVector: true } array && Element(array.ElementType);

    /// <summary>
    /// An admitted class or <c>string</c>. An array of such a static type holds, at run time, elements of a class
    /// derived from it, so the stored object's base classes decide covariance exactly. Lean binds an element named
    /// as an object only to a class of a pinned assembly or <c>string</c>: an interface, <c>object</c> or other
    /// class outside the pins may type an interface array, whose check the model cannot decide.
    /// </summary>
    internal static bool Element(TypeReference element) => ObjectTypes.Is(element) || ObjectTypes.IsString(element);

    /// <summary>
    /// The checked operation for an array instruction over an array of class references, or null when the
    /// instruction is not one; <c>ldlen</c> is the same instruction for every array.
    /// </summary>
    internal static Operation? Translate(Instruction instruction) => instruction.OpCode.Code switch
    {
        Code.Newarr when instruction.Operand is TypeReference element && Element(element) =>
            new NewArray(new(LayoutEvidence.Scope(element), element.FullName)),
        Code.Ldelem_Ref or Code.Stelem_Ref => new StackOperation(instruction.OpCode.Code),
        _ => null
    };
}
