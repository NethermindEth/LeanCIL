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
    /// An admitted class, or a non-generic class outside the model other than <c>System.Object</c>, such as
    /// <c>string</c>. An array of such a static type holds, at run time, elements of a class derived from it, so
    /// the stored object's base classes decide covariance exactly; an interface or <c>object</c> element would
    /// also admit interface arrays, whose check the model cannot decide.
    /// </summary>
    internal static bool Element(TypeReference element) => ObjectTypes.Is(element) ||
        element is not (TypeSpecification or GenericParameter) && !element.IsValueType &&
        element.FullName != "System.Object" && ObjectTypes.Opaque(element) &&
        element.Resolve() is { IsInterface: false, HasGenericParameters: false, IsValueType: false };

    /// <summary>
    /// The checked operation for an array instruction over an array of class references, or null when the
    /// instruction is not one. <paramref name="arrayOperand"/> says whether <c>ldlen</c> reads such an array.
    /// </summary>
    internal static Operation? Translate(Instruction instruction, bool arrayOperand) => instruction.OpCode.Code switch
    {
        Code.Newarr when instruction.Operand is TypeReference element && Element(element) =>
            new NewReferenceArray(LayoutEvidence.Scope(element), element.FullName),
        Code.Ldlen when arrayOperand => MemoryOperation.Of(new ReferenceArrayOperation(ReferenceArrayAccess.Length)),
        Code.Ldelem_Ref => MemoryOperation.Of(new ReferenceArrayOperation(ReferenceArrayAccess.Load)),
        Code.Stelem_Ref => MemoryOperation.Of(new ReferenceArrayOperation(ReferenceArrayAccess.Store)),
        Code.Ldelema or Code.Ldelem_Any or Code.Stelem_Any
            when instruction.Operand is TypeReference element &&
                (ObjectTypes.Candidate(element) || Element(element)) =>
            throw new InvalidDataException("Unsupported typed element access on an array of class references: " +
                instruction.OpCode.Name + " " + element.FullName +
                "\n  Element addresses would expose a reference slot; only ldelem.ref and stelem.ref are modelled."),
        _ => null
    };
}
