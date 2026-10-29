using System.Runtime.CompilerServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Raw call sites determine the only callable representation admitted for a native table body.
internal sealed class NativeDispatch
{
    static readonly ConditionalWeakTable<MethodDefinition, NativeDispatch> Cache = new();
    readonly Mono.Cecil.CallSite? signature;
    readonly HashSet<int> pointerLocals = [];

    NativeDispatch(MethodDefinition method)
    {
        var calls = method.Body.Instructions.Where(instruction => instruction.OpCode.Code == Code.Calli)
            .Select(instruction => (Mono.Cecil.CallSite)instruction.Operand).ToArray();
        if (calls.Length == 0 || calls.Any(site => !ManagedPointers.SameSignature(calls[0], site))) return;
        signature = calls[0];
        foreach (var instruction in method.Body.Instructions.Where(instruction => instruction.OpCode.Code == Code.Calli))
        {
            var previous = instruction.Previous;
            if (previous?.OpCode.Code == Code.Tail) previous = previous.Previous;
            if (previous?.OpCode.Code is Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or
                Code.Ldloc_2 or Code.Ldloc_3) pointerLocals.Add(FeatureConstants.Local(previous));
        }
    }

    internal static NativeDispatch For(MethodDefinition method) => Cache.GetValue(method, static value => new(value));

    internal string? Kind(TypeReference type, int? local = null)
    {
        if (signature is null) return null;
        var table = type is PointerType pointer && Native(pointer.ElementType);
        if (!table && !(local is { } index && pointerLocals.Contains(index) && Native(type))) return null;
        return $".{(table ? "methodTable" : "methodPointer")} {ManagedPointers.SignatureEvidence(signature)}";
    }

    static bool Native(TypeReference type) => type.MetadataType is MetadataType.IntPtr or MetadataType.UIntPtr;
}
