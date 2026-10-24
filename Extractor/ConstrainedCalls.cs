using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Resolve a constrained receiver to a method declared by that concrete struct. No boxing fallback exists.
internal static class ConstrainedCalls
{
    internal sealed record Resolution(TypeDefinition Receiver, MethodDefinition Slot, MethodDefinition Target);

    internal static Resolution Resolve(MethodDefinition caller, Instruction call, string architecture)
    {
        if (call.OpCode.Code != Code.Callvirt || call.Operand is not MethodReference reference ||
            call.Previous is not { OpCode.Code: Code.Constrained, Operand: TypeReference receiver })
            throw new InvalidDataException("Virtual calls require an adjacent concrete constrained receiver");
        if (receiver is TypeSpecification or GenericParameter || receiver.Resolve() is not { } concrete ||
            concrete.Module != caller.Module || !concrete.IsValueType || concrete.HasGenericParameters ||
            receiver.FullName != concrete.FullName || LayoutEvidence.Scope(receiver) != LayoutEvidence.Scope(concrete))
            throw new InvalidDataException("Constrained receiver must be a concrete same-assembly struct");
        MetadataValidation.Layout(concrete, caller.Module, architecture);
        if (caller.Body.Instructions.Any(instruction => instruction.Operand == call ||
                instruction.Operand is Instruction[] targets && targets.Contains(call)))
            throw new InvalidDataException("Branch bypasses constrained receiver prefix");
        if (reference is GenericInstanceMethod || reference.Resolve() is not { } slot ||
            slot.Module != caller.Module || reference.FullName != slot.FullName ||
            reference.HasThis != slot.HasThis || !slot.HasThis || slot.IsStatic || slot.IsConstructor ||
            slot.HasGenericParameters || reference.ExplicitThis ||
            reference.CallingConvention != MethodCallingConvention.Default)
            throw new InvalidDataException("Unsupported constrained method slot");

        if (slot.DeclaringType == concrete)
            return Checked(concrete, slot, slot);
        if (!slot.DeclaringType.IsInterface || slot.DeclaringType.HasGenericParameters ||
            !slot.IsAbstract || !slot.IsVirtual ||
            !concrete.Interfaces.Any(implementation => implementation.InterfaceType.Resolve() == slot.DeclaringType))
            throw new InvalidDataException("Constrained call requires a directly implemented same-assembly interface");

        var explicitTargets = concrete.Methods.Where(method =>
            method.Overrides.Any(overridden => overridden.Resolve() == slot)).ToArray();
        var targets = explicitTargets.Length != 0 ? explicitTargets : concrete.Methods.Where(method =>
            method.IsPublic && method.Name == slot.Name && SignatureMatches(method, slot)).ToArray();
        if (targets.Length != 1)
            throw new InvalidDataException("Constrained interface slot has no unique struct implementation");
        return Checked(concrete, slot, targets[0]);
    }

    static Resolution Checked(TypeDefinition receiver, MethodDefinition slot, MethodDefinition target)
    {
        if (target.DeclaringType != receiver || !target.HasThis || target.IsStatic || target.IsAbstract ||
            !target.HasBody || target.IsConstructor || target.HasGenericParameters || target.ExplicitThis ||
            target.CallingConvention != MethodCallingConvention.Default || !SignatureMatches(target, slot))
            throw new InvalidDataException("Constrained call would require boxing or unsupported dispatch");
        return new(receiver, slot, target);
    }

    static bool SignatureMatches(MethodReference implementation, MethodReference slot) =>
        SameType(implementation.ReturnType, slot.ReturnType) &&
        implementation.Parameters.Count == slot.Parameters.Count &&
        implementation.Parameters.Zip(slot.Parameters).All(pair =>
            SameType(pair.First.ParameterType, pair.Second.ParameterType));

    static bool SameType(TypeReference left, TypeReference right) =>
        left.FullName == right.FullName && LayoutEvidence.Scope(left) == LayoutEvidence.Scope(right);
}
