using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Resolve a constrained receiver to a method declared by that concrete struct. No boxing fallback exists.
internal static class ConstrainedCalls
{
    internal sealed record Resolution(TypeDefinition Receiver, MethodDefinition Slot, MethodDefinition Target);

    internal sealed class TargetIndex(IEnumerable<MethodDefinition> methods)
    {
        readonly Dictionary<(MethodDefinition Definition, string Owner), MethodDefinition> targets = methods
            .Where(method => method.HasThis && MethodSpecialization.OwnerArguments(method).Count != 0 &&
                !MethodSpecialization.Definition(method).HasGenericParameters)
            .ToDictionary(method => (MethodSpecialization.Definition(method),
                MethodSpecialization.SignatureType(MethodSpecialization.DeclaringType(method))));

        internal MethodDefinition Find(MethodDefinition definition, TypeReference receiver) =>
            receiver is not GenericInstanceType ? definition :
                targets.GetValueOrDefault((definition, MethodSpecialization.SignatureType(receiver))) ??
                    throw new InvalidDataException("Unresolved constrained owner specialization");
    }

    internal static MethodDefinition Specialize(Resolution resolution, Instruction call,
        MethodSpecialization specializations)
    {
        if (call.Previous.Operand is not GenericInstanceType owner) return resolution.Target;
        var definition = resolution.Target;
        var reference = new MethodReference(definition.Name, definition.ReturnType, owner)
        {
            HasThis = definition.HasThis,
            CallingConvention = definition.CallingConvention
        };
        foreach (var parameter in definition.Parameters)
            reference.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
        return specializations.Instantiate(reference);
    }

    internal static Resolution Resolve(MethodDefinition caller, Instruction call,
        InstructionIndex instructions, string architecture)
    {
        if (call.OpCode.Code != Code.Callvirt || call.Operand is not MethodReference reference ||
            call.Previous is not { OpCode.Code: Code.Constrained, Operand: TypeReference receiver })
            throw new InvalidDataException("callvirt requires an adjacent concrete constrained receiver");
        if (receiver is GenericParameter || receiver is TypeSpecification && !GenericStructs.Is(receiver) ||
            receiver.Resolve() is not { } concrete || concrete.Module != caller.Module || !concrete.IsValueType ||
            receiver.ContainsGenericParameter || LayoutEvidence.Scope(receiver) != LayoutEvidence.Scope(concrete) ||
            receiver is not GenericInstanceType && receiver.FullName != concrete.FullName)
            throw new InvalidDataException("Constrained receiver must be a concrete same-assembly struct");
        MetadataValidation.Layout(receiver, caller.Module, architecture);
        if (instructions.IsTarget(call))
            throw new InvalidDataException("Branch bypasses constrained receiver prefix");
        if (reference is GenericInstanceMethod || reference.Resolve() is not { } slot ||
            slot.Module != caller.Module || reference.FullName != slot.FullName ||
            reference.HasThis != slot.HasThis || !slot.HasThis || slot.IsStatic || slot.IsConstructor ||
            slot.HasGenericParameters || reference.ExplicitThis ||
            reference.CallingConvention != MethodCallingConvention.Default)
            throw new InvalidDataException("Unsupported constrained method slot");

        var owner = receiver as GenericInstanceType;
        if (slot.DeclaringType == concrete)
        {
            if (owner is not null)
                throw new InvalidDataException("Constrained generic receivers require a non-generic interface slot");
            return Checked(concrete, slot, slot, owner);
        }
        if (!slot.DeclaringType.IsInterface || slot.DeclaringType.HasGenericParameters ||
            !slot.IsAbstract || !slot.IsVirtual ||
            !concrete.Interfaces.Any(implementation => implementation.InterfaceType.Resolve() == slot.DeclaringType))
            throw new InvalidDataException("Constrained call requires a directly implemented same-assembly interface");

        var explicitTargets = concrete.Methods.Where(method =>
            method.Overrides.Any(overridden => overridden.Resolve() == slot)).ToArray();
        var targets = explicitTargets.Length != 0 ? explicitTargets : concrete.Methods.Where(method =>
            method.IsPublic && !method.HasGenericParameters && method.Name == slot.Name &&
            SignatureMatches(method, slot, owner)).ToArray();
        if (targets.Length != 1)
            throw new InvalidDataException("Constrained interface slot has no unique struct implementation");
        return Checked(concrete, slot, targets[0], owner);
    }

    static Resolution Checked(TypeDefinition receiver, MethodDefinition slot, MethodDefinition target,
        GenericInstanceType? owner)
    {
        if (target.DeclaringType != receiver || !target.HasThis || target.IsStatic || target.IsAbstract ||
            !target.HasBody || target.IsConstructor || target.HasGenericParameters || target.ExplicitThis ||
            target.CallingConvention != MethodCallingConvention.Default || !SignatureMatches(target, slot, owner))
            throw new InvalidDataException("Constrained call would require boxing or unsupported dispatch");
        return new(receiver, slot, target);
    }

    static bool SignatureMatches(MethodReference implementation, MethodReference slot, GenericInstanceType? owner)
    {
        TypeReference Closed(TypeReference type) => owner is null ? type : GenericStructs.Substitute(type, owner);
        return SameType(Closed(implementation.ReturnType), slot.ReturnType) &&
            implementation.Parameters.Count == slot.Parameters.Count &&
            implementation.Parameters.Zip(slot.Parameters).All(pair =>
                SameType(Closed(pair.First.ParameterType), pair.Second.ParameterType));
    }

    static bool SameType(TypeReference left, TypeReference right) =>
        left.FullName == right.FullName && LayoutEvidence.Scope(left) == LayoutEvidence.Scope(right);
}
