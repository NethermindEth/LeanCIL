using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Resolve a constrained receiver to a struct method or the most specific static interface-level body, never boxing.
// `callvirt` dispatches an instance slot; `call` dispatches a static interface slot to a static implementation.
internal static class ConstrainedCalls
{
    // `Owner` is the closed type declaring the selected instance: the receiver, or the declaring interface of an
    // interface-level body. `MethodArguments` are the site's method type arguments, empty for a non-generic slot.
    internal sealed record Resolution(TypeDefinition Receiver, MethodDefinition Slot, MethodDefinition Target,
        TypeReference Owner, TypeReference[] MethodArguments)
    {
        internal bool Specialized => Owner is GenericInstanceType || MethodArguments.Length != 0;
    }

    internal sealed class TargetIndex(IEnumerable<MethodDefinition> methods)
    {
        readonly Dictionary<(MethodDefinition Definition, string Owner, string Arguments), MethodDefinition> targets =
            methods.Where(method => MethodSpecialization.Source(method) is not null)
                .ToDictionary(method => (MethodSpecialization.Definition(method),
                    MethodSpecialization.SignatureType(MethodSpecialization.DeclaringType(method)),
                    ArgumentKey(MethodSpecialization.Arguments(method)
                        .Take(MethodSpecialization.Arguments(method).Count -
                            MethodSpecialization.OwnerArguments(method).Count))));

        internal MethodDefinition Find(Resolution resolution) =>
            !resolution.Specialized ? resolution.Target :
                targets.GetValueOrDefault((resolution.Target, MethodSpecialization.SignatureType(resolution.Owner),
                    ArgumentKey(resolution.MethodArguments))) ??
                    throw new InvalidDataException("Unresolved constrained owner specialization");

        static string ArgumentKey(IEnumerable<TypeReference> arguments) =>
            string.Join(",", arguments.Select(MethodSpecialization.SignatureType));
    }

    internal static MethodDefinition Specialize(Resolution resolution, MethodSpecialization specializations)
    {
        if (!resolution.Specialized) return resolution.Target;
        var definition = resolution.Target;
        var member = new MethodReference(definition.Name, definition.ReturnType, resolution.Owner)
        {
            HasThis = definition.HasThis,
            CallingConvention = definition.CallingConvention
        };
        foreach (var parameter in definition.Parameters)
            member.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
        foreach (var parameter in definition.GenericParameters)
            member.GenericParameters.Add(new GenericParameter(parameter.Name, member));
        if (resolution.MethodArguments.Length == 0) return specializations.Instantiate(member);
        var instance = new GenericInstanceMethod(member);
        foreach (var argument in resolution.MethodArguments) instance.GenericArguments.Add(argument);
        return specializations.Instantiate(instance);
    }

    internal static Resolution Resolve(MethodDefinition caller, Instruction call,
        InstructionIndex instructions, string architecture)
    {
        if (call.OpCode.Code is not (Code.Callvirt or Code.Call) || call.Operand is not MethodReference reference ||
            call.Previous is not { OpCode.Code: Code.Constrained, Operand: TypeReference receiver })
            throw new InvalidDataException("callvirt requires an adjacent concrete constrained receiver");
        var instance = call.OpCode.Code == Code.Callvirt;
        if (receiver is GenericParameter || receiver is TypeSpecification && !GenericStructs.Is(receiver) ||
            receiver.Resolve() is not { } concrete || !Extracted(concrete.Module, caller.Module) ||
            !concrete.IsValueType ||
            receiver.ContainsGenericParameter || LayoutEvidence.Scope(receiver) != LayoutEvidence.Scope(concrete) ||
            receiver is not GenericInstanceType && receiver.FullName != concrete.FullName)
            throw new InvalidDataException("Constrained receiver must be a concrete struct of an extracted assembly");
        MetadataValidation.Layout(receiver, caller.Module, architecture);
        if (instructions.IsTarget(call))
            throw new InvalidDataException("Branch bypasses constrained receiver prefix");
        TypeReference[] methodArguments = reference is GenericInstanceMethod generic
            ? [.. generic.GenericArguments] : [];
        var member = reference is GenericInstanceMethod specialized ? specialized.ElementMethod : reference;
        if (member.Resolve() is not { } slot ||
            !Extracted(slot.Module, caller.Module) || member.Name != slot.Name ||
            !SameType(member.ReturnType, slot.ReturnType) ||
            !member.Parameters.Select(parameter => MethodSpecialization.SignatureType(parameter.ParameterType))
                .SequenceEqual(slot.Parameters.Select(parameter =>
                    MethodSpecialization.SignatureType(parameter.ParameterType))) ||
            member.HasThis != slot.HasThis || slot.HasThis != instance || slot.IsStatic == instance ||
            slot.IsConstructor || slot.GenericParameters.Count != methodArguments.Length ||
            instance && methodArguments.Length != 0 ||
            methodArguments.Any(argument => argument.ContainsGenericParameter) || member.ExplicitThis ||
            member.CallingConvention != Convention(methodArguments.Length))
            throw new InvalidDataException("Unsupported constrained method slot");
        ModifierTwins.Reject(slot);

        var owner = receiver as GenericInstanceType;
        var slotOwner = reference.DeclaringType as GenericInstanceType;
        if (reference.DeclaringType.ContainsGenericParameter ||
            (slotOwner?.GenericArguments.Count ?? 0) != slot.DeclaringType.GenericParameters.Count ||
            LayoutEvidence.Scope(reference.DeclaringType) != LayoutEvidence.Scope(slot.DeclaringType))
            throw new InvalidDataException("Unsupported constrained method owner");
        if (slot.DeclaringType == concrete && instance)
        {
            if (!SameType(reference.DeclaringType, receiver))
                throw new InvalidDataException("Constrained direct slot must match its receiver owner");
            return Checked(concrete, receiver, reference, slot, methodArguments);
        }
        // An instance slot with a body would run on a boxed receiver, so only abstract instance slots dispatch.
        var instanceDefault = instance && !slot.IsAbstract;
        if (!slot.DeclaringType.IsInterface || !slot.IsVirtual || instanceDefault ||
            !concrete.Interfaces.Any(implementation => SameType(
                GenericStructs.Substitute(implementation.InterfaceType, owner), reference.DeclaringType)))
            throw new InvalidDataException("Constrained call requires a directly implemented interface");

        var explicitTargets = concrete.Methods.Where(method =>
            method.Overrides.Any(overridden => overridden.Resolve() == slot &&
                SameType(GenericStructs.Substitute(overridden.DeclaringType, owner),
                    reference.DeclaringType))).ToArray();
        if (explicitTargets.Length != 0)
            return explicitTargets.Length == 1
                ? Checked(concrete, receiver, reference, explicitTargets[0], methodArguments)
                : throw new InvalidDataException(NoStructImplementation);
        var implicitTargets = concrete.Methods.Where(method =>
            method.IsPublic && method.GenericParameters.Count == methodArguments.Length &&
            method.Name == slot.Name && method.HasThis == instance &&
            SignatureMatches(method, reference, owner, methodArguments)).ToArray();
        // An unrecorded same-signature struct method beside a slot body is ambiguous, so it is rejected.
        if (implicitTargets.Length != 0)
            return implicitTargets.Length == 1 && slot.IsAbstract
                ? Checked(concrete, receiver, reference, implicitTargets[0], methodArguments)
                : throw new InvalidDataException(NoStructImplementation);
        if (instance) throw new InvalidDataException(NoStructImplementation);
        var (body, bodyOwner) = MostSpecific(concrete, owner, slot, reference.DeclaringType, caller.Module);
        return InterfaceBody(concrete, reference, slot, body, bodyOwner, methodArguments);
    }

    const string NoStructImplementation = "Constrained interface slot has no unique struct implementation";

    static Resolution Checked(TypeDefinition receiver, TypeReference closedReceiver, MethodReference slot,
        MethodDefinition target, TypeReference[] methodArguments)
    {
        var owner = closedReceiver as GenericInstanceType;
        if (target.DeclaringType != receiver || target.HasThis != slot.HasThis || target.IsStatic == slot.HasThis ||
            target.IsAbstract || !target.HasBody || target.IsConstructor ||
            target.GenericParameters.Count != methodArguments.Length || target.ExplicitThis ||
            target.CallingConvention != Convention(methodArguments.Length) ||
            !SignatureMatches(target, slot, owner, methodArguments))
            throw new InvalidDataException("Constrained call would require boxing or unsupported dispatch");
        return new(receiver, Slot(slot), target, closedReceiver, methodArguments);
    }

    // An interface-level body, the slot's own or a derived interface's MethodImpl, is instantiated at its closed
    // declaring interface and the site's method arguments.
    static Resolution InterfaceBody(TypeDefinition receiver, MethodReference slot, MethodDefinition slotDefinition,
        MethodDefinition target, TypeReference owner, TypeReference[] methodArguments)
    {
        if (!target.IsStatic || target.HasThis || target.IsAbstract || !target.HasBody ||
            !target.DeclaringType.IsInterface || target.ExplicitThis || target.IsConstructor ||
            target.GenericParameters.Count != methodArguments.Length ||
            target.CallingConvention != Convention(methodArguments.Length) ||
            !SignatureMatches(target, slot, owner as GenericInstanceType, methodArguments))
            throw new InvalidDataException("Constrained call would require boxing or unsupported dispatch");
        return new(receiver, slotDefinition, target, owner, methodArguments);
    }

    // The runtime runs the most specific interface-level body: the candidate, among the slot's own declaration
    // and every interface MethodImpl of it, whose interface inherits every other candidate's. As in Lean, the
    // receiver's interfaces must be closed under inheritance and declared in extracted assemblies, so no
    // candidate is unseen.
    static (MethodDefinition Body, TypeReference Owner) MostSpecific(TypeDefinition concrete,
        GenericInstanceType? owner, MethodDefinition slot, TypeReference closedSlotOwner, ModuleDefinition caller)
    {
        var listed = concrete.Interfaces.Select(implementation =>
            GenericStructs.Substitute(implementation.InterfaceType, owner)).ToArray();
        var names = listed.Select(MethodSpecialization.SignatureType).ToHashSet(StringComparer.Ordinal);
        List<(MethodDefinition Body, TypeReference Owner)> candidates = [(slot, closedSlotOwner)];
        foreach (var candidate in listed)
        {
            if (candidate.Resolve() is not { } declared || !Extracted(declared.Module, caller) ||
                !declared.IsInterface || !BaseInterfaces(candidate).All(parent =>
                    names.Contains(MethodSpecialization.SignatureType(parent))))
                throw new InvalidDataException("A static virtual slot's interface-level body requires every " +
                    "interface of the receiver, including inherited ones, to be listed and declared in an " +
                    "extracted assembly");
            foreach (var method in declared.Methods)
                if (method.Overrides.Any(overridden => (overridden.Resolve() ?? throw new InvalidDataException(
                        "Unresolved interface-level override: " + overridden.FullName)) == slot && SameType(
                        GenericStructs.Substitute(overridden.DeclaringType, candidate as GenericInstanceType),
                        closedSlotOwner)))
                    candidates.Add((method, candidate));
        }
        var winners = candidates.Where(candidate => candidates.All(other =>
            Derives(candidate.Owner, other.Owner, listed.Length))).ToArray();
        if (winners.Length != 1)
            throw new InvalidDataException("Static virtual slot has no unique most specific interface implementation");
        if (winners[0].Body.IsAbstract)
            throw new InvalidDataException(winners[0].Body == slot ? NoStructImplementation
                : "The most specific interface implementation of the static virtual slot re-abstracts it");
        return winners[0];
    }

    static IEnumerable<TypeReference> BaseInterfaces(TypeReference type) =>
        type.Resolve().Interfaces.Select(implementation =>
            GenericStructs.Substitute(implementation.InterfaceType, type as GenericInstanceType));

    // Inheritance through at most `depth` interface lists, matching the Lean walk's bound.
    static bool Derives(TypeReference derived, TypeReference ancestor, int depth) =>
        SameType(derived, ancestor) ||
        depth > 0 && BaseInterfaces(derived).Any(parent => Derives(parent, ancestor, depth - 1));

    // Dispatch stays inside one extracted assembly: the caller's own or a pinned reference.
    internal static bool Extracted(ModuleDefinition module, ModuleDefinition caller) =>
        module == caller || PinnedAssemblies.Active?.Contains(module) == true;

    static MethodDefinition Slot(MethodReference slot) =>
        (slot is GenericInstanceMethod generic ? generic.ElementMethod : slot).Resolve();

    static MethodCallingConvention Convention(int methodArity) =>
        methodArity == 0 ? MethodCallingConvention.Default : MethodCallingConvention.Generic;

    // The implementation's owner and method parameters are closed at the site's arguments before comparison.
    static bool SignatureMatches(MethodReference implementation, MethodReference slot, GenericInstanceType? owner,
        TypeReference[] methodArguments)
    {
        return SameType(Close(implementation.ReturnType, owner, methodArguments), CallReturnType.Resolve(slot)) &&
            implementation.Parameters.Count == slot.Parameters.Count &&
            implementation.Parameters.Zip(CallReturnType.Parameters(slot)).All(pair =>
                SameType(Close(pair.First.ParameterType, owner, methodArguments), pair.Second));
    }

    static TypeReference Close(TypeReference type, GenericInstanceType? owner, TypeReference[] methodArguments)
    {
        if (type is GenericParameter { Type: GenericParameterType.Method } parameter)
            return parameter.Position >= 0 && parameter.Position < methodArguments.Length
                ? methodArguments[parameter.Position]
                : throw new InvalidDataException("Unbound constrained method type parameter");
        if (type is GenericParameter) return GenericStructs.Substitute(type, owner);
        if (type is ArrayType { IsVector: true } array) return new ArrayType(Close(array.ElementType, owner,
            methodArguments));
        return TypeSubstitution.Components(type, component => Close(component, owner, methodArguments));
    }

    static bool SameType(TypeReference left, TypeReference right) =>
        MethodSpecialization.SignatureType(left) == MethodSpecialization.SignatureType(right);
}
