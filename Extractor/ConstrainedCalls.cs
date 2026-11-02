using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Resolve a constrained receiver to a struct method or a static interface default body. No boxing fallback exists.
// `callvirt` dispatches an instance slot; `call` dispatches a static interface slot to a static implementation.
internal static class ConstrainedCalls
{
    // `Owner` is the closed type declaring the selected instance: the receiver, or the slot's interface for a
    // default body. `MethodArguments` are the site's method type arguments, empty for a non-generic slot.
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

    // A static slot whose resolved body is exactly `ldc.i4.0` or `ldc.i4.1; ret` returns that Boolean.
    // Lean recomputes the answer from the called program method, so this must never be broader.
    internal static bool? ConstantResult(MethodDefinition caller, Instruction call, InstructionIndex instructions,
        string architecture)
    {
        if (call.OpCode.Code != Code.Call || call.Previous?.OpCode.Code != Code.Constrained) return null;
        MethodDefinition target;
        try
        {
            target = Resolve(caller, call, instructions, architecture).Target;
        }
        catch (InvalidDataException)
        {
            // Validation reports the same failure for a reachable site; here it only means unknown.
            return null;
        }
        if (target.HasThis || target.Parameters.Count != 0 || target.ReturnType.FullName != "System.Boolean" ||
            LayoutEvidence.Scope(target.ReturnType) != TypeTests.RuntimeScope ||
            target.Body?.Instructions is not [var load, { OpCode.Code: Code.Ret }])
            return null;
        return load.OpCode.Code switch { Code.Ldc_I4_0 => false, Code.Ldc_I4_1 => true, _ => null };
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
            receiver.Resolve() is not { } concrete || concrete.Module != caller.Module || !concrete.IsValueType ||
            receiver.ContainsGenericParameter || LayoutEvidence.Scope(receiver) != LayoutEvidence.Scope(concrete) ||
            receiver is not GenericInstanceType && receiver.FullName != concrete.FullName)
            throw new InvalidDataException("Constrained receiver must be a concrete same-assembly struct");
        if (!instance && receiver is GenericInstanceType)
            throw new InvalidDataException("Static constrained slots on generic struct receivers are unsupported");
        MetadataValidation.Layout(receiver, caller.Module, architecture);
        if (instructions.IsTarget(call))
            throw new InvalidDataException("Branch bypasses constrained receiver prefix");
        TypeReference[] methodArguments = reference is GenericInstanceMethod generic
            ? [.. generic.GenericArguments] : [];
        var member = reference is GenericInstanceMethod specialized ? specialized.ElementMethod : reference;
        if (member.Resolve() is not { } slot ||
            slot.Module != caller.Module || member.Name != slot.Name ||
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
        InReferences.RejectTwins(slot);

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
        // A static virtual slot with a body runs only when the receiver records no implementation of it.
        var defaultBody = !instance && !slot.IsAbstract && slot.HasBody;
        if (!slot.DeclaringType.IsInterface || !slot.IsVirtual || !slot.IsAbstract && !defaultBody ||
            !concrete.Interfaces.Any(implementation => SameType(
                GenericStructs.Substitute(implementation.InterfaceType, owner), reference.DeclaringType)))
            throw new InvalidDataException("Constrained call requires a directly implemented same-assembly interface");

        var explicitTargets = concrete.Methods.Where(method =>
            method.Overrides.Any(overridden => overridden.Resolve() == slot &&
                SameType(GenericStructs.Substitute(overridden.DeclaringType, owner),
                    reference.DeclaringType))).ToArray();
        if (explicitTargets.Length != 0)
            return explicitTargets.Length == 1
                ? Checked(concrete, receiver, reference, explicitTargets[0], methodArguments)
                : throw new InvalidDataException("Constrained interface slot has no unique struct implementation");
        var implicitTargets = concrete.Methods.Where(method =>
            method.IsPublic && method.GenericParameters.Count == methodArguments.Length &&
            method.Name == slot.Name && method.HasThis == instance &&
            SignatureMatches(method, reference, owner, methodArguments)).ToArray();
        if (defaultBody && implicitTargets.Length == 0)
        {
            RequireUnshadowed(concrete, owner, slot, reference.DeclaringType);
            return Default(concrete, reference, slot, methodArguments);
        }
        // A default slot with an unrecorded same-signature struct method is ambiguous, so it is rejected.
        if (implicitTargets.Length != 1 || defaultBody)
            throw new InvalidDataException("Constrained interface slot has no unique struct implementation");
        return Checked(concrete, receiver, reference, implicitTargets[0], methodArguments);
    }

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

    // The default body is the slot itself, instantiated at the site's closed interface and method arguments.
    static Resolution Default(TypeDefinition receiver, MethodReference slot, MethodDefinition target,
        TypeReference[] methodArguments)
    {
        if (!target.IsStatic || target.HasThis || target.IsAbstract || !target.HasBody || !target.IsVirtual ||
            !target.DeclaringType.IsInterface || target.ExplicitThis ||
            target.CallingConvention != Convention(methodArguments.Length) ||
            !SignatureMatches(target, slot, slot.DeclaringType as GenericInstanceType, methodArguments))
            throw new InvalidDataException("Constrained call would require boxing or unsupported dispatch");
        return new(receiver, target, target, slot.DeclaringType, methodArguments);
    }

    // An interface-level MethodImpl of the slot on any interface of the receiver is more specific than the
    // default body. As in Lean, the receiver's interfaces must all be same-assembly and closed under inheritance.
    static void RequireUnshadowed(TypeDefinition concrete, GenericInstanceType? owner, MethodDefinition slot,
        TypeReference closedSlotOwner)
    {
        var listed = concrete.Interfaces.Select(implementation =>
            GenericStructs.Substitute(implementation.InterfaceType, owner)).ToArray();
        var names = listed.Select(MethodSpecialization.SignatureType).ToHashSet(StringComparer.Ordinal);
        foreach (var candidate in listed)
        {
            if (candidate.Resolve() is not { } declared || declared.Module != concrete.Module ||
                !declared.Interfaces.All(implementation => names.Contains(MethodSpecialization.SignatureType(
                    GenericStructs.Substitute(implementation.InterfaceType, candidate as GenericInstanceType)))))
                throw new InvalidDataException("A static virtual default body requires every interface of the " +
                    "receiver, including inherited ones, to be listed and declared in this assembly");
            if (declared.Methods.Any(method => method.Overrides.Any(overridden =>
                    overridden.Resolve() is not { } resolved || resolved == slot && SameType(
                        GenericStructs.Substitute(overridden.DeclaringType, candidate as GenericInstanceType),
                        closedSlotOwner))))
                throw new InvalidDataException(
                    "Another interface of the receiver re-implements the static virtual slot");
        }
    }

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
