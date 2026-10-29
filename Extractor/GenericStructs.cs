using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Closed owners retain their definition; only field and receiver signatures are substituted.
internal static class GenericStructs
{
    internal static bool DirectInterfaceConstraint(TypeReference constraint, TypeReference argument,
        ModuleDefinition module) =>
        constraint.Scope is ModuleDefinition && !constraint.ContainsGenericParameter &&
        constraint.Resolve() is { IsInterface: true } declared && declared.Module == module &&
        argument.Resolve() is { } concrete && concrete.Module == module && concrete.IsValueType &&
        concrete.Interfaces.Any(implemented => MethodSpecialization.SignatureType(Substitute(
            implemented.InterfaceType, argument as GenericInstanceType)) ==
            MethodSpecialization.SignatureType(constraint));

    internal static bool Is(TypeReference type) => type is GenericInstanceType generic &&
        generic.ElementType.Scope is ModuleDefinition && generic.IsValueType;

    internal static TypeReference Substitute(TypeReference type, GenericInstanceType? owner)
    {
        if (owner is null) return type;
        if (type is GenericParameter parameter)
        {
            if (parameter.Type != GenericParameterType.Type || parameter.Owner != owner.ElementType.Resolve() ||
                parameter.Position < 0 || parameter.Position >= owner.GenericArguments.Count)
                throw new InvalidDataException("Foreign or unbound generic struct parameter");
            return owner.GenericArguments[parameter.Position];
        }
        if (type is ArrayType array) return new ArrayType(Substitute(array.ElementType, owner), array.Rank);
        return TypeSubstitution.Components(type, component => Substitute(component, owner));
    }

    internal static void Validate(GenericInstanceType owner)
    {
        var definition = owner.Resolve();
        if (!definition.IsSequentialLayout || definition.GenericParameters.Count != owner.GenericArguments.Count ||
            owner.GenericArguments.Count == 0 || owner.ContainsGenericParameter)
            throw new InvalidDataException("Unsupported closed generic struct layout: " + owner.FullName);
        foreach (var argument in owner.GenericArguments)
            if (argument is PointerType or ByReferenceType or ArrayType || !argument.IsValueType)
                throw new InvalidDataException("Generic struct arguments must be reference-free value types");
        foreach (var (parameter, argument) in definition.GenericParameters.Zip(owner.GenericArguments))
        {
            if (((uint)parameter.Attributes & ~56u) != 0)
                throw new InvalidDataException("Unsupported generic struct constraint flags");
            foreach (var constraint in parameter.Constraints)
            {
                var type = constraint.ConstraintType;
                if (DirectInterfaceConstraint(type, argument, definition.Module)) continue;
                if (type is RequiredModifierType modifier &&
                    modifier.ModifierType.FullName == "System.Runtime.InteropServices.UnmanagedType" &&
                    RuntimeModels.ExactScope(modifier.ModifierType.Scope, "System.Runtime"))
                    type = modifier.ElementType;
                if (type.FullName != "System.ValueType" || !RuntimeModels.ExactScope(type.Scope, "System.Runtime"))
                    throw new InvalidDataException("Unsupported generic struct constraint type");
            }
        }
    }
}
