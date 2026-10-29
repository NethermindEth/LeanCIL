using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Closed owners retain their definition; only field and receiver signatures are substituted.
internal static class GenericStructs
{
    internal static bool Is(TypeReference type) => type is GenericInstanceType generic &&
        generic.ElementType.Scope is ModuleDefinition && generic.IsValueType;

    internal static TypeReference Substitute(TypeReference type, GenericInstanceType owner)
    {
        if (type is GenericParameter parameter)
        {
            if (parameter.Type != GenericParameterType.Type || parameter.Owner != owner.ElementType.Resolve() ||
                parameter.Position < 0 || parameter.Position >= owner.GenericArguments.Count)
                throw new InvalidDataException("Foreign or unbound generic struct parameter");
            return owner.GenericArguments[parameter.Position];
        }
        if (type is GenericInstanceType nested)
        {
            var closed = new GenericInstanceType(nested.ElementType);
            foreach (var argument in nested.GenericArguments) closed.GenericArguments.Add(Substitute(argument, owner));
            return closed;
        }
        if (type is ByReferenceType reference) return new ByReferenceType(Substitute(reference.ElementType, owner));
        if (type is PointerType pointer) return new PointerType(Substitute(pointer.ElementType, owner));
        if (type is ArrayType array) return new ArrayType(Substitute(array.ElementType, owner), array.Rank);
        return type;
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
        foreach (var parameter in definition.GenericParameters)
        {
            if (((uint)parameter.Attributes & ~56u) != 0)
                throw new InvalidDataException("Unsupported generic struct constraint flags");
            foreach (var constraint in parameter.Constraints)
            {
                var type = constraint.ConstraintType;
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
