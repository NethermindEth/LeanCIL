using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Owners validate their own parameters; constructed types share the same recursive traversal.
internal static class TypeSubstitution
{
    internal static TypeReference Components(TypeReference type, Func<TypeReference, TypeReference> substitute)
    {
        if (type is ByReferenceType reference) return new ByReferenceType(substitute(reference.ElementType));
        if (type is RequiredModifierType required)
            return new RequiredModifierType(required.ModifierType, substitute(required.ElementType));
        if (type is PointerType pointer) return new PointerType(substitute(pointer.ElementType));
        if (type is GenericInstanceType generic)
        {
            var result = new GenericInstanceType(generic.ElementType);
            foreach (var argument in generic.GenericArguments) result.GenericArguments.Add(substitute(argument));
            return result;
        }
        return type;
    }
}
