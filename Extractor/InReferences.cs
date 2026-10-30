using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Roslyn encodes `in` parameters of virtual, abstract and interface members as `T& modreq(InAttribute)`.
// The modifier only affects signature identity: the parameter is the same reference a non-virtual `in` passes.
internal static class InReferences
{
    const string Modifier = "System.Runtime.InteropServices.InAttribute";

    // Exactly System.Runtime's InAttribute, required directly on a modifier-free by-reference type.
    internal static ByReferenceType? Unwrap(TypeReference type) =>
        type is RequiredModifierType { ModifierType: var modifier, ElementType: ByReferenceType reference } &&
        modifier is not TypeSpecification && modifier.FullName == Modifier &&
        RuntimeModels.ExactScope(modifier.Scope, "System.Runtime") && !Modified(reference.ElementType)
            ? reference : null;

    internal static bool Is(TypeReference type) => Unwrap(type) is not null;

    // The type a parameter has at run time; other modifiers are left for their consumer to reject.
    internal static TypeReference Parameter(TypeReference type) => Unwrap(type) ?? type;

    // Substitutes inside an `in` reference and keeps its modifier; other types are substituted whole.
    // Span indexer returns keep their open `!0& modreq(InAttribute)` spelling, which Lean checks.
    internal static TypeReference Substitute(TypeReference type, Func<TypeReference, TypeReference> substitute) =>
        type is RequiredModifierType required && Unwrap(type) is { } reference
            ? new RequiredModifierType(required.ModifierType, substitute(reference)) : substitute(type);

    // Whether any custom modifier occurs in the type, including inside elements and generic arguments.
    internal static bool Modified(TypeReference type) => type switch
    {
        RequiredModifierType or OptionalModifierType => true,
        GenericInstanceType generic => generic.GenericArguments.Any(Modified) || Modified(generic.ElementType),
        TypeSpecification specification => Modified(specification.ElementType),
        _ => false
    };
}
