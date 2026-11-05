using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Lean records an `in` reference as a plain one and an `init` accessor as a plain void method, so a
// sibling equal once those modifiers are erased would be indistinguishable in the certificate.
// C# never emits such modifier-only overloads.
internal static class ModifierTwins
{
    internal static void Reject(MethodDefinition method)
    {
        var definition = MethodSpecialization.Definition(method);
        var siblings = definition.DeclaringType.Methods.Where(other => other.Name == definition.Name).ToArray();
        if (siblings.Length < 2 || !siblings.Any(Modified)) return;
        var erased = Erased(definition);
        var twins = siblings.Where(other => Erased(other) == erased).ToArray();
        if (twins.Length > 1)
            throw new InvalidDataException("Ambiguous modifier-only twin: " +
                string.Join(" | ", twins.Select(twin => twin.FullName)) +
                "; the certificate cannot distinguish modifier-only overloads");
    }

    static bool Modified(MethodDefinition method) => InitAccessors.Is(method.ReturnType) ||
        method.Parameters.Any(parameter => InReferences.Is(parameter.ParameterType));

    static string Erased(MethodDefinition method) =>
        $"{method.HasThis}:{method.ExplicitThis}:{(int)method.CallingConvention}:{method.GenericParameters.Count}:" +
        MethodSpecialization.SignatureType(InitAccessors.Return(method.ReturnType)) + "(" +
        string.Join(",", method.Parameters.Select(parameter =>
            MethodSpecialization.SignatureType(InReferences.Parameter(parameter.ParameterType)))) + ")";
}
