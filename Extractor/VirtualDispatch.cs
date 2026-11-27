using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// `callvirt` of a virtual method of an admitted class. The table maps every admitted, non-abstract class of the
// extraction that derives from the slot's class to the body the runtime selects for it; Lean re-resolves each entry
// from the dispatch catalog, and a receiver of any other class is a model fault, never a call.
internal static class VirtualDispatch
{
    /// <summary>One dispatch table entry: a class and the body the runtime runs on its instances.</summary>
    internal readonly record struct Entry(TypeDefinition Class, MethodDefinition Body);

    /// <summary>A callvirt without a constrained prefix of a virtual method declared by a class.</summary>
    internal static bool Is(Instruction call) =>
        ObjectTypes.ReceiverCall(call) && ((MethodReference)call.Operand).Resolve() is { IsVirtual: true };

    /// <summary>
    /// The dispatch table of a virtual call: each admitted concrete class deriving from the slot's declaring class,
    /// with its implementation, ordered by class name. Rejects by name every hierarchy the table cannot cover.
    /// </summary>
    internal static Entry[] Table(MethodReference reference)
    {
        var slot = reference.Resolve() ?? throw Rejected(reference, "The slot does not resolve.");
        if (!ObjectTypes.Is(reference.DeclaringType))
            throw Rejected(reference, "The slot is declared outside the admitted classes, so bodies that override " +
                "it can come from classes the extraction does not see.");
        var declaring = ObjectTypes.Validate(reference.DeclaringType);
        if (!slot.IsNewSlot)
            throw Rejected(reference, "The call names an override rather than the method that introduces the slot.");
        if (slot.HasGenericParameters || reference is GenericInstanceMethod)
            throw Rejected(reference, "Generic virtual methods are not modelled.");
        var table = new List<Entry>();
        foreach (var candidate in Hierarchy(reference))
        {
            if (!ObjectTypes.Is(candidate))
                throw Rejected(reference, candidate.FullName + " derives from " + declaring.FullName +
                    " but is not an admitted class, so the table would miss its instances.");
            if (!candidate.IsAbstract) table.Add(new(candidate, Implementation(reference, slot, declaring, candidate)));
        }
        if (table.Count == 0)
            throw Rejected(reference, "No admitted class implements the slot.");
        return [.. table.OrderBy(entry => LayoutEvidence.Identity(entry.Class), StringComparer.Ordinal)];
    }

    /// <summary>
    /// Why an unconstrained callvirt of a virtual or interface method outside the extracted classes has no
    /// dispatch table, or null for any other call.
    /// </summary>
    internal static string? Unresolvable(Instruction call)
    {
        // A callee the pins cannot resolve, such as a contract import, is left to the rejections that name it.
        if (call is not { OpCode.Code: Code.Callvirt, Operand: MethodReference reference } ||
            call.Previous?.OpCode.Code == Code.Constrained || ObjectTypes.ReceiverCall(call) ||
            reference.DeclaringType.Scope is AssemblyNameReference scope &&
                PinnedAssemblies.Active is { } pins && !pins.Resolves(scope) ||
            reference.Resolve() is not { IsVirtual: true } slot)
            return null;
        if (slot.DeclaringType.IsInterface)
            return "An interface slot needs an adjacent concrete constrained receiver; interface dispatch over " +
                "classes is not modelled, since no table maps them to the bodies implementing " +
                slot.DeclaringType.FullName + ".";
        return reference.DeclaringType is TypeSpecification
            ? "Virtual methods of generic classes are not modelled."
            : "The slot is declared outside the extracted assemblies, so bodies overriding it can come from " +
                "classes the extraction does not see.";
    }

    /// <summary>The slot's declaring class and every class of the pinned assemblies deriving from it.</summary>
    internal static IEnumerable<TypeDefinition> Hierarchy(MethodReference reference)
    {
        var declaring = reference.DeclaringType.Resolve();
        if (declaring is null) return [];
        return PinnedAssemblies.Active is { } pins
            ? pins.DispatchHierarchy(declaring) : DerivedClasses([declaring.Module], declaring);
    }

    /// <summary>Every class in the modules, including nested classes, that derives from the slot's class.</summary>
    internal static IEnumerable<TypeDefinition> DerivedClasses(IEnumerable<ModuleDefinition> modules,
        TypeDefinition declaring)
    {
        var derives = new Dictionary<TypeDefinition, bool?> { [declaring] = true };
        var path = new List<TypeDefinition>();
        foreach (var module in modules)
        foreach (var candidate in module.GetTypes())
        {
            if (candidate.IsValueType || candidate.IsInterface) continue;
            bool reachesOwner = false;
            for (var current = candidate; current is not null; current = current.BaseType?.Resolve())
            {
                if (derives.TryGetValue(current, out bool? known))
                {
                    reachesOwner = known ?? throw new InvalidDataException("Cyclic base class: " + current.FullName);
                    break;
                }
                // A pending answer belongs to this path until the chain reaches a known base or ends.
                derives.Add(current, null);
                path.Add(current);
            }
            foreach (var type in path) derives[type] = reachesOwner;
            path.Clear();
            if (reachesOwner) yield return candidate;
        }
    }

    // The body the runtime selects for `concrete`: the nearest class from `concrete` up to the slot's declarer with
    // a same-name, same-signature virtual method. Hiding, re-abstraction and explicit overrides are rejected by name.
    static MethodDefinition Implementation(MethodReference reference, MethodDefinition slot, TypeDefinition declaring,
        TypeDefinition concrete)
    {
        var chain = new List<TypeDefinition>();
        for (var current = concrete; current != declaring; current = current.BaseType.Resolve()) chain.Add(current);
        chain.Add(declaring);
        foreach (var owner in chain)
            foreach (var method in owner.Methods)
                if (method.Overrides.Any(target => chain.Any(other => other.FullName == target.DeclaringType.FullName)))
                    throw Rejected(reference, method.FullName + " overrides by an explicit MethodImpl, which the " +
                        "model does not resolve.");
        foreach (var owner in chain)
        {
            if (owner == declaring)
                return !slot.IsAbstract && slot.HasBody ? slot
                    : throw Rejected(reference, concrete.FullName + " inherits the abstract slot without a body.");
            var matches = owner.Methods.Where(method => method.IsVirtual && method.Name == slot.Name &&
                SameSignature(method, slot)).ToArray();
            if (matches.Length == 0) continue;
            if (matches.Length > 1) throw Rejected(reference, owner.FullName + " declares the slot twice.");
            var body = matches[0];
            if (body.IsNewSlot)
                throw Rejected(reference, body.FullName + " hides the slot with a new virtual method, which the " +
                    "model does not resolve.");
            if (body.IsAbstract || !body.HasBody)
                throw Rejected(reference, body.FullName + " re-abstracts the slot for " + concrete.FullName + ".");
            return body;
        }
        throw Rejected(reference, concrete.FullName + " does not reach the slot's class.");
    }

    static bool SameSignature(MethodDefinition method, MethodDefinition slot) =>
        method.HasThis == slot.HasThis && !method.HasGenericParameters &&
        StructuralSignatures.Current.Type(method.ReturnType) == StructuralSignatures.Current.Type(slot.ReturnType) &&
        method.Parameters.Select(parameter => StructuralSignatures.Current.Type(parameter.ParameterType))
            .SequenceEqual(slot.Parameters.Select(parameter => StructuralSignatures.Current.Type(parameter.ParameterType)));

    // The caller names the call site; this states why its hierarchy is not modelled.
    static InvalidDataException Rejected(MethodReference reference, string detail) =>
        new(detail.Replace("\n", "\n  ", StringComparison.Ordinal) + " (" + reference.Name + ")");
}
