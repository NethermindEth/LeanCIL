using System.Runtime.CompilerServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// The Boolean a parameterless static call returns, read from its program callee's own feature certificate: the same
// 0 or 1 at every reachable `ret`. Lean reads that certificate (`constantReturn`), so this must never be broader.
internal static class ConstantReturns
{
    // Callees being certified on this thread; one reached again is on a call cycle and stays unknown.
    [ThreadStatic] static Dictionary<MethodDefinition, bool?>? session;

    internal static bool? Of(MethodDefinition caller, Instruction call, Func<InstructionIndex> positions,
        FeatureProfile profile)
    {
        // Lean folds neither a tail call nor any call with `this`, arguments or a non-Boolean result.
        if (call.OpCode.Code != Code.Call || call.Previous?.OpCode.Code == Code.Tail ||
            call.Operand is not MethodReference { HasThis: false, Parameters.Count: 0 } reference ||
            reference.ReturnType.FullName != "System.Boolean")
            return null;
        var callee = call.Previous?.OpCode.Code == Code.Constrained
            ? Constrained(caller, call, positions(), profile.Architecture)
            : Plain(caller, call, reference, profile.Architecture);
        return callee is null ? null : Returned(callee, profile);
    }

    // The callee body, extracted from a pinned module; an import or framework method is never constant.
    static MethodDefinition? Plain(MethodDefinition caller, Instruction call, MethodReference reference,
        string architecture)
    {
        var callee = reference switch
        {
            MethodDefinition definition => definition,
            GenericInstanceMethod or { DeclaringType: GenericInstanceType } => Close(call, architecture,
                () => reference.Resolve() is { } definition
                    ? new MethodSpecialization(definition.Module, architecture).Instantiate(reference) : null),
            _ => Resolved(reference)
        };
        return callee is not null && ConstrainedCalls.Extracted(callee.Module, caller.Module) ? callee : null;
    }

    // A callee in an imported or otherwise unpinned assembly fails resolution; for folding that only means unknown.
    static MethodDefinition? Resolved(MethodReference reference)
    {
        try
        {
            return reference.Resolve();
        }
        catch (InvalidDataException)
        {
            return null;
        }
    }

    // The resolved body, closed over the receiver's and site's type arguments when it is generic.
    static MethodDefinition? Constrained(MethodDefinition caller, Instruction call, InstructionIndex positions,
        string architecture)
    {
        ConstrainedCalls.Resolution resolution;
        try
        {
            resolution = ConstrainedCalls.Resolve(caller, call, positions, architecture);
        }
        catch (InvalidDataException)
        {
            // Validation reports the same failure for a reachable site; here it only means unknown.
            return null;
        }
        if (!ConstrainedCalls.Extracted(resolution.Target.Module, caller.Module)) return null;
        return !resolution.Specialized ? resolution.Target : Close(call, architecture, () =>
            ConstrainedCalls.Specialize(resolution, new MethodSpecialization(resolution.Target.Module, architecture)));
    }

    // Validation certifies a caller before it rewrites the caller's generic calls to the program's closed bodies, so
    // both passes close the callee the same way; specialization is deterministic, so the bodies certify alike.
    static readonly ConditionalWeakTable<Instruction, Closed> closed = new();

    sealed record Closed(string Architecture, MethodDefinition? Body);

    static MethodDefinition? Close(Instruction call, string architecture, Func<MethodDefinition?> instantiate)
    {
        if (closed.TryGetValue(call, out Closed? known) && known.Architecture == architecture) return known.Body;
        MethodDefinition? body;
        try
        {
            body = instantiate();
        }
        catch (InvalidDataException)
        {
            // Validation rejects the same instantiation at a reachable site; here it only means unknown.
            body = null;
        }
        closed.AddOrUpdate(call, new(architecture, body));
        return body;
    }

    static bool? Returned(MethodDefinition callee, FeatureProfile profile)
    {
        if (callee.HasThis || callee.Parameters.Count != 0 || !callee.HasBody ||
            callee.ReturnType.FullName != "System.Boolean" ||
            LayoutEvidence.Scope(callee.ReturnType) != TypeTests.RuntimeScope)
            return null;
        var outermost = session is null;
        session ??= [];
        try
        {
            if (session.TryGetValue(callee, out bool? known)) return known;
            session[callee] = null;
            bool? result;
            try
            {
                result = Word(Reachability.Certify(callee, profile));
            }
            catch (InvalidDataException)
            {
                // The callee's own validation reports the failure; a caller only loses the fold.
                result = null;
            }
            session[callee] = result;
            return result;
        }
        finally
        {
            if (outermost) session = null;
        }
    }

    static bool? Word(Dictionary<Instruction, FeatureConstants> states)
    {
        int? word = null;
        foreach (var (instruction, state) in states)
        {
            if (instruction.OpCode.Code != Code.Ret) continue;
            if (state.Stack is not [.., int value] || value is not (0 or 1) || word is int seen && seen != value)
                return null;
            word = value;
        }
        return word is int found ? found == 1 : null;
    }
}
