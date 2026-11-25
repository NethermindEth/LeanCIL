using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class Reachability
{
    internal static HashSet<Instruction> Analyze(MethodDefinition method, FeatureProfile? selectedProfile = null,
        Instruction? managedConstructor = null)
        => Certify(method, selectedProfile, managedConstructor).Keys.ToHashSet();

    internal static Dictionary<Instruction, FeatureConstants> Certify(MethodDefinition method, FeatureProfile? selectedProfile = null,
        Instruction? managedConstructor = null)
    {
        FeatureProfile profile = selectedProfile ?? FeatureProfile.Scalar;
        profile.Validate();
        InstructionPrefixes.Validate(method);
        var instructions = method.Body.Instructions;
        var boundaries = instructions.ToHashSet();
        foreach (Instruction instruction in instructions)
        {
            if (instruction.OpCode.Code != Code.Switch &&
                instruction.OpCode.FlowControl is FlowControl.Branch or FlowControl.Cond_Branch &&
                (instruction.Operand is not Instruction target || !boundaries.Contains(target)))
                throw new InvalidDataException("Malformed control-flow target");
            if (instruction.OpCode.Code == Code.Switch &&
                (instruction.Operand is not Instruction[] targets || targets.Any(t => !boundaries.Contains(t))))
                throw new InvalidDataException("Malformed switch targets");
        }
        // Address-taken locals may be changed indirectly by calls or stores.
        // Never use them as constant facts, even before their address escapes.
        HashSet<int> addressed = instructions.Where(i => i.OpCode.Code is Code.Ldloca or Code.Ldloca_S)
            .Select(FeatureConstants.Local).ToHashSet();
        // A handler or the target of a leave can follow any instruction of its try, so no local keeps a fact.
        if (method.Body.HasExceptionHandlers) addressed.UnionWith(Enumerable.Range(0, method.Body.Variables.Count));
        Dictionary<Instruction, FeatureConstants> incoming = new()
        {
            [instructions[0]] = new(method.Body.Variables.Count)
        };
        Queue<Instruction> pending = new();
        HashSet<Instruction> queued = [instructions[0]];
        pending.Enqueue(instructions[0]);
        foreach (var handler in method.Body.ExceptionHandlers)
        {
            incoming[handler.HandlerStart] = FeatureConstants.HandlerEntry(method.Body.Variables.Count,
                handler.HandlerType == ExceptionHandlerType.Catch);
            if (queued.Add(handler.HandlerStart)) pending.Enqueue(handler.HandlerStart);
        }
        // Revisit successors when a backedge or join weakens a constant fact.
        // Facts only move from a constant to unknown, so this reaches a fixed point.
        var typeTests = TypeTests.Analyze(method);
        var throws = Throws.Analyze(method, managedConstructor);
        foreach (var handler in method.Body.ExceptionHandlers)
            if (typeTests.Interior.Contains(handler.HandlerStart) || throws.Interior.Contains(handler.HandlerStart) ||
                TailCalls.IsInterior(handler.HandlerStart))
                throw new InvalidDataException(
                    $"Exception handler starts inside a folded sequence: {handler.HandlerStart}");
        InstructionIndex? positions = null;
        while (pending.TryDequeue(out Instruction? i))
        {
            queued.Remove(i);
            if (i.OpCode.Code == Code.Tail) TailCalls.ValidateReachable(method, i, profile.Architecture);
            FeatureConstants state = incoming[i];
            var folded = typeTests.Results.TryGetValue(i, out bool same);
            var conditional = i.OpCode.FlowControl == FlowControl.Cond_Branch;
            var condition = conditional ? state.BranchCondition(i.OpCode.Code) : null;
            if (conditional && folded) condition = same;
            var selector = i.OpCode.Code == Code.Switch && state.Stack.Count != 0 ? state.Stack[^1] : null;
            state = state.Copy();
            var constant = ConstantReturns.Of(method, i, () => positions ??= new(method), profile);
            state.Step(i, method, profile, addressed, folded && !conditional ? same : null, constant);

            void Successor(Instruction target)
            {
                if (!boundaries.Contains(target))
                    throw new InvalidDataException("Malformed control-flow target");
                if (incoming.TryGetValue(target, out FeatureConstants? previous))
                {
                    if (!previous.Merge(state)) return;
                }
                else incoming[target] = state.Copy();
                if (queued.Add(target)) pending.Enqueue(target);
            }

            // A jump must not bypass the operands used to establish a folded result.
            void ValidateJump(Instruction target)
            {
                if (TailCalls.IsInterior(target))
                    throw new InvalidDataException($"Branch enters the middle of a tail transfer: {i}");
                if (typeTests.Interior.Contains(target))
                    throw new InvalidDataException($"Branch into a folded type comparison: {i}");
                if (throws.Interior.Contains(target))
                    throw new InvalidDataException($"Branch into a folded throw: {i}");
            }

            if (i.Operand is Instruction target)
            {
                ValidateJump(target);
                if (condition is bool taken)
                {
                    if (taken) Successor(target);
                    else Successor(i.Next ?? throw new InvalidDataException("Missing selected feature successor"));
                    continue;
                }
                Successor(target);
            }
            if (i.OpCode.Code == Code.Switch)
            {
                var targets = (Instruction[])i.Operand;
                if (selector is int index)
                {
                    foreach (var destination in targets) ValidateJump(destination);
                    Successor((uint)index < (uint)targets.Length ? targets[index] :
                        i.Next ?? throw new InvalidDataException("Missing selected switch successor"));
                    continue;
                }
                foreach (var destination in targets)
                {
                    ValidateJump(destination);
                    Successor(destination);
                }
            }
            if (i.OpCode.FlowControl is not (FlowControl.Return or FlowControl.Branch or FlowControl.Throw))
                Successor(i.Next ?? throw new InvalidDataException("Control falls off method"));
        }
        return incoming;
    }
}
