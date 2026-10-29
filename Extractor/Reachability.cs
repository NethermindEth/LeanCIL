using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class Reachability
{
    internal static HashSet<Instruction> Analyze(MethodDefinition method, FeatureProfile? selectedProfile = null)
        => Certify(method, selectedProfile).Keys.ToHashSet();

    internal static Dictionary<Instruction, FeatureConstants> Certify(MethodDefinition method, FeatureProfile? selectedProfile = null)
    {
        FeatureProfile profile = selectedProfile ?? FeatureProfile.Scalar;
        profile.Validate();
        MemoryPrefixes.Validate(method);
        TailCalls.Validate(method);
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
        Dictionary<Instruction, FeatureConstants> incoming = new()
        {
            [instructions[0]] = new(method.Body.Variables.Count)
        };
        // Revisit successors when a backedge or join weakens a constant fact.
        // Facts only move from a constant to unknown, so this reaches a fixed point.
        var typeTests = TypeTests.Analyze(method);
        var throws = Throws.Analyze(method);
        var spans = Spans.Analyze(method);
        Queue<Instruction> pending = new();
        HashSet<Instruction> queued = [instructions[0]];
        pending.Enqueue(instructions[0]);
        while (pending.TryDequeue(out Instruction? i))
        {
            queued.Remove(i);
            FeatureConstants state = incoming[i];
            int? condition = state.Top;
            state = state.Copy();
            state.Step(i, method, profile, addressed, typeTests.Results.TryGetValue(i, out bool same) ? same : null);

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

            // Folded operands push nothing, so a fold must be entered at its start.
            void Jump(Instruction target)
            {
                if (TailCalls.IsInterior(target))
                    throw new InvalidDataException($"Branch enters the middle of a tail transfer: {i}");
                if (typeTests.Interior.Contains(target))
                    throw new InvalidDataException($"Branch into a folded type comparison: {i}");
                if (throws.Interior.Contains(target))
                    throw new InvalidDataException($"Branch into a folded throw: {i}");
                if (spans.Interior.Contains(target))
                    throw new InvalidDataException($"Branch into a folded span receiver: {i}");
                Successor(target);
            }

            if (condition is int known && i.OpCode.Code is Code.Brfalse or Code.Brfalse_S or Code.Brtrue or Code.Brtrue_S)
            {
                bool taken = (known != 0) == (i.OpCode.Code is Code.Brtrue or Code.Brtrue_S);
                if (taken) Jump((Instruction)i.Operand);
                else Successor(i.Next ?? throw new InvalidDataException("Missing selected feature successor"));
                continue;
            }
            if (i.Operand is Instruction target) Jump(target);
            if (i.OpCode.Code == Code.Switch)
                foreach (var destination in (Instruction[])i.Operand) Jump(destination);
            if (i.OpCode.FlowControl is not (FlowControl.Return or FlowControl.Branch or FlowControl.Throw))
                Successor(i.Next ?? throw new InvalidDataException("Control falls off method"));
        }
        return incoming;
    }
}
