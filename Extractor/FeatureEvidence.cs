using System.Collections.Immutable;
using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Only serialize the worklist result. Lean recomputes transfers from the raw body
// and checks the entire fixed point, including every successor and emitted hole.
internal static class FeatureEvidence
{
    static string Fact(int? value) => value is int word ? $"some (BitVec.ofInt 32 ({word}))" : "none";

    internal static void Emit(StringBuilder lean, MethodDefinition method, int number,
        IReadOnlyDictionary<Instruction, FeatureConstants> incoming)
    {
        // Instructions sharing a local map emit the same facts in increasing slot order.
        var locals = new Dictionary<ImmutableSortedDictionary<int, int>, string>(ReferenceEqualityComparer.Instance);
        string KnownLocals(ImmutableSortedDictionary<int, int> facts)
        {
            if (facts.IsEmpty) return "";
            if (!locals.TryGetValue(facts, out var text))
            {
                text = string.Join(", ", facts.Select(entry => $"({entry.Key}, BitVec.ofInt 32 ({entry.Value}))"));
                locals.Add(facts, text);
            }
            return text;
        }

        var states = method.Body.Instructions.Select(instruction =>
        {
            if (!incoming.TryGetValue(instruction, out FeatureConstants? state)) return "none";
            return $"some {{ stack := [{string.Join(", ", state.Stack.Reverse().Select(Fact))}], " +
                $"locals := [{KnownLocals(state.KnownLocals)}] }}";
        });
        lean.AppendLine($"def method{number}FeatureStates : Extraction.FeatureCertificate := [{string.Join(", ", states)}]");
    }

    // Follows `methodEvidence`, whose callee certificates supply the words constant calls push. The obligation
    // therefore depends on the whole program and must stay out of any per-method component.
    internal static void EmitTheorem(StringBuilder lean, int number, string table = "methodEvidence") =>
        lean.AppendLine($"theorem method{number}_features_validated : Extraction.FeatureFlowValid rawLayouts.toArray " +
            // `MethodEvidenceValid` reads links by `linkIndex`; another reader makes its proof unfold the whole body.
            $"(Extraction.evidenceConstants {table}) (Extraction.linkIndex method{number}) " +
            $"method{number}Closed profile method{number}FeatureStates " +
            $"method{number}Reachable method{number}.code := {LeanEmitter.Decide}");
}
