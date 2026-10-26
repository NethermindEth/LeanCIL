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
        var states = method.Body.Instructions.Select(instruction =>
        {
            if (!incoming.TryGetValue(instruction, out FeatureConstants? state)) return "none";
            return $"some {{ stack := [{string.Join(", ", state.Stack.Reverse().Select(Fact))}], " +
                $"locals := [{string.Join(", ", state.Locals.Select(Fact))}] }}";
        });
        lean.AppendLine($"def method{number}FeatureStates : Extraction.FeatureCertificate := [{string.Join(", ", states)}]");
        lean.AppendLine($"theorem method{number}_features_validated : Extraction.FeatureFlowValid method{number}Closed profile method{number}FeatureStates method{number}Reachable method{number}.code := {LeanEmitter.Decide}");
    }
}
