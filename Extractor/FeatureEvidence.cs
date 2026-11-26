using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Only serialize the worklist result. Lean recomputes transfers from the raw body
// and checks the entire fixed point, including every successor and emitted hole.
internal static class FeatureEvidence
{
    static string Fact(int? value) => value is int word ? $"some (BitVec.ofInt 32 ({word}))" : "none";

    // Lean accepts only known facts in increasing local order, so unknown locals cost nothing.
    static IEnumerable<string> KnownLocals(IReadOnlyList<int?> locals) =>
        locals.Select((value, index) => (value, index))
            .Where(entry => entry.value is not null)
            .Select(entry => $"({entry.index}, BitVec.ofInt 32 ({entry.value}))");

    internal static void Emit(StringBuilder lean, MethodDefinition method, int number,
        IReadOnlyDictionary<Instruction, FeatureConstants> incoming)
    {
        var states = method.Body.Instructions.Select(instruction =>
        {
            if (!incoming.TryGetValue(instruction, out FeatureConstants? state)) return "none";
            return $"some {{ stack := [{string.Join(", ", state.Stack.Reverse().Select(Fact))}], " +
                $"locals := [{string.Join(", ", KnownLocals(state.Locals))}] }}";
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
