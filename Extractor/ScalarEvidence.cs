using System.Text;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class ScalarEvidence
{
    static string Kind(NativeOperands.StackType value) => value.Metadata?.ToLean() ?? value.Kind switch
    {
        NativeOperands.Kind.Word32 => ".word32",
        NativeOperands.Kind.Word64 => ".word64",
        NativeOperands.Kind.Native => ".native",
        NativeOperands.Kind.Reference => ".reference",
        NativeOperands.Kind.NullObject => ".nullObject",
        NativeOperands.Kind.Object => ".object",
        NativeOperands.Kind.Opaque => ".opaque",
        _ => Arrays.StackKind(value.Kind)?.ToLean() ?? ".other"
    };

    internal static void Emit(StringBuilder lean, MethodDefinition method, int number,
        NativeOperands.Certificate certificate, bool decoded)
    {
        IEnumerable<string> states = method.Body.Instructions.Select(instruction =>
            certificate.Incoming.TryGetValue(instruction, out NativeOperands.StackType[]? stack)
                ? $"some [{string.Join(", ", stack.Reverse().Select(Kind))}]" : "none");
        lean.AppendLine($"def method{number}ScalarStates : Extraction.ScalarCertificate := [{string.Join(", ", states)}]");
        var name = $"method{number}";
        var statesArgs = $"{name}Closed {name}FeatureStates {name}ScalarStates";
        var flag = LeanText.Bool(decoded);
        var check = $"Extraction.ScalarFlowValid rawLayouts.toArray {statesArgs} {name}.code {flag}";
        var binding = $"{flag} = true -> {name}.code = Instruction.ofRawCode none {name}Closed.code";
        var witness = decoded ? $"fun _ => {name}_decoded_code" : "fun h => False.elim (Bool.false_ne_true h)";
        var proof = $"And.intro ({LeanEmitter.Decide}) ({witness})";
        lean.AppendLine($"""theorem {name}_scalars_validated : And ({check}) ({binding}) := {proof}""");
    }
}
