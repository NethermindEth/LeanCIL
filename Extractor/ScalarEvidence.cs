using System.Text;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class ScalarEvidence
{
    static string Kind(NativeOperands.StackType value) => value.Metadata ?? value.Kind switch
    {
        NativeOperands.Kind.Word32 => ".word32",
        NativeOperands.Kind.Word64 => ".word64",
        NativeOperands.Kind.Native => ".native",
        NativeOperands.Kind.Reference => ".reference",
        NativeOperands.Kind.NullObject => ".nullObject",
        _ => Arrays.StackKind(value.Kind) ?? ".other"
    };

    internal static void Emit(StringBuilder lean, MethodDefinition method, int number,
        NativeOperands.Certificate certificate)
    {
        IEnumerable<string> states = method.Body.Instructions.Select(instruction =>
            certificate.Incoming.TryGetValue(instruction, out NativeOperands.StackType[]? stack)
                ? $"some [{string.Join(", ", stack.Reverse().Select(Kind))}]" : "none");
        lean.AppendLine($"def method{number}ScalarStates : Extraction.ScalarCertificate := [{string.Join(", ", states)}]");
        lean.AppendLine($"theorem method{number}_scalars_validated : Extraction.ScalarFlowValid rawLayouts.toArray " +
            $"method{number}Closed method{number}FeatureStates method{number}ScalarStates " +
            $"method{number}.code := {LeanEmitter.Decide}");
    }
}
