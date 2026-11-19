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
        NativeOperands.Certificate certificate, bool decoded, string? objectProof)
    {
        IEnumerable<string> states = method.Body.Instructions.Select(instruction =>
            certificate.Incoming.TryGetValue(instruction, out NativeOperands.StackType[]? stack)
                ? $"some [{string.Join(", ", stack.Reverse().Select(Kind))}]" : "none");
        lean.AppendLine($"def method{number}ScalarStates : Extraction.ScalarCertificate := [{string.Join(", ", states)}]");
        EmitInstructionChecks(lean, number, decoded, objectProof);
    }

    // The checks share the closed operands. Decoded methods already prove their code equality.
    static void EmitInstructionChecks(StringBuilder lean, int number, bool decoded, string? objectProof)
    {
        var method = $"method{number}";
        var flag = LeanText.Bool(decoded);
        var flow = $"{method}Closed {method}FeatureStates {method}ScalarStates {method}.code {flag}";
        var scalar = $"Extraction.ScalarFlowValid rawLayouts.toArray {flow}";
        var context = $"{method}.profile {method}.environment {method}.links";
        var code = $"Extraction.methodCode {context} {method}Reachable {method}Closed";
        var binding = $"{flag} = true -> {method}.code = {code}";
        var witness = decoded ? $"fun _ => {method}_decoded_code" : "fun h => False.elim (Bool.false_ne_true h)";
        var scalarEvidence = $"And ({scalar}) ({binding})";
        var unsafeCalls = $"Extraction.UnsafeCallsValid {method}Closed {method}Reachable {method}.code";
        var intrinsics = $"Extraction.ExactIntrinsicsValid {method}Closed {method}Reachable {method}";
        var models = $"Extraction.RuntimeModelsAgree {method}Closed {method}Reachable {method}";
        var otherChecks = $"And ({unsafeCalls}) (And ({intrinsics}) ({models}))";
        var objects = $"Extraction.ObjectOperandsValid {method}Closed {method}Reachable {method}";
        var remaining = $"And ({otherChecks}) ({objects})";
        var decided = objectProof is null ? remaining : otherChecks;
        var checkedTail = objectProof is null ? "checks.2" : $"(And.intro checks.2 ({objectProof}))";
        lean.AppendLine($"""
            theorem {method}_instruction_checks : And ({scalarEvidence}) ({remaining}) := by
              have checks : And ({scalar}) ({decided}) := {LeanEmitter.Decide}
              exact And.intro (And.intro checks.1 ({witness})) {checkedTail}
            #print axioms {method}_instruction_checks
            theorem {method}_scalars_validated : {scalarEvidence} := {method}_instruction_checks.1
            theorem {method}_unsafe_validated : {unsafeCalls} := {method}_instruction_checks.2.1.1
            theorem {method}_intrinsics_validated : {intrinsics} := {method}_instruction_checks.2.1.2.1
            theorem {method}_models_validated : {models} := {method}_instruction_checks.2.1.2.2
            theorem {method}_object_operands_validated : {objects} := {method}_instruction_checks.2.2
            """);
    }
}
