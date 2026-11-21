using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

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
        NativeOperands.Certificate certificate, string? objectProof)
    {
        IEnumerable<string> states = method.Body.Instructions.Select(instruction =>
            certificate.Incoming.TryGetValue(instruction, out NativeOperands.StackType[]? stack)
                ? $"some [{string.Join(", ", stack.Reverse().Select(Kind))}]" : "none");
        lean.AppendLine($"def method{number}ScalarStates : Extraction.ScalarCertificate := [{string.Join(", ", states)}]");
        var calls = method.Body.Instructions.Count(instruction =>
            instruction.OpCode.Code is Code.Call or Code.Callvirt or Code.Newobj or Code.Calli);
        EmitInstructionChecks(lean, number, method.Body.Instructions.Count, calls, objectProof);
    }

    // The checks share the closed operands; the code equality comes from the method's decoding.
    static void EmitInstructionChecks(StringBuilder lean, int number, int instructions, int calls,
        string? objectProof)
    {
        var method = $"method{number}";
        var flow = $"{method}Closed {method}FeatureStates {method}ScalarStates {method}.code";
        var scalar = $"Extraction.ScalarFlowValid {flow}";
        var context = $"{method}.profile {method}.environment {method}.links";
        var code = $"Extraction.methodCode {context} {method}Reachable {method}Closed";
        var binding = $"{method}.code = {code}";
        var witness = $"{method}_decoded_code";
        var scalarEvidence = $"And ({scalar}) ({binding})";
        var unsafeCalls = $"Extraction.UnsafeCallsValid {method}Closed {method}Reachable {method}.code";
        var objects = $"Extraction.ObjectOperandsValid {method}Closed {method}Reachable {method}";
        var remaining = $"And ({unsafeCalls}) ({objects})";
        var decided = objectProof is null ? remaining : unsafeCalls;
        var checkedTail = objectProof is null ? "checks.2" : $"(And.intro checks.2 ({objectProof}))";
        var heartbeats = LeanEmitter.InstructionCheckHeartbeats(instructions, calls);
        if (heartbeats > LeanEmitter.InstructionCheckHeartbeats(0, 0))
            lean.AppendLine($"set_option maxHeartbeats {heartbeats} in");
        lean.AppendLine($"""
            theorem {method}_instruction_checks : And ({scalarEvidence}) ({remaining}) := by
              have checks : And ({scalar}) ({decided}) := {LeanEmitter.Decide}
              exact And.intro (And.intro checks.1 ({witness})) {checkedTail}
            #print axioms {method}_instruction_checks
            theorem {method}_scalars_validated : {scalarEvidence} := {method}_instruction_checks.1
            theorem {method}_unsafe_validated : {unsafeCalls} := {method}_instruction_checks.2.1
            theorem {method}_object_operands_validated : {objects} := {method}_instruction_checks.2.2
            """);
    }
}
