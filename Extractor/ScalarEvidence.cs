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
        LeanEmitter.EmitCertificate(lean, $"method{number}ScalarStates", "ScalarCertificate",
            "Option (List Extraction.ScalarKind)", states);
        var calls = method.Body.Instructions.Count(instruction =>
            instruction.OpCode.Code is Code.Call or Code.Callvirt or Code.Newobj or Code.Calli);
        EmitInstructionChecks(lean, number, method.Body.Instructions.Count, calls, objectProof);
    }

    // The checks share the closed operands in one decision when object shapes are not supplied as named facts.
    static void EmitInstructionChecks(StringBuilder lean, int number, int instructions, int calls,
        string? objectProof)
    {
        var method = $"method{number}";
        var flow = $"{method}Closed {method}FeatureStates {method}ScalarStates {method}.code";
        var scalar = $"Extraction.ScalarFlowValid {flow}";
        var objects = $"Extraction.ObjectOperandsValid {method}Closed {method}Reachable {method}";
        var heartbeats = LeanEmitter.InstructionCheckHeartbeats(instructions, calls);
        if (heartbeats > LeanEmitter.InstructionCheckHeartbeats(0, 0))
            lean.AppendLine($"set_option maxHeartbeats {heartbeats} in");
        if (objectProof is null)
        {
            lean.AppendLine($"""
                theorem {method}_instruction_checks : And ({scalar}) ({objects}) := {LeanEmitter.Decide}
                #print axioms {method}_instruction_checks
                theorem {method}_scalars_validated : {scalar} := {method}_instruction_checks.1
                theorem {method}_object_operands_validated : {objects} := {method}_instruction_checks.2
                """);
        }
        else
        {
            lean.AppendLine($"""
                theorem {method}_scalars_validated : {scalar} := {LeanEmitter.Decide}
                #print axioms {method}_scalars_validated
                theorem {method}_object_operands_validated : {objects} := {objectProof}
                """);
        }
    }
}
