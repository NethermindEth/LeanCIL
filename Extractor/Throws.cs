using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Folds `throw new E(...)` with string or null arguments into a fault naming E. This mirrors
// CIL.Extraction.throwFold; Lean rechecks every raised type. The constructor is not run.
internal static class Throws
{
    internal sealed record Analysis(Dictionary<Instruction, string> Raises, HashSet<Instruction> Operands, HashSet<Instruction> Interior);

    // Exact framework constructors whose string arguments cannot change the raised type.
    // Keep the same allowlist in CIL.Extraction.exceptionConstructor.
    static bool ExceptionConstructor(string type, int count) =>
        (count <= 1 && type is "System.Exception" or "System.SystemException" or "System.ApplicationException" or
            "System.ArithmeticException" or "System.DivideByZeroException" or "System.OverflowException" or
            "System.InvalidOperationException" or "System.NotSupportedException" or "System.NotImplementedException" or
            "System.ArgumentException" or "System.ArgumentNullException" or "System.ArgumentOutOfRangeException" or
            "System.IndexOutOfRangeException" or "System.NullReferenceException" or "System.FormatException") ||
        (count == 2 && type is "System.ArgumentException" or "System.ArgumentNullException" or "System.ArgumentOutOfRangeException");

    static string? Raised(Instruction instruction, int count) =>
        instruction.OpCode.Code == Code.Newobj && instruction.Operand is MethodReference constructor &&
        constructor is not GenericInstanceMethod && constructor.Name == ".ctor" && constructor.HasThis &&
        !constructor.ExplicitThis && constructor.CallingConvention == MethodCallingConvention.Default && !constructor.HasGenericParameters &&
        constructor.ReturnType.MetadataType == MetadataType.Void && constructor.Parameters.Count == count &&
        constructor.Parameters.All(p => p.ParameterType.MetadataType == MetadataType.String) &&
        constructor.DeclaringType is not TypeSpecification && !constructor.DeclaringType.IsValueType &&
        ExceptionConstructor(constructor.DeclaringType.FullName, count) &&
        LayoutEvidence.Scope(constructor.DeclaringType) == TypeTests.RuntimeScope ? constructor.DeclaringType.FullName : null;

    static readonly System.Runtime.CompilerServices.ConditionalWeakTable<MethodDefinition, Analysis> cache = new();

    internal static Analysis Analyze(MethodDefinition method) => cache.GetValue(method, Compute);

    static Analysis Compute(MethodDefinition method)
    {
        var code = method.Body.Instructions;
        var analysis = new Analysis([], [], []);
        for (int at = 0; at < code.Count; at++)
        {
            int count = 0;
            while (at + count < code.Count && code[at + count].OpCode.Code is Code.Ldstr or Code.Ldnull) count++;
            int raise = at + count + 1;
            if (raise >= code.Count || code[raise].OpCode.Code != Code.Throw || Raised(code[at + count], count) is not string name)
                continue;
            for (int k = at; k < raise; k++) analysis.Operands.Add(code[k]);
            for (int k = at + 1; k <= raise; k++) analysis.Interior.Add(code[k]);
            analysis.Raises.Add(code[raise], name);
            at = raise;
        }
        return analysis;
    }
}
