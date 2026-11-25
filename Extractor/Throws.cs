using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Folds recognized exception constructors into named faults. This mirrors
// CIL.Extraction.foldRoles; Lean rechecks every raised type. The constructor is not run.
internal static class Throws
{
    const int ArgumentLimit = 4;
    /// <summary>
    /// The folded raises with their operands and interiors, and the instructions of candidates left unfolded because a
    /// clause protects their throw: a folded raise carries no object for a catch to test.
    /// </summary>
    internal sealed record Analysis(
        Dictionary<Instruction, ExceptionType> Raises, HashSet<Instruction> Operands, HashSet<Instruction> Interior,
        HashSet<Instruction> Protected);

    const string Message = "System.String";
    const string Inner = "System.Exception";
    const string Actual = "System.Object";

    // Keep the same parameter lists in CIL.Extraction.admittedParameters.
    static string[][] AdmittedParameters(ExceptionType exception) => exception switch
    {
        ExceptionType.BaseException or ExceptionType.InvalidOperation => [[], [Message], [Message, Inner]],
        ExceptionType.SystemException or ExceptionType.ApplicationException or ExceptionType.Arithmetic or
            ExceptionType.DivideByZero or ExceptionType.Overflow or ExceptionType.NotSupported or
            ExceptionType.NotImplemented or ExceptionType.IndexOutOfRange or ExceptionType.NullReference or
            ExceptionType.Format => [[], [Message]],
        ExceptionType.Argument =>
            [[], [Message], [Message, Message], [Message, Inner], [Message, Message, Inner]],
        ExceptionType.ArgumentNull => [[], [Message], [Message, Message]],
        ExceptionType.ArgumentOutOfRange =>
            [[], [Message], [Message, Message], [Message, Inner], [Message, Actual, Message]],
        ExceptionType.InvalidCast or ExceptionType.ArrayTypeMismatch or ExceptionType.OutOfMemory => [],
        _ => throw new ArgumentOutOfRangeException(nameof(exception))
    };

    /// <summary>The member whose runtime type <paramref name="type"/> names, or null for any other type.</summary>
    internal static ExceptionType? Owner(TypeReference type)
    {
        if (type is TypeSpecification || type.IsNested || type.Namespace != "System" ||
            LayoutEvidence.Scope(type) != TypeTests.RuntimeScope) return null;
        foreach (ExceptionType exception in ExceptionTypeText.All)
            if (type.Name == exception.MetadataName()) return exception;
        return null;
    }

    static bool AdmittedConstructor(MethodReference constructor, ExceptionType exception)
    {
        var parameters = constructor.Parameters.Select(parameter => parameter.ParameterType).ToArray();
        if (parameters.Any(parameter => parameter is TypeSpecification ||
            LayoutEvidence.Scope(parameter) != TypeTests.RuntimeScope)) return false;
        var names = parameters.Select(parameter => parameter.FullName).ToArray();
        return AdmittedParameters(exception).Any(admitted => admitted.SequenceEqual(names, StringComparer.Ordinal));
    }

    static ExceptionType? Raised(Instruction instruction, IList<Instruction> code, int start, int count) =>
        instruction.OpCode.Code == Code.Newobj && instruction.Operand is MethodReference constructor &&
        constructor is not GenericInstanceMethod && constructor.Name == ".ctor" && constructor.HasThis &&
        !constructor.ExplicitThis && constructor.CallingConvention == MethodCallingConvention.Default && !constructor.HasGenericParameters &&
        constructor.ReturnType.MetadataType == MetadataType.Void && constructor.Parameters.Count == count &&
        constructor.Parameters.Select((parameter, index) =>
            parameter.ParameterType.MetadataType == MetadataType.String ||
            code[start + index].OpCode.Code == Code.Ldnull).All(valid => valid) &&
        constructor.DeclaringType is not TypeSpecification && !constructor.DeclaringType.IsValueType &&
        Owner(constructor.DeclaringType) is ExceptionType owner && AdmittedConstructor(constructor, owner)
            ? owner : null;

    static readonly System.Runtime.CompilerServices.ConditionalWeakTable<MethodDefinition, Analysis> cache = new();

    static readonly Analysis NoFolds = new([], [], [], []);

    /// <summary>The refusal of an instruction of a recognized throw that a clause protects.</summary>
    internal static InvalidDataException ProtectedRefusal(Instruction site) => new($"""
        Unsupported throw inside a protected range: {site}
          A recognized exception constructor is folded into a fault without an object, which no catch can test.
        """.ReplaceLineEndings("\n"));

    internal static Analysis Analyze(MethodDefinition method, Instruction? managedConstructor = null) =>
        managedConstructor is null ? cache.GetValue(method, Compute) : NoFolds;

    static Analysis Compute(MethodDefinition method)
    {
        var code = method.Body.Instructions;
        var analysis = new Analysis([], [], [], []);
        var clauses = ExceptionClauses.Of(method);
        for (int at = 0; at < code.Count; at++)
        {
            int count = 0;
            while (count < ArgumentLimit && at + count < code.Count &&
                code[at + count].OpCode.Code is Code.Ldstr or Code.Ldnull) count++;
            int raise = at + count + 1;
            if (count == ArgumentLimit || raise >= code.Count || code[raise].OpCode.Code != Code.Throw ||
                Raised(code[at + count], code, at, count) is not ExceptionType raised)
                continue;
            if (clauses.Any(clause => clause.TryStart <= raise && raise < clause.TryEnd))
            {
                for (int k = at; k <= raise; k++) analysis.Protected.Add(code[k]);
                at = raise;
                continue;
            }
            for (int k = at; k < raise; k++) analysis.Operands.Add(code[k]);
            for (int k = at + 1; k <= raise; k++) analysis.Interior.Add(code[k]);
            analysis.Raises.Add(code[raise], raised);
            at = raise;
        }
        return analysis;
    }
}
