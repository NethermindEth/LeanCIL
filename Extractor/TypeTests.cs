using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Folds closed typeof comparisons, including reference-equality branches. Lean
// rechecks each decided result and target using the same scoped type identities.
internal static class TypeTests
{
    internal sealed record Analysis(Dictionary<Instruction, bool> Results, HashSet<Instruction> Operands, HashSet<Instruction> Interior);

    // The scope text the extractor's string-keyed type identities compare, spelled from the platform identity.
    internal static readonly string RuntimeScope = PlatformAssemblies.SystemRuntime.ToDisplay();

    sealed record Node(string Kind, string Scope = "", string Name = "", Node? Left = null, Node? Right = null);

    // Same shape as GenericEvidence.Type; aggregate, enum and atom leaves share one identity.
    static Node Expr(TypeReference type) => type switch
    {
        GenericParameter parameter => parameter.Type == GenericParameterType.Method
            ? new("parameter", Name: parameter.Position.ToString(System.Globalization.CultureInfo.InvariantCulture))
            : new("named", "", "type-parameter:" + parameter.FullName),
        ByReferenceType byRef => new("byref", Left: Expr(byRef.ElementType)),
        PointerType pointer => new("pointer", Left: Expr(pointer.ElementType)),
        GenericInstanceType generic => generic.GenericArguments.Aggregate(
            new Node("named", LayoutEvidence.Scope(generic.ElementType), generic.ElementType.FullName),
            (result, argument) => new Node("apply", Left: result, Right: Expr(argument))),
        _ when type.FullName == "System.Void" => new("void"),
        _ => new("named", LayoutEvidence.Scope(type), type.FullName)
    };

    internal static bool PlainName(string name) =>
        name.Length > 0 && name.All(c => char.IsAsciiLetterOrDigit(c) || c is '_' or '.' or '/' or '`');

    static bool Plain(Node node) => node.Kind == "named" && node.Scope.Length > 0 && !node.Scope.Contains(':') && PlainName(node.Name);

    static bool Constructed(Node node) => node.Kind is "pointer" or "byref" or "apply";

    static bool? Same(Node a, Node b)
    {
        if (a.Kind == b.Kind && a.Kind is "pointer" or "byref") return Same(a.Left!, b.Left!);
        if (a.Kind == "apply" && b.Kind == "apply")
        {
            var (head, argument) = (Same(a.Left!, b.Left!), Same(a.Right!, b.Right!));
            return head == false || argument == false ? false : head == true && argument == true ? true : null;
        }
        if (a == b) return a.Kind == "void" ? null : true;
        if (Plain(a) && Plain(b)) return a.Name != b.Name ? false : a.Scope == b.Scope ? true : null;
        return (Constructed(a) || Plain(a)) && (Constructed(b) || Plain(b)) ? false : null;
    }

    static bool RuntimeType(TypeReference type, string name, bool valueType = false) =>
        type is not TypeSpecification && !type.IsNested && type.Namespace == "System" && type.Name == name &&
        type.IsValueType == valueType && RuntimeModels.ExactScope(type, PlatformAssemblies.SystemRuntime);

    static bool TypeMethod(Instruction instruction, string name)
    {
        if (instruction.OpCode.Code != Code.Call || instruction.Operand is not MethodReference method ||
            method is GenericInstanceMethod || method.HasGenericParameters || method.Name != name ||
            method.HasThis || method.ExplicitThis || method.CallingConvention != MethodCallingConvention.Default ||
            !RuntimeType(method.DeclaringType, "Type")) return false;

        if (name == "GetTypeFromHandle")
            return RuntimeType(method.ReturnType, "Type") && method.Parameters is [var handle] &&
                RuntimeType(handle.ParameterType, "RuntimeTypeHandle", valueType: true);
        return method.ReturnType.MetadataType == MetadataType.Boolean && method.Parameters is [var left, var right] &&
            RuntimeType(left.ParameterType, "Type") && RuntimeType(right.ParameterType, "Type");
    }

    static bool? Comparison(Instruction instruction) =>
        instruction.OpCode.Code == Code.Ceq && instruction.Operand is null ? true :
        instruction.Operand is Instruction && instruction.OpCode.Code is Code.Beq or Code.Beq_S ? true :
        instruction.Operand is Instruction && instruction.OpCode.Code is Code.Bne_Un or Code.Bne_Un_S ? false :
        TypeMethod(instruction, "op_Equality") ? true :
        TypeMethod(instruction, "op_Inequality") ? false : null;

    static bool? Test(IList<Instruction> code, int at)
    {
        if (at + 4 >= code.Count || code[at].OpCode.Code != Code.Ldtoken || code[at].Operand is not TypeReference left ||
            code[at + 2].OpCode.Code != Code.Ldtoken || code[at + 2].Operand is not TypeReference right ||
            !TypeMethod(code[at + 1], "GetTypeFromHandle") || !TypeMethod(code[at + 3], "GetTypeFromHandle") ||
            Comparison(code[at + 4]) is not bool equality)
            return null;
        return Same(Expr(left), Expr(right)) is bool same ? same == equality : null;
    }

    static readonly System.Runtime.CompilerServices.ConditionalWeakTable<MethodDefinition, Analysis> cache = new();

    internal static Analysis Analyze(MethodDefinition method) => cache.GetValue(method, Compute);

    static Analysis Compute(MethodDefinition method)
    {
        var code = method.Body.Instructions;
        var analysis = new Analysis([], [], []);
        for (int at = 0; at < code.Count; at++)
        {
            if (Test(code, at) is not bool value) continue;
            for (int k = 0; k < 4; k++) analysis.Operands.Add(code[at + k]);
            for (int k = 1; k < 5; k++) analysis.Interior.Add(code[at + k]);
            analysis.Results.Add(code[at + 4], value);
            at += 4;
        }
        return analysis;
    }
}
