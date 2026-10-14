using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class LeanEmitter
{
    internal static string Kind(TypeReference type, ModuleDefinition module)
    {
        if (type is ByReferenceType) return ".reference";
        if (MetadataValidation.IsAggregate(type, module)) return $".aggregate {MetadataValidation.Layout(type, module)}";
        return type.FullName switch
        {
            "System.Byte" or "System.Boolean" => ".byte",
            "System.Int32" or "System.UInt32" => ".word32",
            "System.Int64" or "System.UInt64" => ".word64",
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector128`1<", StringComparison.Ordinal) => ".vector128",
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector256`1<", StringComparison.Ordinal) => ".vector256",
            _ => throw new InvalidDataException($"Unsupported local: {type.FullName}")
        };
    }
    internal static string Initial(TypeReference type, ModuleDefinition module) => Kind(type, module) switch
    {
        ".reference" => ".nullRef", ".byte" or ".word32" => ".i32 0", ".word64" => ".i64 0",
        ".vector128" => ".v128 0", ".vector256" => ".v256 0",
        _ => $".aggregate (List.replicate {MetadataValidation.Layout(type, module)} 0)"
    };
    internal static string Emit(MethodDefinition[] methods, FeatureProfile profile, string assemblyHash)
    {
        StringBuilder lean = new("import CIL.Layout\nimport CIL.SymbolicExecution\nimport CIL.Safety.Execution\n\nnamespace Extracted\nopen CIL\n\n");
        lean.AppendLine($"def assemblySha256 : String := {JsonSerializer.Serialize(assemblyHash)}");
        lean.AppendLine($"@[cil_code] def profile : FeatureProfile := {profile.Lean}");
        lean.AppendLine("theorem profile_valid : profile.Valid := by decide");
        FieldDefinition[] data = methods.SelectMany(m => Reachability.Analyze(m, profile))
            .Where(i => i.OpCode.Code == Code.Ldsflda)
            .Select(i => StaticData.Validate((FieldReference)i.Operand, methods[0].Module)).Distinct().ToArray();
        TypeReference[] types = methods.SelectMany(m => m.Parameters.Select(p => p.ParameterType)
            .Concat(m.Body.Variables.Select(v => v.VariableType)).Append(m.ReturnType)
            .Concat(m.Body.Instructions.Where(i => i.Operand is FieldReference).Select(i => ((FieldReference)i.Operand).DeclaringType)))
            .Select(t => t is ByReferenceType r ? r.ElementType : t)
            .Where(t => MetadataValidation.IsAggregate(t, methods[0].Module)).DistinctBy(t => t.FullName).ToArray();
        for (int i = 0; i < types.Length; i++)
        {
            int size = MetadataValidation.Layout(types[i], methods[0].Module);
            string fields = string.Join(", ", types[i].Resolve().Fields.Where(f => !f.IsStatic)
                .Select(f => $"⟨{f.Offset}, {MetadataValidation.PrimitiveWidth(f.FieldType)}⟩"));
            lean.AppendLine($"def layout{i} : AggregateLayout := ⟨{size}, [{fields}]⟩");
            lean.AppendLine($"theorem layout{i}_valid : layout{i}.Valid := by decide");
        }
        for (int n = 0; n < methods.Length; n++)
        {
            MethodDefinition m = methods[n];
            HashSet<Instruction> reachable = Reachability.Analyze(m, profile);
            string locals = string.Join(", ", m.Body.Variables.Select(v => m.Body.InitLocals ? Initial(v.VariableType, m.Module) : ".unmodeled"));
            string kinds = string.Join(", ", m.Body.Variables.Select(v => Kind(v.VariableType, m.Module)));
            string sites = string.Join(", ", m.Body.Instructions.Select((i, pc) => (i, pc))
                .Where(s => reachable.Contains(s.i) && s.i.OpCode.Code == Code.Ldsflda).Select(s =>
                {
                    FieldDefinition f = StaticData.Validate((FieldReference)s.i.Operand, m.Module);
                    return $"({s.pc}, {{ identity := {Array.IndexOf(data, f)}, fieldName := {JsonSerializer.Serialize(f.FullName)}, bytes := {StaticData.LeanBytes(f)} }})";
                }));
            lean.AppendLine($"def method{n}Signature : String := {JsonSerializer.Serialize(m.FullName)}");
            lean.AppendLine($"def method{n} : Method := {{ profile := profile, returnsValue := {(m.ReturnType.FullName == "System.Void" ? "false" : "true")}, locals := [{locals}], localKinds := [{kinds}], staticSites := [{sites}], code := [");
            List<string> ops = [];
            foreach (Instruction i in m.Body.Instructions)
                ops.Add(reachable.Contains(i) ? InstructionTranslation.Translate(i, m, methods, n, profile) : ".unsupported \"Unreachable under selected profile\"");
            lean.AppendLine(string.Join(",\n", ops.Select(op => "  " + op)) + "] }");
            for (int pc = 0; pc < ops.Count; pc++)
                lean.AppendLine($"@[cil_code ↓] theorem method{n}_instruction{pc} : method{n}.code[{pc}]? = some ({ops[pc]} : Op) := rfl");
            foreach (string field in new[] { "profile", "locals", "localKinds", "returnsValue", "staticSites", "vectorLocals", "vectorArgs" })
                lean.AppendLine($"@[cil_code] theorem method{n}_{field} : method{n}.{field} = ({(field == "profile" ? "profile" : field == "locals" ? $"[{locals}]" : field == "localKinds" ? $"[{kinds}]" : field == "returnsValue" ? (m.ReturnType.FullName == "System.Void" ? "false" : "true") : field == "staticSites" ? $"[{sites}]" : "[]")}) := rfl");
        }
        lean.AppendLine("def program : Program := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"method{n}")) + "]");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"@[cil_code] theorem lookup{n} : program[{n}]? = some method{n} := rfl");
        lean.AppendLine("end Extracted");
        return lean.ToString();
    }
}
