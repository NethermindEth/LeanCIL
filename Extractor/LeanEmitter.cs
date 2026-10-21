using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class LeanEmitter
{
    internal static string? Narrow(TypeReference type) => EnumTypes.Storage(type).FullName switch
    {
        "System.SByte" => "signed8",
        "System.Byte" or "System.Boolean" => "unsigned8",
        "System.Int16" => "signed16",
        "System.UInt16" or "System.Char" => "unsigned16",
        _ => null
    };

    internal static string Kind(TypeReference type, ModuleDefinition module)
    {
        // A span local is only touched by a receiver fold, so its slot is an inert root.
        if (type is ByReferenceType || Spans.Width(type) is not null) return ".reference";
        if (MetadataValidation.IsAggregate(type, module)) return $".aggregate {MetadataValidation.Layout(type, module)}";
        if (Narrow(type) is { } narrow) return $".narrow .{narrow}";
        return EnumTypes.Storage(type).FullName switch
        {
            "System.Int32" or "System.UInt32" => ".word32",
            "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" => ".word64",
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector128`1<", StringComparison.Ordinal) => ".vector128",
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector256`1<", StringComparison.Ordinal) => ".vector256",
            _ => throw new InvalidDataException($"Unsupported local: {type.FullName}")
        };
    }
    static bool StaticSite(Instruction i) => i.OpCode.Code == Code.Ldsflda || (i.OpCode.Code == Code.Ldtoken && i.Operand is FieldReference);
    internal static string Initial(TypeReference type, ModuleDefinition module) => Kind(type, module) switch
    {
        ".reference" => ".nullRef", ".word32" => ".i32 0", ".word64" => ".i64 0",
        string kind when kind.StartsWith(".narrow ", StringComparison.Ordinal) => ".i32 0",
        ".vector128" => ".v128 0", ".vector256" => ".v256 0",
        _ => $".aggregate (List.replicate {MetadataValidation.Layout(type, module)} 0)"
    };
    internal static string Emit(MethodDefinition[] methods, FeatureProfile profile, ModuleDefinition originalModule)
    {
        StringBuilder lean = new("import CIL.Extraction.Translation\nimport CIL.SymbolicExecution\nimport CIL.Safety.Execution\n\nnamespace Extracted\nopen CIL\n\nset_option maxRecDepth 4096\n\n");
        lean.AppendLine($"@[cil_code] def profile : FeatureProfile := {profile.Lean}");
        lean.AppendLine("theorem profile_valid : profile.Valid := by decide");
        FieldDefinition[] data = methods.SelectMany(m => Reachability.Analyze(m, profile))
            .Where(StaticSite)
            .Select(i => StaticData.Validate((FieldReference)i.Operand, methods[0].Module)).Distinct().ToArray();
        TypeReference[] types = methods.SelectMany(m => m.Parameters.Select(p => p.ParameterType)
            .Concat(m.HasThis ? [m.DeclaringType] : [])
            .Concat(m.Body.Variables.Select(v => v.VariableType)).Append(m.ReturnType)
            .Concat(MethodSpecialization.Arguments(m))
            .Concat(m.Body.Instructions.Where(i => i.Operand is TypeReference).Select(i => (TypeReference)i.Operand))
            .Concat(m.Body.Instructions.Where(i => i.Operand is GenericInstanceMethod).SelectMany(i => ((GenericInstanceMethod)i.Operand).GenericArguments))
            .Concat(m.Body.Instructions.Where(i => i.Operand is FieldReference).Select(i => ((FieldReference)i.Operand).DeclaringType)))
            .Select(t => t is ByReferenceType r ? r.ElementType : t)
            .Where(t => MetadataValidation.IsAggregate(t, methods[0].Module)).DistinctBy(t => t.FullName).ToArray();
        var layouts = new List<TypeReference>();
        var seenLayouts = new HashSet<string>();
        void IncludeLayout(TypeReference type)
        {
            if (!seenLayouts.Add(type.FullName)) return;
            layouts.Add(type);
            foreach (var field in type.Resolve().Fields.Where(f => !f.IsStatic))
                if (MetadataValidation.IsAggregate(field.FieldType, methods[0].Module)) IncludeLayout(field.FieldType);
        }
        foreach (var type in types) IncludeLayout(type);
        types = layouts.ToArray();
        for (int i = 0; i < types.Length; i++)
        {
            int size = MetadataValidation.Layout(types[i], methods[0].Module);
            string fields = string.Join(", ", types[i].Resolve().Fields.Where(f => !f.IsStatic)
                .Select(f => $"⟨{MetadataValidation.FieldOffset(f, methods[0].Module)}, {MetadataValidation.FieldSize(f.FieldType, methods[0].Module)}, {MetadataValidation.IsAggregate(f.FieldType, methods[0].Module).ToString().ToLowerInvariant()}⟩"));
            lean.AppendLine($"def layout{i} : AggregateLayout := ⟨{size}, [{fields}]⟩");
            lean.AppendLine($"theorem layout{i}_valid : layout{i}.Valid := by decide");
        }
        var layoutEvidence = new LayoutEvidence(types);
        layoutEvidence.EmitLayouts(lean);
        var genericEvidence = new GenericEvidence(originalModule, layoutEvidence);
        for (int n = 0; n < methods.Length; n++)
        {
            MethodDefinition m = methods[n];
            HashSet<Instruction> reachable = Reachability.Analyze(m, profile);
            var nativeOperands = NativeOperands.Analyze(m, profile);
            var parameterIndices = ParameterStorage.Analyze(m, profile);
            var parameters = string.Join(", ", parameterIndices.Select(index => $"({index}, {Kind(MethodArguments.Type(m, index), m.Module)})"));
            string locals = string.Join(", ", m.Body.Variables.Select(v => m.Body.InitLocals ? Initial(v.VariableType, m.Module) : ".unmodeled"));
            string kinds = string.Join(", ", m.Body.Variables.Select(v => Kind(v.VariableType, m.Module)));
            string sites = string.Join(", ", m.Body.Instructions.Select((i, pc) => (i, pc))
                .Where(s => reachable.Contains(s.i) && StaticSite(s.i)).Select(s =>
                {
                    FieldDefinition f = StaticData.Validate((FieldReference)s.i.Operand, m.Module);
                    return $"({s.pc}, {{ identity := {Array.IndexOf(data, f)}, fieldName := {JsonSerializer.Serialize(f.FullName)}, bytes := {StaticData.LeanBytes(f)} }})";
                }));
            lean.AppendLine($"def method{n}Signature : String := {JsonSerializer.Serialize(m.FullName)}");
            if (MethodSpecialization.Source(m) is { } origin)
            {
                lean.AppendLine($"def method{n}GenericDefinition : String := {JsonSerializer.Serialize(origin.Definition)}");
                lean.AppendLine($"def method{n}TypeArguments : List String := [{string.Join(", ", origin.TypeArguments.Select(t => JsonSerializer.Serialize(t)))}]");
            }
            lean.AppendLine($"def method{n} : Method := {{ profile := profile, returnsValue := {(m.ReturnType.FullName == "System.Void" ? "false" : "true")}, locals := [{locals}], localKinds := [{kinds}], parameterHomes := [{parameters}], staticSites := [{sites}], code := [");
            List<string> ops = [];
            foreach (Instruction i in m.Body.Instructions)
                ops.Add(reachable.Contains(i) ? InstructionTranslation.Translate(i, m, methods, n, profile, nativeOperands, parameterIndices) : ".unsupported \"Unreachable under selected profile\"");
            lean.AppendLine(string.Join(",\n", ops.Select(op => "  " + op)) + "] }");
            layoutEvidence.EmitMethod(lean, m, n, reachable, parameterIndices);
            ParameterEvidence.Emit(lean, m, n, reachable, layoutEvidence);
            genericEvidence.EmitMethod(lean, m, n);
            FeatureEvidence.Emit(lean, m, n, profile);
            lean.AppendLine($"@[cil_code] theorem method{n}_parameterHomes : method{n}.parameterHomes = [{parameters}] := rfl");
            for (int pc = 0; pc < ops.Count; pc++)
                lean.AppendLine($"@[cil_code ↓] theorem method{n}_instruction{pc} : method{n}.code[{pc}]? = some ({ops[pc]} : Op) := rfl");
            foreach (string field in new[] { "profile", "locals", "localKinds", "returnsValue", "staticSites", "vectorLocals", "vectorArgs" })
                lean.AppendLine($"@[cil_code] theorem method{n}_{field} : method{n}.{field} = ({(field == "profile" ? "profile" : field == "locals" ? $"[{locals}]" : field == "localKinds" ? $"[{kinds}]" : field == "returnsValue" ? (m.ReturnType.FullName == "System.Void" ? "false" : "true") : field == "staticSites" ? $"[{sites}]" : "[]")}) := rfl");
        }
        lean.AppendLine("def specializedMethods : List Extraction.SpecializedMethod := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"⟨method{n}TypeArgumentsRaw, method{n}Closed⟩")) + "]");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"theorem method{n}_calls_validated : Extraction.ManagedCallsValid specializedMethods method{n}Closed method{n}Reachable method{n} := by decide");
        lean.AppendLine("def program : Program := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"method{n}")) + "]");
        lean.AppendLine("def methodEvidence : List Extraction.MethodEvidence := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"{{ original := method{n}Original, arguments := method{n}TypeArgumentsRaw, closed := method{n}Closed, parameterInput := method{n}RawArguments, reachable := method{n}Reachable, featureStates := method{n}FeatureStates, layoutUses := method{n}LayoutUses }}")) + "]");
        for (int n = 0; n < methods.Length; n++)
        {
            lean.AppendLine($"theorem method{n}_coverage_validated : Extraction.LayoutUsesComplete rawLayouts method{n}Closed method{n}RawArguments method{n}Reachable method{n}LayoutUses := by decide");
            lean.AppendLine($"theorem method{n}_shape_validated : Extraction.MethodShapeValid rawLayouts method{n}Closed method{n} := by decide");
            lean.AppendLine($"theorem method{n}_skipInit_validated : Extraction.SkipInitValid rawLayouts method{n}Closed method{n}Reachable method{n}.code := by decide");
            lean.AppendLine($"theorem method{n}_evidence_validated : Extraction.MethodEvidenceValid rawLayouts computedLayouts methodEvidence methodEvidence[{n}] method{n} :=");
            lean.AppendLine($"  ⟨method{n}_specialization_validated, method{n}_parameters_validated, method{n}_layouts_validated, method{n}_features_validated, method{n}_calls_validated, method{n}_coverage_validated, method{n}_shape_validated, method{n}_skipInit_validated⟩");
        }
        lean.AppendLine("theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts methodEvidence program := by");
        lean.AppendLine("  apply Extraction.translation_of_methods layouts_validated");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"  refine Extraction.MethodsChecked.cons method{n}_evidence_validated ?_");
        lean.AppendLine("  exact Extraction.MethodsChecked.nil");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"@[cil_code] theorem lookup{n} : program[{n}]? = some method{n} := rfl");
        lean.AppendLine("end Extracted");
        return lean.ToString();
    }
}
