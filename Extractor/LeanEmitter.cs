using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class LeanEmitter
{
    internal readonly record struct Emission(string Source, string[] LayoutIdentities,
        TemplateEmitter.Method[] Templates);

    internal static string? Narrow(TypeReference type) => EnumTypes.Storage(type).FullName switch
    {
        "System.SByte" => "signed8",
        "System.Byte" or "System.Boolean" => "unsigned8",
        "System.Int16" => "signed16",
        "System.UInt16" or "System.Char" => "unsigned16",
        _ => null
    };

    // The kernel rechecks every decide; elaborator whnf costs grow superlinearly with body size.
    internal const string Decide = "by decide +kernel";
    internal static string Kind(TypeReference type, ModuleDefinition module, string architecture = "scalar",
        MetadataValidation.LayoutContext? layouts = null)
    {
        layouts?.Require(module, architecture);
        if (ManagedPointers.Signature(type) is { } pointer)
            return $".{(type is ArrayType ? "methodTable" : "methodPointer")} " +
                ManagedPointers.SignatureEvidence(pointer);
        if (type is ByReferenceType or PointerType) return ".reference";
        if (Arrays.Of(type, architecture) is { } element) return $".array {element.Expression}";
        if (Spans.Width(type, architecture) is { } width)
            return $".span {width} {(Spans.Writable(type) ? "true" : "false")}";
        if (MetadataValidation.IsAggregate(type, module))
        {
            var size = layouts?.Size(type) ?? MetadataValidation.Layout(type, module, architecture);
            return $".aggregate {size}";
        }
        if (Narrow(type) is { } narrow) return $".narrow .{narrow}";
        return EnumTypes.Storage(type).FullName switch
        {
            "System.Int32" or "System.UInt32" => ".word32",
            "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" => ".word64",
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector128`1<", StringComparison.Ordinal) => ".vector128",
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector256`1<", StringComparison.Ordinal) => ".vector256",
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector512`1<", StringComparison.Ordinal) => ".vector512",
            _ => throw new InvalidDataException($"Unsupported local: {type.FullName}")
        };
    }
    static bool StaticSite(Instruction i) => i.OpCode.Code == Code.Ldsflda || StaticValues.IsLoad(i) ||
        (i.OpCode.Code == Code.Ldtoken && i.Operand is FieldReference);
    static FieldDefinition StaticField(Instruction i, ModuleDefinition module, string architecture) => StaticValues.IsLoad(i)
        ? StaticValues.Resolve((FieldReference)i.Operand, module, architecture).Field : StaticData.Validate((FieldReference)i.Operand, module);
    internal static StaticIdentityRecord[] StaticIdentities(MethodDefinition[] methods, FeatureProfile profile) =>
        methods.SelectMany(method => Reachability.Analyze(method, profile)).Where(StaticSite)
            .Select(instruction => StaticIdentity.Of(StaticField(instruction, methods[0].Module, profile.Architecture)))
            .Distinct().OrderBy(identity => identity.Identity, StringComparer.Ordinal).ToArray();
    internal static string Initial(TypeReference type, ModuleDefinition module, string architecture = "scalar",
        MetadataValidation.LayoutContext? layouts = null) => Kind(type, module, architecture, layouts) switch
    {
        ".reference" => ".nullRef", ".word32" => ".i32 0", ".word64" => ".i64 0",
        string kind when kind.StartsWith(".narrow ", StringComparison.Ordinal) => ".i32 0",
        string kind when kind.StartsWith(".span ", StringComparison.Ordinal) ||
            kind.StartsWith(".array ", StringComparison.Ordinal) ||
            kind.StartsWith(".methodPointer ", StringComparison.Ordinal) ||
            kind.StartsWith(".methodTable ", StringComparison.Ordinal) => ".nullRef",
        ".vector128" => ".v128 0", ".vector256" => ".v256 0", ".vector512" => ".v512 0",
        _ => ".aggregate (List.replicate " +
            (layouts?.Size(type) ?? MetadataValidation.Layout(type, module, architecture)) + " 0)"
    };
    static TypeReference[] LayoutTypes(MethodDefinition[] methods, MetadataValidation.LayoutContext metadata)
    {
        TypeReference[] types = methods
            .SelectMany(m => m.Parameters.Select(p => InReferences.Parameter(p.ParameterType))
            .Concat(m.HasThis ? [MethodSpecialization.DeclaringType(m)] : [])
            .Concat(m.Body.Variables.Select(v => v.VariableType)).Append(m.ReturnType)
            .Concat(MethodSpecialization.Arguments(m))
            .Concat(m.Body.Instructions.Where(i => i.Operand is TypeReference).Select(i => (TypeReference)i.Operand))
            .Concat(m.Body.Instructions.Where(i => i.Operand is GenericInstanceMethod).SelectMany(i => ((GenericInstanceMethod)i.Operand).GenericArguments))
            .Concat(m.Body.Instructions.Where(i => i.Operand is FieldReference).Select(i => ((FieldReference)i.Operand).DeclaringType)))
            .Select(t => t is ByReferenceType r ? r.ElementType : t)
            .Select(t => t is ArrayType array ? array.ElementType : t)
            .Select(t => Spans.Is(t) ? ((GenericInstanceType)t).GenericArguments[0] : t)
            .Where(t => MetadataValidation.IsAggregate(t, methods[0].Module)).DistinctBy(LayoutEvidence.Identity).ToArray();
        List<TypeReference> layouts = [];
        HashSet<string> seenLayouts = new(StringComparer.Ordinal);
        void IncludeLayout(TypeReference type)
        {
            if (!seenLayouts.Add(LayoutEvidence.Identity(type))) return;
            layouts.Add(type);
            foreach (MetadataValidation.InstanceField field in metadata.Fields(type))
                if (MetadataValidation.IsAggregate(field.Type, methods[0].Module)) IncludeLayout(field.Type);
        }
        foreach (TypeReference type in types) IncludeLayout(type);
        return layouts.ToArray();
    }

    // These definitions guide proof simplification; the full validator still checks every call.
    static string? CallDefinitions(int caller, IReadOnlyList<string> operations, int methodCount)
    {
        var targets = new SortedSet<int> { caller };
        var hasCall = false;
        foreach (var operation in operations)
        {
            if (!operation.StartsWith(".call ", StringComparison.Ordinal) &&
                !operation.StartsWith(".newAggregate ", StringComparison.Ordinal) &&
                !operation.StartsWith(".newVector256 ", StringComparison.Ordinal)) continue;
            hasCall = true;
            var fields = operation.Split(' ', 3);
            if (fields.Length >= 2 && int.TryParse(fields[1], out var target) &&
                target >= 0 && target < methodCount) targets.Add(target);
        }
        if (!hasCall) return null;
        return string.Join(", ", targets.SelectMany(target =>
            new[] { $"method{target}Closed", $"method{target}TypeArgumentsRaw" }));
    }

    internal static Emission Emit(MethodDefinition[] methods, FeatureProfile profile, ModuleDefinition originalModule, ImportResolution? importResolution = null,
        StaticIdentityRecord[]? staticIdentities = null, bool collectTemplates = false)
    {
        var methodIndices = methods.Select((method, index) => (method, index))
            .ToDictionary(pair => pair.method, pair => pair.index);
        var constrainedTargets = new ConstrainedCalls.TargetIndex(methods);
        var templates = new List<TemplateEmitter.Method>();
        var callDefinitions = new string?[methods.Length];
        StringBuilder lean = new("import CIL.Extraction.Translation\nimport CIL.SymbolicExecution\nimport CIL.Safety.Execution\n\nnamespace Extracted\nopen CIL\n\nset_option maxRecDepth 4096\n\n");
        lean.AppendLine($"@[cil_code] def profile : FeatureProfile := {profile.Lean}");
        lean.AppendLine("theorem profile_valid : profile.Valid := " + Decide);
        StaticIdentity.Validate(staticIdentities ?? StaticIdentities(methods, profile));
        var layoutContext = new MetadataValidation.LayoutContext(methods[0].Module, profile.Architecture);
        TypeReference[] types = LayoutTypes(methods, layoutContext);
        for (int i = 0; i < types.Length; i++)
        {
            int size = layoutContext.Size(types[i]);
            string fields = string.Join(", ", layoutContext.Fields(types[i])
                .Select(field =>
                {
                    var offset = layoutContext.FieldOffset(types[i], field.Definition);
                    var width = layoutContext.FieldSize(field.Type);
                    var aggregate = MetadataValidation.IsAggregate(field.Type, methods[0].Module);
                    return $"⟨{offset}, {width}, {aggregate.ToString().ToLowerInvariant()}⟩";
                }));
            lean.AppendLine($"def layout{i} : AggregateLayout := ⟨{size}, [{fields}]⟩");
            lean.AppendLine($"theorem layout{i}_valid : layout{i}.Valid := {Decide}");
        }
        LayoutEvidence layoutEvidence = new(types, layoutContext);
        layoutEvidence.EmitLayouts(lean);
        GenericEvidence genericEvidence = new(originalModule, layoutEvidence, importResolution);
        for (int n = 0; n < methods.Length; n++)
        {
            MethodDefinition m = methods[n];
            var instructions = new InstructionIndex(m);
            var featureCertificate = Reachability.Certify(m, profile);
            var reachable = featureCertificate.Keys.ToHashSet();
            var scalarCertificate = NativeOperands.Certify(m, reachable, profile);
            var parameterIndices = ParameterStorage.Analyze(m, reachable);
            var parameterHomes = ParameterStorage.IndexHomes(parameterIndices);
            var dispatch = NativeDispatch.For(m);
            string LocalKind(TypeReference type, int? local = null) => dispatch.Kind(type, local) ??
                Kind(type, m.Module, profile.Architecture, layoutContext);
            string parameters = string.Join(", ", parameterIndices.Select(index =>
                $"({index}, {LocalKind(MethodArguments.Type(m, index))})"));
            string locals = string.Join(", ", m.Body.Variables.Select(variable => m.Body.InitLocals
                ? dispatch.Kind(variable.VariableType, variable.Index) is not null ? ".nullRef" :
                    Initial(variable.VariableType, m.Module, profile.Architecture, layoutContext) : ".unmodeled"));
            HashSet<int> addressedLocals = m.Body.Instructions
                .Where(instruction => instruction.OpCode.Code is Code.Ldloca or Code.Ldloca_S)
                .Select(instruction => ((VariableDefinition)instruction.Operand).Index).ToHashSet();
            List<string> ops = [];
            foreach (Instruction i in m.Body.Instructions)
                ops.Add(reachable.Contains(i)
                    ? InstructionTranslation.Translate(i, m, methodIndices, n, instructions, profile,
                        scalarCertificate, parameterHomes, importResolution, layoutContext, constrainedTargets)
                    : ".unsupported \"Unreachable under selected profile\"");
            var needsOpaqueLocals = ops.Any(op => op.StartsWith(".intrinsic (.vector .createScalarUnsafe64) ", StringComparison.Ordinal));
            string opaqueLocals = needsOpaqueLocals ? string.Join(", ", m.Body.Variables
                .Where(variable => variable.VariableType.FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" &&
                    !addressedLocals.Contains(variable.Index)).Select(variable => variable.Index)) : "";
            string kinds = string.Join(", ", m.Body.Variables.Select(variable => LocalKind(variable.VariableType, variable.Index)));
            string sites = string.Join(", ", m.Body.Instructions.Select((i, pc) => (i, pc))
                .Where(s => reachable.Contains(s.i) && StaticSite(s.i)).Select(s =>
                {
                    if (StaticValues.IsLoad(s.i))
                    {
                        StaticValues.Value value = StaticValues.Resolve((FieldReference)s.i.Operand, m.Module, profile.Architecture);
                        var initializer = value.Initializer is null ? 0 : methodIndices.GetValueOrDefault(value.Initializer, -1);
                        if (initializer < 0)
                            throw new InvalidDataException($"Missing static initializer: {value.Initializer!.FullName}");
                        var literal = value.Literal is null ? "" : $", literal := some ({value.Literal})";
                        var construct = value.Construct ? ", construct := true" : "";
                        StaticIdentityRecord identity = StaticIdentity.Of(value.Field);
                        return $$"""
                            ({{s.pc}}, { identity := {{identity.Identity}},
                              assemblyIdentity := {{JsonSerializer.Serialize(identity.AssemblyIdentity)}},
                              fieldName := {{JsonSerializer.Serialize(value.Field.FullName)}},
                              bytes := {{StaticData.LeanBytes(value.Bytes)}}, scalar := {{StaticValues.Scalar(value.Field)}},
                              initializer := some { method := {{initializer}},
                                arguments := [{{string.Join(", ", value.Arguments)}}]{{literal}}{{construct}} } })
                            """;
                    }
                    FieldDefinition f = StaticData.Validate((FieldReference)s.i.Operand, m.Module);
                    StaticIdentityRecord fieldIdentity = StaticIdentity.Of(f);
                    return $$"""
                        ({{s.pc}}, { identity := {{fieldIdentity.Identity}},
                          assemblyIdentity := {{JsonSerializer.Serialize(fieldIdentity.AssemblyIdentity)}},
                          fieldName := {{JsonSerializer.Serialize(f.FullName)}},
                          bytes := {{StaticData.LeanBytes(f)}}, alignment := {{StaticData.Alignment(f)}} })
                        """;
                }));
            lean.AppendLine($"def method{n}Signature : String := {JsonSerializer.Serialize(m.FullName)}");
            if (MethodSpecialization.Source(m) is { } origin)
            {
                lean.AppendLine($"def method{n}GenericDefinition : String := {JsonSerializer.Serialize(origin.Definition)}");
                lean.AppendLine($"def method{n}TypeArguments : List String := [{string.Join(", ", origin.TypeArguments.Select(t => JsonSerializer.Serialize(t)))}]");
            }
            var metadata = $"returnsValue := {(m.ReturnType.FullName == "System.Void" ? "false" : "true")}, " +
                $"locals := [{locals}], localKinds := [{kinds}], opaqueVectorLocals := [{opaqueLocals}], " +
                $"parameterHomes := [{parameters}], staticSites := [{sites}]";
            callDefinitions[n] = CallDefinitions(n, ops, methods.Length);
            if (collectTemplates)
                templates.Add(new(m.FullName, metadata, ops.ToArray(), sites.Length != 0));
            lean.AppendLine($"def method{n} : Method := {{ profile := profile, {metadata}, code := [");
            lean.AppendLine(string.Join(",\n", ops.Select(op => "  " + op)) + "] }");
            layoutEvidence.EmitMethod(lean, m, n, reachable, parameterIndices);
            ParameterEvidence.Emit(lean, m, n, reachable, layoutEvidence);
            genericEvidence.EmitMethod(lean, m, n, reachable);
            FeatureEvidence.Emit(lean, m, n, featureCertificate);
            lean.AppendLine($"@[cil_code] theorem method{n}_opaqueVectorLocals : method{n}.opaqueVectorLocals = [{opaqueLocals}] := rfl");
            ScalarEvidence.Emit(lean, m, n, scalarCertificate);
            lean.AppendLine($"@[cil_code] theorem method{n}_parameterHomes : method{n}.parameterHomes = [{parameters}] := rfl");
            for (int pc = 0; pc < ops.Count; pc++)
                lean.AppendLine($"@[cil_code ↓] theorem method{n}_instruction{pc} : method{n}.code[{pc}]? = some ({ops[pc]} : Op) := rfl");
            foreach (string field in new[] { "profile", "locals", "localKinds", "returnsValue", "staticSites", "vectorLocals", "vectorArgs" })
                lean.AppendLine($"@[cil_code] theorem method{n}_{field} : method{n}.{field} = ({(field == "profile" ? "profile" : field == "locals" ? $"[{locals}]" : field == "localKinds" ? $"[{kinds}]" : field == "returnsValue" ? (m.ReturnType.FullName == "System.Void" ? "false" : "true") : field == "staticSites" ? $"[{sites}]" : "[]")}) := rfl");
        }
        lean.AppendLine("def specializedMethods : List Extraction.SpecializedMethod := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"⟨method{n}TypeArgumentsRaw, method{n}Closed⟩")) + "]");
        IReadOnlyList<ImportResolution.Binding> importBindings = importResolution?.Bindings ?? [];
        lean.AppendLine("def imports : List ImportSlot := [" + string.Join(", ", importBindings.Select(ImportResolution.LeanSlot)) + "]");
        for (var n = 0; n < methods.Length; n++)
        {
            var facts = $"specializedMethods, imports, Extraction.lowerConstrainedRaw, {callDefinitions[n]}, " +
                $"method{n}, method{n}Reachable, method{n}DispatchTypes";
            var proof = callDefinitions[n] is null ? Decide : $"by cil_managed_calls [{facts}]";
            lean.AppendLine($"theorem method{n}_calls_validated : Extraction.ManagedCallsValid " +
                $"specializedMethods imports (Extraction.lowerConstrainedRaw method{n}DispatchTypes " +
                $"method{n}Closed) method{n}Reachable method{n} := {proof}");
        }
        lean.AppendLine("def program : Program := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"method{n}")) + "]");
        // Proofs resolve methods by signature (CIL.MethodIdentity), so inserted helpers do not renumber them.
        lean.AppendLine("def signatures : List String := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"method{n}Signature")) + "]");
        lean.AppendLine("theorem signatures_length : signatures.length = program.length := rfl");
        lean.AppendLine("def importSignatures : List String := [" + string.Join(", ", importBindings.Select(binding => JsonSerializer.Serialize(binding.Identity))) + "]");
        lean.AppendLine("theorem importSignatures_length : importSignatures.length = imports.length := rfl");
        lean.AppendLine("theorem statics_validated : Extraction.StaticValuesValid program := " + Decide);
        lean.AppendLine("def methodEvidence : List Extraction.MethodEvidence := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"{{ original := method{n}Original, arguments := method{n}TypeArgumentsRaw, closed := method{n}Closed, parameterInput := method{n}RawArguments, reachable := method{n}Reachable, featureStates := method{n}FeatureStates, scalarStates := method{n}ScalarStates, layoutUses := method{n}LayoutUses, dispatchTypes := method{n}DispatchTypes }}")) + "]");
        for (int n = 0; n < methods.Length; n++)
        {
            lean.AppendLine($"theorem method{n}_coverage_validated : Extraction.LayoutUsesComplete rawLayouts method{n}Closed method{n}RawArguments method{n}Reachable method{n}LayoutUses := {Decide}");
            lean.AppendLine($"theorem method{n}_constrained_validated : Extraction.ConstrainedCallsValid method{n}DispatchTypes specializedMethods method{n}Closed method{n}Reachable method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_shape_validated : Extraction.MethodShapeValid rawLayouts method{n}Closed method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_unsafe_validated : Extraction.UnsafeCallsValid rawLayouts method{n}Closed method{n}Reachable method{n}.code := {Decide}");
            lean.AppendLine($"theorem method{n}_division_validated : Extraction.DivisionIntrinsicsValid method{n}Closed method{n}Reachable method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_opaque_validated : Extraction.OpaqueLocalsValid method{n}Closed method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_vector_initializations_validated : Extraction.VectorInitializationsValid method{n}Closed method{n}Reachable method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_evidence_validated : Extraction.MethodEvidenceValid rawLayouts computedLayouts methodEvidence imports methodEvidence[{n}] method{n} :=");
            lean.AppendLine($"  ⟨method{n}_specialization_validated, method{n}_parameters_validated, method{n}_layouts_validated, method{n}_features_validated, method{n}_calls_validated, method{n}_coverage_validated, method{n}_shape_validated, method{n}_unsafe_validated, method{n}_division_validated, method{n}_opaque_validated, method{n}_vector_initializations_validated, method{n}_scalars_validated, method{n}_constrained_validated⟩");
        }
        lean.AppendLine("theorem import_layouts_validated : Extraction.ImportedLayoutsValid imports profile.architecture := " + Decide);
        lean.AppendLine("#print axioms import_layouts_validated");
        lean.AppendLine("theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts methodEvidence imports program := by");
        lean.AppendLine("  apply Extraction.translation_of_methods (program := program) layouts_validated statics_validated import_layouts_validated");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"  refine Extraction.MethodsChecked.cons method{n}_evidence_validated ?_");
        lean.AppendLine("  exact Extraction.MethodsChecked.nil");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"@[cil_code] theorem lookup{n} : program[{n}]? = some method{n} := rfl");
        lean.AppendLine("end Extracted");
        return new(lean.ToString(), layoutEvidence.Identities, templates.ToArray());
    }
}
