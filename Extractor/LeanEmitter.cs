using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class LeanEmitter
{
    /// <summary>An extraction's Lean source and what it is built from; `Refusals` holds, per method, why it is
    /// written as a literal, or null for a method defined from its decoder.</summary>
    internal readonly record struct Emission(string Source, string[] LayoutIdentities,
        TemplateEmitter.Method[] Templates, ClassViews.View[] Views, ComputedLayout[] Layouts,
        GenericEvidence.DecodeRefusal?[] Refusals);

    internal static Narrowing? Narrow(TypeReference type) => EnumTypes.Storage(type).FullName switch
    {
        "System.SByte" => Narrowing.Signed8,
        "System.Byte" or "System.Boolean" => Narrowing.Unsigned8,
        "System.Int16" => Narrowing.Signed16,
        "System.UInt16" or "System.Char" => Narrowing.Unsigned16,
        _ => null
    };

    // An `init` accessor returns nothing, like a plain void method.
    static bool ReturnsValue(MethodDefinition method) =>
        InitAccessors.Return(method.ReturnType).FullName != "System.Void";

    // The kernel rechecks every decide; elaborator whnf costs grow superlinearly with body size.
    internal const string Decide = "by decide +kernel";
    internal static LocalKind Kind(TypeReference type, ModuleDefinition module, string architecture = "scalar",
        MetadataValidation.LayoutContext? layouts = null)
    {
        layouts?.Require(module, architecture);
        if (ManagedPointers.Signature(type) is { } pointer)
            return type is ArrayType ? new LocalKind.MethodTable(ManagedPointers.SignatureEvidence(pointer))
                : new LocalKind.MethodPointer(ManagedPointers.SignatureEvidence(pointer));
        if (type is ByReferenceType or PointerType) return new LocalKind.Reference();
        if (ObjectTypes.Reference(type) || ReferenceArrays.Is(type)) return new LocalKind.Object();
        if (Arrays.Of(type, architecture) is { } element) return new LocalKind.Array(element);
        if (Spans.Width(type, architecture) is { } width) return new LocalKind.Span(width, Spans.Writable(type));
        if (MetadataValidation.IsAggregate(type, module) || layouts?.IsImported(type) == true)
            return new LocalKind.Aggregate(
                layouts?.Size(type) ?? MetadataValidation.Layout(type, module, architecture));
        if (Narrow(type) is { } narrow) return new LocalKind.Narrow(narrow);
        return EnumTypes.Storage(type).FullName switch
        {
            "System.Int32" or "System.UInt32" => new LocalKind.Word32(),
            "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" => new LocalKind.Word64(),
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector128`1<", StringComparison.Ordinal) =>
                new LocalKind.Vector(128),
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector256`1<", StringComparison.Ordinal) =>
                new LocalKind.Vector(256),
            string s when s.StartsWith("System.Runtime.Intrinsics.Vector512`1<", StringComparison.Ordinal) =>
                new LocalKind.Vector(512),
            _ => throw new InvalidDataException($"Unsupported local: {type.FullName}")
        };
    }
    // An opaque value names no initializer; its zero bytes fix only the load width.
    static StaticSite OpaqueSite(int pc, FieldRef reference, StaticValues.Value value) =>
        new(pc, StaticIdentity.Of(value.Field), reference, value.Bytes,
            new OpaqueStaticValue(StaticValues.ScalarSign(value.Field)));

    static StaticSite SiteOf(Instruction i, int pc, FieldRef reference, MethodDefinition method,
        IReadOnlyDictionary<MethodDefinition, int> methodIndices, FeatureProfile profile)
    {
        if (StaticValues.IsLoad(i))
        {
            var value = StaticValues.Resolve((FieldReference)i.Operand, method.Module, profile.Architecture);
            if (value.Opaque) return OpaqueSite(pc, reference, value);
            int? initializer = value.Initializer is null
                ? null : methodIndices.GetValueOrDefault(value.Initializer, -1);
            if (initializer < 0)
                throw new InvalidDataException($"Missing static initializer: {value.Initializer!.FullName}");
            return new(pc, StaticIdentity.Of(value.Field), reference, value.Bytes,
                new InitializedStaticValue(StaticValues.ScalarSign(value.Field), initializer, value.Arguments,
                    value.Literal, value.Construct));
        }
        FieldDefinition field = StaticData.Validate((FieldReference)i.Operand, method.Module);
        return new(pc, StaticIdentity.Of(field), reference, field.InitialValue,
            new StaticDataBlock(StaticData.Alignment(field)));
    }

    static bool IsStaticSite(Instruction i) => i.OpCode.Code == Code.Ldsflda || StaticValues.IsLoad(i) ||
        (i.OpCode.Code == Code.Ldtoken && i.Operand is FieldReference);
    static FieldDefinition StaticField(Instruction i, ModuleDefinition module, string architecture) => StaticValues.IsLoad(i)
        ? StaticValues.Resolve((FieldReference)i.Operand, module, architecture).Field : StaticData.Validate((FieldReference)i.Operand, module);
    internal static StaticIdentityRecord[] StaticIdentities(MethodDefinition[] methods, FeatureProfile profile) =>
        methods.SelectMany(method => Reachability.Analyze(method, profile)).Where(IsStaticSite)
            .Select(instruction => StaticIdentity.Of(StaticField(instruction, methods[0].Module, profile.Architecture)))
            .Distinct().OrderBy(identity => identity.Identity, StringComparer.Ordinal).ToArray();
    internal static InitialValue Initial(TypeReference type, ModuleDefinition module, string architecture = "scalar",
        MetadataValidation.LayoutContext? layouts = null) => Kind(type, module, architecture, layouts).Initial();
    static TypeReference[] LayoutTypes(MethodDefinition[] methods, MetadataValidation.LayoutContext metadata)
    {
        TypeReference[] types = methods
            .SelectMany(m => m.Parameters.Select(p => InReferences.Parameter(p.ParameterType))
            .Concat(m.HasThis ? [MethodSpecialization.DeclaringType(m)] : [])
            .Concat(m.Body.Variables.Select(v => v.VariableType)).Append(InitAccessors.Return(m.ReturnType))
            .Concat(MethodSpecialization.Arguments(m))
            .Concat(m.Body.Instructions.Where(i => i.Operand is TypeReference).Select(i => (TypeReference)i.Operand))
            .Concat(m.Body.Instructions.Where(i => i.Operand is GenericInstanceMethod).SelectMany(i => ((GenericInstanceMethod)i.Operand).GenericArguments))
            .Concat(m.Body.Instructions.Select(i => i.Operand).OfType<FieldReference>()
                .Select(field => field.DeclaringType))
            // A class field holding an array of structs needs the struct's layout for its element width.
            .Concat(m.Body.Instructions.Select(i => i.Operand).OfType<FieldReference>()
                .Where(field => field.FieldType is ArrayType).Select(field => field.FieldType)))
            .Select(t => t is ByReferenceType r ? r.ElementType : t)
            .Select(t => t is ArrayType array ? array.ElementType : t)
            .Select(t => Spans.Is(t) ? ((GenericInstanceType)t).GenericArguments[0] : t)
            .Where(metadata.IsLayout).Select(metadata.Canonical).DistinctBy(LayoutEvidence.Identity).ToArray();
        List<TypeReference> layouts = [];
        HashSet<string> seenLayouts = new(StringComparer.Ordinal);
        void IncludeLayout(TypeReference type)
        {
            if (!seenLayouts.Add(LayoutEvidence.Identity(type))) return;
            layouts.Add(type);
            foreach (MetadataValidation.InstanceField field in metadata.Fields(type))
                if (metadata.IsLayout(field.Type)) IncludeLayout(metadata.Canonical(field.Type));
        }
        foreach (TypeReference type in types) IncludeLayout(type);
        return layouts.ToArray();
    }

    static string LinkName(int method, int pc) => $"method{method}Link{pc}";

    // These definitions guide proof simplification; the full validator still checks every call.
    static string? CallDefinitions(int caller, IReadOnlyList<Operation> operations, int methodCount)
    {
        var targets = new SortedSet<int> { caller };
        var hasCall = false;
        foreach (var operation in operations)
        {
            // A tail call lists no callee: a method that only tail-calls is proved by `decide`, which unfolds none.
            if (operation is not (Call { Kind: not CallKind.Tail } or Newobj)) continue;
            hasCall = true;
            var target = operation.Methods.Single();
            if (target >= 0 && target < methodCount) targets.Add(target);
        }
        if (!hasCall) return null;
        return string.Join(", ", targets.SelectMany(target =>
            new[] { $"method{target}Closed", $"method{target}TypeArgumentsRaw" }));
    }

    /// <summary>The recursion depth every generated declaration fits in, whatever the method length.</summary>
    const int BaseRecursionDepth = 4096;

    /// <summary>Recursion depth Lean needs per instruction to compile and compare a method's code lists.</summary>
    const int RecursionDepthPerInstruction = 16;

    // Lean compares and compiles a code list one nested cell per instruction, so the depth follows the longest body.
    internal static int RecursionDepth(int longestBody) =>
        Math.Max(BaseRecursionDepth, RecursionDepthPerInstruction * longestBody);

    internal static Emission Emit(MethodDefinition[] methods, FeatureProfile profile, PinnedAssemblies pinned,
        ImportResolution? importResolution = null,
        StaticIdentityRecord[]? staticIdentities = null, bool collectTemplates = false)
    {
        var methodIndices = methods.Select((method, index) => (method, index))
            .ToDictionary(pair => pair.method, pair => pair.index);
        var constrainedTargets = new ConstrainedCalls.TargetIndex(methods);
        var templates = new List<TemplateEmitter.Method>();
        var callDefinitions = new string?[methods.Length];
        var refusals = new GenericEvidence.DecodeRefusal?[methods.Length];
        StringBuilder lean = new($"""
            import CIL.Extraction.Translation
            import CIL.Extraction.DecodedDefinition
            import CIL.SymbolicExecution
            import CIL.InstructionEquations
            import CIL.Safety.Execution
            import CIL.Safety.ResolutionFacts

            namespace Extracted
            open CIL

            set_option maxRecDepth {RecursionDepth(methods.Max(method => method.Body.Instructions.Count))}


            """.ReplaceLineEndings("\n"));
        lean.AppendLine($"@[cil_code] def profile : FeatureProfile := {profile.Lean}");
        lean.AppendLine("theorem profile_valid : profile.Valid := " + Decide);
        StaticIdentity.Validate(staticIdentities ?? StaticIdentities(methods, profile));
        var layoutContext = new MetadataValidation.LayoutContext(methods[0].Module, profile.Architecture);
        if (importResolution is not null) layoutContext.AddImported(importResolution.LocalLayouts());
        TypeReference[] types = LayoutTypes(methods, layoutContext);
        var layouts = new ComputedLayout[types.Length];
        for (int i = 0; i < types.Length; i++)
        {
            int size = layoutContext.Size(types[i]);
            LayoutField[] fields = [.. layoutContext.Fields(types[i]).Select(field => new LayoutField(
                layoutContext.FieldOffset(types[i], field.Definition), layoutContext.FieldSize(field.Type),
                layoutContext.IsLayout(field.Type)))];
            layouts[i] = new ComputedLayout(LayoutEvidence.Identity(types[i]), size, fields);
            lean.AppendLine($"def layout{i} : AggregateLayout := {layouts[i].ToLean()}");
            lean.AppendLine($"theorem layout{i}_valid : layout{i}.Valid := {Decide}");
        }
        LayoutEvidence layoutEvidence = new(types, layoutContext);
        layoutEvidence.EmitLayouts(lean);
        // One shared constant, so a method literal names the tables instead of repeating them.
        lean.AppendLine($"@[cil_code] def {FrameMetadata.EnvironmentLean} : LayoutEnvironment := " +
            "{ rawLayouts := rawLayouts, layouts := computedLayouts }");
        // The shape facts are written here once every method has been translated, so admission reports its own
        // refusals first, and every method's components see them.
        var shapeFactsAt = lean.Length;
        var operandShapes = new OperandShapes();
        GenericEvidence genericEvidence = new(pinned, layoutEvidence, importResolution);
        genericEvidence.EmitAssemblyMetadata(lean);
        var fieldAccesses = new List<ClassViews.Access>();
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
            LocalKind KindOf(TypeReference type, int? local = null) => dispatch.Kind(type, local) ??
                Kind(type, m.Module, profile.Architecture, layoutContext);
            ParameterHome[] homes = [.. parameterIndices.Select(index =>
                new ParameterHome(index, KindOf(MethodArguments.Type(m, index))))];
            InitialValue[] locals = [.. m.Body.Variables.Select(variable => m.Body.InitLocals
                ? dispatch.Kind(variable.VariableType, variable.Index) is not null ? InitialValue.NullRef :
                    Initial(variable.VariableType, m.Module, profile.Architecture, layoutContext)
                : InitialValue.Unmodeled)];
            HashSet<int> addressedLocals = m.Body.Instructions
                .Where(instruction => instruction.OpCode.Code is Code.Ldloca or Code.Ldloca_S)
                .Select(instruction => ((VariableDefinition)instruction.Operand).Index).ToHashSet();
            Operation Translated(Instruction i, int pc)
            {
                var operation = InstructionTranslation.Translate(i, m, methodIndices, n, instructions, profile,
                    scalarCertificate, parameterHomes, importResolution, layoutContext, constrainedTargets);
                // An allocation and a field access name the element or field their raw operand names.
                return operation switch
                {
                    NewArray allocation => allocation with { Element = genericEvidence.ArrayElementOf(m, i) },
                    ClassField access => access with { Reference = genericEvidence.FieldReferenceOf(m, pc) },
                    StaticFieldInstruction access => access with { Field = genericEvidence.FieldReferenceOf(m, pc) },
                    Newobj construction =>
                        construction with { Constructor = genericEvidence.MethodReferenceOf(m, pc) },
                    _ => operation
                };
            }
            List<Operation> ops = [];
            foreach (Instruction i in m.Body.Instructions)
                ops.Add(reachable.Contains(i) ? Translated(i, ops.Count) : Unadmitted.At(i));
            fieldAccesses.AddRange(m.Body.Instructions.Select((instruction, pc) =>
                ClassViews.Of(instruction, n, pc, ops[pc])).OfType<ClassViews.Access>());
            var needsOpaqueLocals = ops.Any(op => op is VectorCreateScalarUnsafe64);
            int[] opaqueLocals = needsOpaqueLocals ? [.. m.Body.Variables
                .Where(variable => variable.VariableType.FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" &&
                    !addressedLocals.Contains(variable.Index)).Select(variable => variable.Index)] : [];
            LocalKind[] kinds =
                [.. m.Body.Variables.Select(variable => KindOf(variable.VariableType, variable.Index))];
            StaticSite[] sites = [.. m.Body.Instructions.Select((i, pc) => (i, pc))
                .Where(s => reachable.Contains(s.i) && IsStaticSite(s.i))
                .Select(s => SiteOf(s.i, s.pc, genericEvidence.FieldReferenceOf(m, s.pc), m, methodIndices,
                    profile))];
            var frame = new FrameMetadata(ReturnsValue(m), locals, kinds, opaqueLocals, homes, sites,
                genericEvidence.Declared(m));
            // The table is derived from the operations, so it needs no renumbering beside the code.
            List<(int Pc, string Link)> linkEntries = [.. ops.Select((op, pc) =>
                (Pc: pc, Link: op.Link(LeanText.MethodNumber))).Where(entry => entry.Link is not null)
                .Select(entry => (entry.Pc, entry.Link!))];
            lean.AppendLine($"def method{n}Signature : String := {JsonSerializer.Serialize(m.FullName)}");
            if (MethodSpecialization.Source(m) is { } origin)
            {
                lean.AppendLine($"def method{n}GenericDefinition : String := {JsonSerializer.Serialize(origin.Definition)}");
                lean.AppendLine($"def method{n}TypeArguments : List String := [{string.Join(", ", origin.TypeArguments.Select(t => JsonSerializer.Serialize(t)))}]");
            }
            callDefinitions[n] = CallDefinitions(n, ops, methods.Length);
            // Each link's text is written once, as a definition the table, the index and its facts name.
            // The cil_code tag lets a simp-driven step unfold a fact's link to its constructor form.
            foreach (var (pc, link) in linkEntries)
                lean.AppendLine($"@[cil_code] def {LinkName(n, pc)} : Link := {link}");
            // One named table, which the literal and the decoder both take, so a decoded method's links are the
            // extractor's and its link facts name the same definitions as a literal's.
            var linkTable = $"method{n}Links";
            lean.AppendLine($"@[cil_code] def {linkTable} : List (Nat × Link) := [" + string.Join(", ",
                linkEntries.Select(entry => $"({entry.Pc}, {LinkName(n, entry.Pc)})")) + "]");
            layoutEvidence.EmitMethod(lean, m, n, reachable, parameterIndices);
            ParameterEvidence.Emit(lean, m, n, reachable, layoutEvidence);
            genericEvidence.EmitMethod(lean, m, n, reachable);
            // A call names the method its raw operand names; a constrained one also the type the definition just
            // written spells for its prefix.
            for (var pc = 0; pc < ops.Count; pc++)
                if (ops[pc] is Call { Kind: not CallKind.Instance } call)
                    ops[pc] = call with
                    {
                        Site = genericEvidence.MethodReferenceOf(m, pc),
                        ConstrainedType = call.Constrained
                            ? genericEvidence.ClosedOperandOf(m.Body.Instructions[pc].Previous) : null
                    };
            if (collectTemplates)
                templates.Add(new(m.FullName, frame, [.. ops], [.. m.Body.Instructions.Select(Unadmitted.RawOpcode)]));
            // A class field access names its operand's definition, so stepping reads that operand's shape fact.
            operandShapes.Add(m, reachable, genericEvidence);
            refusals[n] = GenericEvidence.FirstDecodeRefusal(m, reachable, ops);
            var decoded = refusals[n] is null;
            if (decoded)
            {
                // The decoder's raw definition is the method's only source; the command states its field facts and
                // writes each field operand as the definition the literal form names.
                var naming = string.Join(", ", ops.OfType<ClassField>().Select(access =>
                    operandShapes.FieldName(access.Reference ?? throw new InvalidOperationException(
                        "A class field access has no field operand."))).Distinct());
                lean.AppendLine($"cil_decoded_method method{n} {(naming.Length == 0 ? "" : $"[{naming}] ")}:= " +
                    $"Method.ofRaw? profile {FrameMetadata.EnvironmentLean} {linkTable} method{n}Original " +
                    $"method{n}TypeArgumentsRaw");
            }
            else
            {
                // Links stay out of the frame: templates share it across profiles, but call indices differ.
                lean.AppendLine($"def method{n} : Method := {{ profile := profile, {frame.ToLean()}, " +
                    $"links := {linkTable}, code := [");
                lean.AppendLine(string.Join(",\n", ops.Select(op => "  " +
                    (op is ClassField { Reference: { } field } access
                        ? access.Naming(operandShapes.FieldName(field)) : op.ToLean()))) + "] }");
            }
            lean.AppendLine($"theorem method{n}_layouts_validated : Extraction.MethodLayoutsValid rawLayouts " +
                $"computedLayouts method{n} method{n}LayoutUses := {Decide}");
            lean.AppendLine($"theorem method{n}_parameters_validated : Extraction.ParameterHomesValid " +
                $"computedLayouts method{n}RawArguments method{n}Reachable method{n} := {Decide}");
            FeatureEvidence.Emit(lean, m, n, featureCertificate);
            if (!decoded)
                lean.AppendLine($"@[cil_code] theorem method{n}_opaqueVectorLocals : " +
                    $"method{n}.opaqueVectorLocals = [{frame.OpaqueVectorLocalsLean}] := rfl");
            ScalarEvidence.Emit(lean, m, n, scalarCertificate);
            if (!decoded)
                lean.AppendLine($"@[cil_code] theorem method{n}_parameterHomes : " +
                    $"method{n}.parameterHomes = [{frame.ParameterHomesLean}] := rfl");
            // The command states `method{n}_instruction{pc}` for each pc and `method{n}_link{pc}` for each call site,
            // in time linear in the body, so a stepping proof reads a link without evaluating the table lookup.
            lean.AppendLine($"cil_instruction_equations method{n}");
            (string Field, string Value)[] facts =
            [
                ("profile", "profile"), ("locals", $"[{frame.LocalsLean}]"),
                ("localKinds", $"[{frame.LocalKindsLean}]"), ("returnsValue", frame.ReturnsValueLean),
                ("staticSites", $"[{frame.StaticSitesLean}]"), ("declared", frame.Declared),
                ("environment", FrameMetadata.EnvironmentLean), ("links", linkTable)
            ];
            if (!decoded)
                foreach (var (field, value) in facts)
                    lean.AppendLine($"@[cil_code] theorem method{n}_{field} : method{n}.{field} = ({value}) := rfl");
            lean.AppendLine($"cil_resolution_facts method{n}");
        }
        lean.Insert(shapeFactsAt, operandShapes.Lean());
        lean.AppendLine("def specializedMethods : List Extraction.SpecializedMethod := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"⟨method{n}TypeArgumentsRaw, method{n}Closed⟩")) + "]");
        IReadOnlyList<ImportResolution.Binding> importBindings = importResolution?.Bindings ?? [];
        lean.AppendLine("def imports : List ImportSlot := [" + string.Join(", ", importBindings.Select(ImportResolution.LeanSlot)) + "]");
        // Whole-program data, so it stays after the `specializedMethods` boundary of per-method components;
        // feature obligations read callee certificates through it.
        lean.AppendLine("def methodEvidence : List Extraction.MethodEvidence := [" + string.Join(", ",
            Enumerable.Range(0, methods.Length).Select(n =>
                $"{{ original := method{n}Original, body := method{n}Body, arguments := method{n}TypeArgumentsRaw, " +
                $"closed := method{n}Closed, parameterInput := method{n}RawArguments, " +
                $"reachable := method{n}Reachable, featureStates := method{n}FeatureStates, " +
                $"scalarStates := method{n}ScalarStates, layoutUses := method{n}LayoutUses, " +
                $"dispatchTypes := method{n}DispatchTypes, links := method{n}Links, " +
                $"assembly := assembly{pinned.Index(methods[n].Module)}, " +
                $"signature := method{n}Signature }}")) + "]");
        for (var n = 0; n < methods.Length; n++)
        {
            FeatureEvidence.EmitTheorem(lean, n);
            var facts = $"specializedMethods, imports, Extraction.lowerConstrainedRaw, {callDefinitions[n]}, " +
                $"method{n}, method{n}Reachable, method{n}DispatchTypes";
            var proof = callDefinitions[n] is null ? Decide : $"by cil_managed_calls [{facts}]";
            lean.AppendLine($"theorem method{n}_calls_validated : Extraction.ManagedCallsValid " +
                $"specializedMethods imports (Extraction.lowerConstrainedRaw method{n}DispatchTypes " +
                $"method{n}Closed) method{n}Reachable method{n} := {proof}");
        }
        lean.AppendLine("def program : Program := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"method{n}")) + "]");
        // Proofs resolve methods by signature (CIL.MethodIdentity), so inserted helpers do not renumber them. Each
        // entry is its evidence record's, which the body check equates with the full name its metadata row spells.
        lean.AppendLine("def signatures : List String := methodEvidence.map Extraction.MethodEvidence.signature");
        lean.AppendLine("theorem signatures_length : signatures.length = program.length := rfl");
        lean.AppendLine("def importSignatures : List String := [" + string.Join(", ", importBindings.Select(binding => JsonSerializer.Serialize(binding.Identity))) + "]");
        lean.AppendLine("theorem importSignatures_length : importSignatures.length = imports.length := rfl");
        lean.AppendLine("theorem statics_validated : Extraction.StaticValuesValid program := " + Decide);
        for (int n = 0; n < methods.Length; n++)
        {
            lean.AppendLine($"theorem method{n}_coverage_validated : Extraction.LayoutUsesComplete rawLayouts method{n}Closed method{n}RawArguments method{n}Reachable method{n}LayoutUses := {Decide}");
            lean.AppendLine($"theorem method{n}_constrained_validated : Extraction.ConstrainedCallsValid method{n}DispatchTypes specializedMethods method{n}Closed method{n}Reachable method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_shape_validated : " +
                $"Extraction.MethodShapeValid method{n}Closed method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_unsafe_validated : Extraction.UnsafeCallsValid rawLayouts method{n}Closed method{n}Reachable method{n}.code := {Decide}");
            lean.AppendLine($"theorem method{n}_intrinsics_validated : Extraction.ExactIntrinsicsValid method{n}Closed method{n}Reachable method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_models_validated : " +
                $"Extraction.RuntimeModelsAgree method{n}Closed method{n}Reachable method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_opaque_validated : Extraction.OpaqueLocalsValid method{n}Closed method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_vector_initializations_validated : Extraction.VectorInitializationsValid method{n}Closed method{n}Reachable method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_environment_validated : " +
                $"Extraction.MethodEnvironmentValid rawLayouts computedLayouts method{n} := rfl");
            lean.AppendLine($"theorem method{n}_declared_validated : " +
                $"Extraction.DeclaredValid method{n}Closed method{n} := rfl");
            lean.AppendLine($"theorem method{n}_evidence_validated : Extraction.MethodEvidenceValid rawLayouts " +
                $"computedLayouts assemblies methodEvidence imports methodEvidence[{n}] method{n} :=");
            lean.AppendLine($"  ⟨method{n}_specialization_validated, method{n}_parameters_validated, " +
                $"method{n}_layouts_validated, method{n}_features_validated, method{n}_calls_validated, " +
                $"method{n}_coverage_validated, method{n}_shape_validated, method{n}_unsafe_validated, " +
                $"method{n}_intrinsics_validated, method{n}_models_validated, method{n}_opaque_validated, " +
                $"method{n}_vector_initializations_validated, method{n}_scalars_validated, " +
                $"method{n}_constrained_validated, method{n}_body_validated,");
            lean.AppendLine($"    method{n}_environment_validated, method{n}_declared_validated⟩");
        }
        lean.AppendLine("theorem import_layouts_validated : Extraction.ImportedLayoutsValid imports profile.architecture := " + Decide);
        lean.AppendLine("#print axioms import_layouts_validated");
        lean.AppendLine("theorem imported_locals_validated : " +
            "Extraction.ImportedLocalLayoutsBound rawLayouts computedLayouts imports := " + Decide);
        lean.AppendLine("theorem attribution_validated : " +
            "Extraction.AttributionValid (Extraction.bodyOwners methodEvidence) = true := " + Decide);
        lean.AppendLine("theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts " +
            "assemblies methodEvidence imports program := by");
        lean.AppendLine("  apply Extraction.translation_of_methods (program := program) layouts_validated statics_validated import_layouts_validated");
        lean.AppendLine("    imported_locals_validated attribution_validated");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"  refine Extraction.MethodsChecked.cons method{n}_evidence_validated ?_");
        lean.AppendLine("  exact Extraction.MethodsChecked.nil");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"@[cil_code] theorem lookup{n} : program[{n}]? = some method{n} := rfl");
        var classViews = ClassViews.Views(fieldAccesses);
        var views = ClassViews.Emit(fieldAccesses, classViews);
        if (views.Length > 0)
        {
            lean.Append(views);
            const string imported = "import CIL.Safety.Execution\n";
            lean.Replace(imported, imported + "import CIL.Safety.ObjectFields\n", 0, lean.ToString().IndexOf(imported,
                StringComparison.Ordinal) + imported.Length);
        }
        lean.AppendLine("end Extracted");
        return new(lean.ToString(), layoutEvidence.Identities, templates.ToArray(), classViews, layouts, refusals);
    }

    /// <summary>
    /// The distinct field and type operands of the reachable field and value-type instructions of every method, each
    /// written once as a definition beside the fact that states how every method of the extraction resolves it.
    /// </summary>
    internal sealed class OperandShapes
    {
        readonly Dictionary<FieldRef, int> fields = [];
        // TypeExpr has no typed C# form, so a type operand is keyed by its rendered term.
        readonly Dictionary<string, int> types = new(StringComparer.Ordinal);
        readonly StringBuilder text = new();

        /// <summary>
        /// Records the operands of <paramref name="method"/>'s reachable instructions not seen before.
        /// </summary>
        internal void Add(MethodDefinition method, IReadOnlySet<Instruction> reachable, GenericEvidence evidence)
        {
            for (var pc = 0; pc < method.Body.Instructions.Count; pc++)
            {
                var instruction = method.Body.Instructions[pc];
                if (!reachable.Contains(instruction)) continue;
                if (instruction.OpCode.Code is Code.Ldfld or Code.Ldflda or Code.Stfld)
                {
                    var field = evidence.FieldReferenceOf(method, pc);
                    if (!fields.TryAdd(field, fields.Count)) continue;
                    var name = $"fieldRef{fields[field]}";
                    text.AppendLine($"def {name} : Extraction.FieldRef := {field.ToLean()}");
                    text.AppendLine($"cil_field_shape {FrameMetadata.EnvironmentLean} {name}");
                }
                else if (instruction.OpCode.Code is
                    Code.Ldobj or Code.Stobj or Code.Initobj or Code.Cpobj or Code.Sizeof)
                {
                    var type = evidence.TypeOperandOf(method, instruction);
                    if (!types.TryAdd(type, types.Count)) continue;
                    var name = $"valueType{types[type]}";
                    text.AppendLine($"def {name} : Extraction.TypeExpr := {type}");
                    text.AppendLine($"cil_value_shape {FrameMetadata.EnvironmentLean} {name}");
                }
            }
        }

        /// <summary>The definition that names the recorded field operand <paramref name="field"/>.</summary>
        internal string FieldName(FieldRef field) => $"fieldRef{fields[field]}";

        /// <summary>The definitions and facts of every recorded operand, in the order first seen.</summary>
        internal string Lean() => text.ToString();
    }
}
