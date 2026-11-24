using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class LeanEmitter
{
    /// <summary>An extraction's Lean source and what it is built from.</summary>
    internal readonly record struct Emission(string Source, string[] LayoutIdentities,
        TemplateEmitter.Method[] Templates, ProofOutline.Method[] Outlines, ClassViews.View[] Views,
        IReadOnlyList<ClassViews.Access> ClassFields,
        ComputedLayout[] Layouts, string TemplateInputs);

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
            return type is ArrayType ? new LocalKind.MethodTable(new(pointer))
                : new LocalKind.MethodPointer(new(pointer));
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
    internal static StaticIdentityRecord[] StaticIdentities(MethodDefinition[] methods, FeatureProfile profile) =>
        methods.SelectMany(method => Reachability.Analyze(method, profile)).Where(IsStaticSite)
            .Select(instruction => StaticIdentity.Of(
                StaticData.FieldOf(instruction, methods[0].Module, profile.Architecture)))
            .Distinct().OrderBy(identity => identity.Identity, StringComparer.Ordinal).ToArray();
    internal static InitialValue Initial(TypeReference type, ModuleDefinition module, string architecture = "scalar",
        MetadataValidation.LayoutContext? layouts = null) => Kind(type, module, architecture, layouts).Initial();
    static TypeReference[] LayoutTypes(MethodDefinition[] methods, MetadataValidation.LayoutContext metadata)
    {
        var types = methods
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
            .Where(metadata.IsLayout);
        List<TypeReference> layouts = [];
        HashSet<TypeReference> seenReferences = new(ReferenceEqualityComparer.Instance);
        Dictionary<string, StructuralSignatures.Signature> identities = new(StringComparer.Ordinal);
        void IncludeLayout(TypeReference reference)
        {
            if (!seenReferences.Add(reference)) return;
            var spelling = LayoutEvidence.Identity(reference);
            var signature = metadata.Signature(reference);
            if (identities.TryGetValue(spelling, out var previous))
            {
                if (previous != signature) throw new InvalidDataException($"Ambiguous layout identity: {spelling}");
                return;
            }
            identities.Add(spelling, signature);
            var type = metadata.Canonical(reference);
            if (!ReferenceEquals(type, reference) && metadata.Signature(type) != signature)
                throw new InvalidDataException($"Ambiguous imported layout identity: {spelling}");
            metadata.RequireEmittableName(type);
            layouts.Add(type);
            foreach (MetadataValidation.InstanceField field in metadata.Fields(type))
                if (metadata.IsLayout(field.Type)) IncludeLayout(field.Type);
        }
        foreach (TypeReference type in types) IncludeLayout(type);
        return layouts.ToArray();
    }

    static string LinkName(int method, int pc) => $"method{method}Link{pc}";

    /// <summary>The recursion depth every generated declaration fits in, whatever the method length.</summary>
    const int BaseRecursionDepth = 4096;

    /// <summary>Recursion depth Lean needs per instruction to compile and compare a method's code lists.</summary>
    const int RecursionDepthPerInstruction = 16;

    // Lean compares and compiles a code list one nested cell per instruction, so the depth follows the longest body.
    internal static int RecursionDepth(int longestBody) =>
        Math.Max(BaseRecursionDepth, RecursionDepthPerInstruction * longestBody);

    /// <summary>Lean's default heartbeat budget, which the instruction checks of a shorter body fit in.</summary>
    const int BaseHeartbeats = 200_000;

    /// <summary>Twice the 60 heartbeats per instruction the instruction checks measured on an arithmetic body.</summary>
    const int HeartbeatsPerInstruction = 120;

    /// <summary>Twice the 216 heartbeats each call site added to the instruction checks of a body of linked calls.</summary>
    const int HeartbeatsPerCall = 432;

    // The kernel decides the instruction checks once per site and a call site costs more, so the budget counts both.
    internal static int InstructionCheckHeartbeats(int instructions, int calls) =>
        Math.Max(BaseHeartbeats, HeartbeatsPerInstruction * instructions + HeartbeatsPerCall * calls);

    /// <summary>The closed decoder and its specialization determine the method and every code position.</summary>
    static void EmitDecodedMethod(StringBuilder lean, int n, string fields, StringBuilder? decoderInputs)
    {
        var method = $"method{n}";
        var decoderArgs = $"profile {FrameMetadata.EnvironmentLean} method{n}Links {method}Reachable";
        var closedDecoder = $"Method.ofClosed? {decoderArgs} {method}Closed {method}RawArguments";
        decoderInputs?.AppendLine($"cil_decoded_method {method} := {closedDecoder}");
        var rawDecoder = $"Method.ofRaw? {decoderArgs} {method}Original {method}TypeArgumentsRaw";
        const string equality = "Extraction.SpecializationValid.ofRaw?_eq_ofClosed?";
        var environment = $"(environment := {FrameMetadata.EnvironmentLean})";
        var evidence = $"{method}_specialization_validated profile method{n}Links {method}Reachable";
        var closedProof = $"(congrArg Except.toOption {method}_decoder_eq)";
        var proof = $"Eq.trans ({equality} {environment} {evidence}) {closedProof}";
        var inputs = $"{decoderArgs} {method}Closed {method}RawArguments {method}";
        var code = $"Extraction.methodCode {decoderArgs} {method}Closed";
        var codeProof = $"@Method.ofClosed?_code {inputs} {method}_decoder_eq";
        lean.AppendLine($"""
            cil_decoded_method {method} {fields}:= {closedDecoder}
            theorem {method}_decoded : {rawDecoder} = some {method} := {proof}
            theorem {method}_decoded_code : {method}.code = {code} := {codeProof}
            """);
    }

    internal static Emission Emit(MethodDefinition[] methods, FeatureProfile profile, PinnedAssemblies pinned,
        ResolvedCallSites callSites, ImportResolution? importResolution = null,
        StaticIdentityRecord[]? staticIdentities = null, bool collectOutlines = false, bool templateInputs = false,
        bool compareOriginal = false)
    {
        var methodIndices = methods.Select((method, index) => (method, index))
            .ToDictionary(pair => pair.method, pair => pair.index);
        var templates = new List<TemplateEmitter.Method>();
        var outlines = new List<ProofOutline.Method>();
        var rangeConstructor = methods.Length == 1 && importResolution?.Bindings.Count is null or 0
            ? Throws.TwoStringRangeConstructor(methods[0]) : null;
        var runtimeImport = rangeConstructor is null ? "" : "import CIL.Runtime.Net11WinX64.RangeConstructor\n";
        StringBuilder lean = new($"""
            import CIL.Extraction.Translation
            import CIL.Extraction.DecodedDefinition
            import CIL.SymbolicExecution
            import CIL.InstructionEquations
            import CIL.Safety.Execution
            import CIL.Safety.ResolutionFacts

            {runtimeImport}namespace Extracted
            open CIL

            set_option maxRecDepth {RecursionDepth(methods.Max(method => method.Body.Instructions.Count))}


            """.ReplaceLineEndings("\n"));
        StringBuilder? inputs = templateInputs ? new() : null;
        var profileDefinition = $"def profile : FeatureProfile := {profile.Lean}";
        lean.AppendLine($"@[cil_code] {profileDefinition}");
        inputs?.AppendLine(profileDefinition);
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
            var layout = $"def layout{i} : AggregateLayout := {layouts[i].ToLean()}";
            lean.AppendLine(layout);
            inputs?.AppendLine(layout);
            lean.AppendLine($"theorem layout{i}_valid : layout{i}.Valid := {Decide}");
        }
        LayoutEvidence layoutEvidence = new(types, layoutContext);
        layoutEvidence.EmitLayouts(lean, inputs);
        // One shared constant, so each method and its evidence name the tables instead of repeating them.
        const string tables = "{ rawLayouts := rawLayouts, layouts := computedLayouts }";
        var environment = $"def {FrameMetadata.EnvironmentLean} : LayoutEnvironment := {tables}";
        lean.AppendLine($"@[cil_code] {environment}");
        inputs?.AppendLine(environment);
        // The shape facts are written here once every method has been translated, so admission reports its own
        // refusals first, and every method's components see them.
        IReadOnlyList<ImportResolution.Binding> importBindings = importResolution?.Bindings ?? [];
        GenericEvidence genericEvidence = new(pinned, layoutEvidence, importResolution);
        var importNames = importBindings.Select(binding =>
            genericEvidence.ExternalIdentities.Reference(binding.Identity, reachable: true)).ToArray();
        genericEvidence.ExternalIdentities.Emit(lean, inputs);
        var slots = string.Join(", ", importBindings.Zip(importNames, ImportResolution.LeanSlot));
        lean.AppendLine($"""def imports : List ImportSlot := [{slots}]""");
        if (importBindings.Count != 0)
            lean.AppendLine("""
                /-- The package's checked call slots and published layout identities. -/
                def importIndex : Extraction.ImportSlotIndex := .ofList imports
                """);
        var shapeFactsAt = lean.Length;
        var operandShapes = new OperandShapes(layoutEvidence);
        genericEvidence.EmitAssemblyMetadata(lean);
        var fieldAccesses = new List<ClassViews.Access>();
        for (int n = 0; n < methods.Length; n++)
        {
            MethodDefinition m = methods[n];
            var featureCertificate = Reachability.Certify(m, profile);
            var reachable = featureCertificate.Keys.ToHashSet();
            var scalarCertificate = NativeOperands.Certify(m, reachable, profile);
            var parameterIndices = ParameterStorage.Analyze(m, reachable);
            var dispatch = NativeDispatch.For(m);
            LocalKind KindOf(TypeReference type, int? local = null) => dispatch.Kind(type, local) ??
                Kind(type, m.Module, profile.Architecture, layoutContext);
            ParameterHome[] homes = [.. parameterIndices.Select(index =>
                new ParameterHome(index, KindOf(MethodArguments.Type(m, index))))];
            InitialValue[] locals = [.. m.Body.Variables.Select(variable => m.Body.InitLocals
                ? dispatch.Kind(variable.VariableType, variable.Index) is not null ? InitialValue.NullRef :
                    Initial(variable.VariableType, m.Module, profile.Architecture, layoutContext)
                : InitialValue.Unmodeled)];

            fieldAccesses.AddRange(m.Body.Instructions.Select((site, pc) => reachable.Contains(site)
                ? ClassViews.Of(site, n, pc, profile.Architecture) : null).OfType<ClassViews.Access>());
            LocalKind[] kinds =
                [.. m.Body.Variables.Select(variable => KindOf(variable.VariableType, variable.Index))];
            StaticSite[] sites = [.. m.Body.Instructions.Select((i, pc) => (i, pc))
                .Where(s => reachable.Contains(s.i) && IsStaticSite(s.i))
                .Select(s => SiteOf(s.i, s.pc, genericEvidence.FieldReferenceOf(m, s.pc), m, methodIndices,
                    profile))];
            var frame = new FrameMetadata(ReturnsValue(m), locals, kinds, [], homes, sites,
                genericEvidence.Declared(m));
            SortedSet<int>? linkedMethods = templateInputs ? [] : null;
            var linkEntries = callSites.Links(m, reachable, methodIndices, importResolution,
                layoutContext, linkedMethods);
            lean.AppendLine($"def method{n}Signature : String := {IdentityText.Quote(m.FullName)}");
            if (MethodSpecialization.Source(m) is { } origin)
            {
                var definition = IdentityText.Quote(origin.Definition);
                var arguments = string.Join(", ", origin.TypeArguments.Select(IdentityText.Quote));
                lean.AppendLine($"def method{n}GenericDefinition : String := {definition}");
                lean.AppendLine($"def method{n}TypeArguments : List String := [{arguments}]");
            }
            // Each link's text is written once, as a definition the table, the index and its facts name.
            // The cil_code tag lets a simp-driven step unfold a fact's link to its constructor form.
            var inputStart = lean.Length;
            foreach (var (pc, link) in linkEntries)
                lean.AppendLine($"@[cil_code] def {LinkName(n, pc)} : Link := {link}");
            // One named table, which the decoder takes, so a decoded method's links are the extractor's and its
            // link facts name these definitions.
            var linkTable = $"method{n}Links";
            lean.AppendLine($"@[cil_code] def {linkTable} : List (Nat × Link) := [" + string.Join(", ",
                linkEntries.Select(entry => $"({entry.Pc}, {LinkName(n, entry.Pc)})")) + "]");
            inputs?.Append(lean, inputStart, lean.Length - inputStart);
            layoutEvidence.EmitMethod(lean, m, n, reachable, parameterIndices);
            inputStart = lean.Length;
            ParameterEvidence.Emit(lean, m, n, reachable, layoutEvidence);
            var staticInput = "";
            if (sites.Length != 0)
            {
                var table = $"method{n}StaticFields";
                var entries = sites.Select(site =>
                {
                    var descriptor = site.DescriptorLean(LeanText.MethodNumber);
                    var size = "";
                    if (site.Detail is StaticDataBlock)
                    {
                        var field = (FieldReference)m.Body.Instructions[site.Pc].Operand;
                        size = $", rvaSize := some {field.FieldType.Resolve().ClassSize}";
                    }
                    return $$"""({{site.Pc}}, { descriptor := {{descriptor}}{{size}} })""";
                });
                var fields = string.Join(", ", entries);
                lean.AppendLine($"def {table} : List (Prod Nat Extraction.StaticFieldSite) := [{fields}]");
                staticInput = $"staticFields := {table}, ";
            }
            inputs?.Append(lean, inputStart, lean.Length - inputStart);
            genericEvidence.EmitMethod(lean, m, n, reachable, methods.Length, staticInput, inputs, compareOriginal);
            if (rangeConstructor is not null && reachable.Contains(rangeConstructor))
            {
                var pc = m.Body.Instructions.IndexOf(rangeConstructor);
                lean.AppendLine($"/-- Managed range constructor image for .NET 11.0.0 Windows x64. -/\n" +
                    $"def method{n}RangeImage{pc} := CIL.Runtime.Net11WinX64.rangeImage? " +
                    $"method{n}Body method{n}Original {pc} profile environment");
            }
            // A field access names its operand's definition, so stepping reads that operand's shape fact.
            var (naming, objectProof) = operandShapes.RecordMethod(m, n, reachable, genericEvidence);
            if (GenericEvidence.FirstDecodeRefusal(m, reachable, callSites, importResolution) is { } refusal)
                throw new GenericEvidence.UndecodedInstruction(m, refusal);
            if (templateInputs)
            {
                var features = reachable.Where(site => site.OpCode.Code == Code.Call && callSites.IsModel(site))
                    .Select(site => FeatureProfile.Getter((MethodReference)site.Operand)).OfType<Feature>()
                    .Distinct().Order().ToArray();
                templates.Add(new(m.FullName, frame, features,
                    [.. m.Body.Instructions.Select(InstructionOperands.RawOpcode)], linkedMethods!.ToArray()));
            }
            if (collectOutlines)
            {
                var instructions = new InstructionIndex(m);
                var parameterHomes = ParameterStorage.IndexHomes(parameterIndices, frame.Locals.Count);
                foreach (var site in m.Body.Instructions)
                    if (reachable.Contains(site))
                        OutlineInstructions.Validate(site, m, methodIndices, instructions, callSites,
                            profile, scalarCertificate, parameterHomes, importResolution, layoutContext);
                outlines.Add(new(frame, m, reachable, parameterHomes, profile, layoutContext,
                    instructions, callSites, methodIndices, importResolution, scalarCertificate));
            }
            // The decoder's raw definition is the method's only source; the command states its field facts and
            // writes each field operand as the definition the operand shapes name.
            var namedOperands = naming.Length == 0 ? "" : $"[{naming}] ";
            EmitDecodedMethod(lean, n, namedOperands, inputs);

            const string layoutTables = "Extraction.MethodLayoutsValid rawLayouts computedLayouts";
            var layoutCheck = $"{layoutTables} method{n} method{n}LayoutUses";
            lean.AppendLine($"theorem method{n}_layouts_validated : {layoutCheck} := ⟨layouts_validated, {Decide}⟩");
            lean.AppendLine($"theorem method{n}_parameters_validated : Extraction.ParameterHomesValid " +
                $"computedLayouts method{n}RawArguments method{n}Reachable method{n} := {Decide}");
            FeatureEvidence.Emit(lean, m, n, featureCertificate);
            ScalarEvidence.Emit(lean, m, n, scalarCertificate, objectProof);
            // The command states `method{n}_instruction{pc}` for each pc and `method{n}_link{pc}` for each call site,
            // in time linear in the body, so a stepping proof reads a link without evaluating the table lookup.
            lean.AppendLine($"cil_instruction_equations method{n}");
            // A modelled call's step reads its model from the fact the command states for its pc.
            if (reachable.Any(callSites.IsModel)) lean.AppendLine($"cil_runtime_models method{n}");
            lean.AppendLine($"cil_resolution_facts method{n}");
        }
        // The platform definitions sit after the shape facts' position, so they go in first.
        genericEvidence.InsertPlatformDefinitions(lean);
        lean.Insert(shapeFactsAt, operandShapes.Lean());
        var specialized = Enumerable.Range(0, methods.Length).Select(n =>
            $"⟨method{n}TypeArgumentsRaw, method{n}Closed, assembly{pinned.Index(methods[n].Module)}⟩");
        lean.AppendLine("def specializedMethods : List Extraction.SpecializedMethod := [" +
            string.Join(", ", specialized) + "]");
        // Whole-program data, so it stays after the `specializedMethods` boundary of per-method components;
        // feature obligations read callee certificates through it.
        var records = Enumerable.Range(0, methods.Length).Select(n =>
        {
            var method = $"method{n}";
            var fields = string.Join(", ",
                $"original := {method}Original", $"body := {method}Body", $"arguments := {method}TypeArgumentsRaw",
                $"closed := {method}Closed", $"parameterInput := {method}RawArguments",
                $"reachable := {method}Reachable",
                $"featureStates := {method}FeatureStates", $"scalarStates := {method}ScalarStates",
                $"layoutUses := {method}LayoutUses", $"dispatchTypes := {method}DispatchTypes",
                $"links := {method}Links",
                $"assembly := assembly{pinned.Index(methods[n].Module)}", $"signature := {method}Signature");
            return $$"""{ {{fields}} }""";
        });
        lean.AppendLine($"""def methodEvidence : List Extraction.MethodEvidence := [{string.Join(", ", records)}]""");
        for (var n = 0; n < methods.Length; n++)
        {
            FeatureEvidence.EmitTheorem(lean, n);
            lean.AppendLine($"theorem method{n}_models_validated : " +
                $"Extraction.RuntimeModelsAgree method{n}Closed method{n}Reachable method{n} := " +
                $"Extraction.RuntimeModelsAgree.of_closed method{n}_decoder_eq method{n}_features_validated");
            lean.AppendLine($"theorem method{n}_calls_validated : Extraction.ManagedCallsValid " +
                $"specializedMethods imports (Extraction.callModelled method{n}) " +
                $"(Extraction.lowerConstrainedRaw method{n}DispatchTypes " +
                $"method{n}Closed) method{n}Reachable method{n} := {Decide}");
        }
        lean.AppendLine("def program : Program := [" + string.Join(", ", Enumerable.Range(0, methods.Length).Select(n => $"method{n}")) + "]");
        // Proofs resolve methods by signature (CIL.MethodIdentity), so inserted helpers do not renumber them. Each
        // entry is its evidence record's, which the body check equates with the full name its metadata row spells.
        lean.AppendLine("def signatures : List String := methodEvidence.map Extraction.MethodEvidence.signature");
        lean.AppendLine("theorem signatures_length : signatures.length = program.length := rfl");
        var signatures = string.Join(", ", importNames);
        lean.AppendLine($"def importSignatures : List String := [{signatures}]");
        lean.AppendLine("theorem importSignatures_length : importSignatures.length = imports.length := rfl");
        lean.AppendLine("theorem statics_validated : Extraction.StaticValuesValid program := " + Decide);
        lean.AppendLine("theorem static_identities_validated : Extraction.StaticIdentitiesValid program " +
            "(methodEvidence.map (·.body)) := " + Decide);
        for (int n = 0; n < methods.Length; n++)
        {
            lean.AppendLine($"theorem method{n}_coverage_validated : Extraction.LayoutUsesComplete rawLayouts method{n}Closed method{n}RawArguments method{n}Reachable method{n}LayoutUses := {Decide}");
            lean.AppendLine($"theorem method{n}_constrained_validated : Extraction.ConstrainedCallsValid method{n}DispatchTypes specializedMethods method{n}Closed method{n}Reachable method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_shape_validated : " +
                $"Extraction.MethodShapeValid method{n}Closed method{n} := {Decide}");

            lean.AppendLine($"theorem method{n}_opaque_validated : Extraction.OpaqueLocalsValid method{n}Closed method{n} := {Decide}");
            lean.AppendLine($"theorem method{n}_environment_validated : " +
                $"Extraction.MethodEnvironmentValid rawLayouts computedLayouts method{n} := rfl");
            lean.AppendLine($"theorem method{n}_declared_validated : " +
                $"Extraction.DeclaredValid method{n}Closed method{n} := rfl");
            lean.AppendLine($"theorem method{n}_evidence_validated : Extraction.MethodEvidenceValid rawLayouts " +
                $"computedLayouts assemblies platformDefinitions methodEvidence imports methodEvidence[{n}] " +
                $"method{n} :=");
            lean.AppendLine($"  ⟨method{n}_specialization_validated, method{n}_parameters_validated, " +
                $"method{n}_layouts_validated, method{n}_features_validated, method{n}_calls_validated, " +
                $"method{n}_coverage_validated, method{n}_shape_validated, method{n}_unsafe_validated, " +
                $"method{n}_decoder_eq, method{n}_opaque_validated, " +
                $"method{n}_object_operands_validated, method{n}_scalars_validated, " +
                $"method{n}_constrained_validated, method{n}_body_validated,");
            lean.AppendLine($"    method{n}_environment_validated, method{n}_declared_validated, rfl, rfl\u27e9");
        }
        lean.AppendLine("theorem import_layouts_validated : Extraction.ImportedLayoutsValid imports profile.architecture := " + Decide);
        lean.AppendLine("#print axioms import_layouts_validated");
        lean.AppendLine("theorem imported_locals_validated : " +
            "Extraction.ImportedLocalLayoutsBound rawLayouts computedLayouts imports := " + Decide);
        lean.AppendLine("theorem attribution_validated : " +
            "Extraction.AttributionValid (Extraction.bodyOwners methodEvidence) = true := " + Decide);
        lean.AppendLine("theorem dispatch_pins_validated : " +
            "Extraction.DispatchPinsValid assemblies methodEvidence = true := " + Decide);
        lean.AppendLine("theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts " +
            "assemblies platformDefinitions methodEvidence imports program := by");
        lean.AppendLine("  apply Extraction.translation_of_methods (program := program) layouts_validated");
        lean.AppendLine("    statics_validated static_identities_validated import_layouts_validated");
        lean.AppendLine("    imported_locals_validated attribution_validated dispatch_pins_validated");
        for (int n = 0; n < methods.Length; n++)
            lean.AppendLine($"  refine Extraction.MethodsChecked.cons method{n}_evidence_validated ?_");
        lean.AppendLine("  exact Extraction.MethodsChecked.nil");
        // One index of the program, checked once, serves every closure and run that reads it.
        lean.AppendLine("/-- The number of methods in the extracted program. -/");
        lean.AppendLine($"def programLength : Nat := {methods.Length}");
        lean.AppendLine("theorem programLength_eq : programLength = program.length := by cil_kernel_rfl");
        lean.AppendLine("/-- The balanced index of the extracted methods in program order. -/");
        lean.AppendLine("def programIndex : Extraction.FlowIndex Method := program_index% program");
        lean.AppendLine("""
            theorem programIndex_eq : programIndex = Extraction.FlowIndex.ofList program := by cil_kernel_rfl
            """);
        lean.AppendLine("theorem programIndex_get? (index : Nat) : programIndex.get? index = program[index]? := by");
        lean.AppendLine("  rw [programIndex_eq]; exact Extraction.FlowIndex.get?_ofList program index");
        ProgramLookupFacts.Append(lean, "program", "method", methods.Length);
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
        return new(lean.ToString(), layoutEvidence.Identities, templates.ToArray(), outlines.ToArray(), classViews,
            fieldAccesses, layouts,
            inputs?.ToString().ReplaceLineEndings("\n") ?? "");
    }

    /// <summary>
    /// The distinct field and type operands of the reachable field and value-type instructions of every method, each
    /// written once as a definition beside the fact that states how every method of the extraction resolves it.
    /// </summary>
    internal sealed class OperandShapes(LayoutEvidence layouts)
    {
        readonly Dictionary<FieldRef, string> fields = [];
        // TypeExpr has no typed C# form, so a type operand is keyed by its rendered term.
        readonly Dictionary<string, string> types = new(StringComparer.Ordinal);
        readonly StringBuilder text = new();

        /// <summary>Records the reachable raw operands and names the shape facts used by this method.</summary>
        internal (string Names, string? ObjectProof) RecordMethod(MethodDefinition method, int index,
            IReadOnlySet<Instruction> reachable, GenericEvidence evidence)
        {
            var names = new List<string>();
            var operands = new List<(int Opcode, string Type)>();
            var needsLayout = false;
            for (var pc = 0; pc < method.Body.Instructions.Count; pc++)
            {
                var instruction = method.Body.Instructions[pc];
                if (!reachable.Contains(instruction)) continue;
                if (instruction.OpCode.Code is Code.Ldfld or Code.Ldflda or Code.Stfld)
                    names.Add(RecordField(evidence.FieldReferenceOf(method, pc)));
                else if (instruction.OpCode.Code is
                    Code.Ldobj or Code.Stobj or Code.Initobj or Code.Cpobj or Code.Sizeof)
                {
                    var type = (TypeReference)instruction.Operand;
                    var name = RecordType(evidence.ClosedOperandOf(instruction));
                    names.Add(name);
                    operands.Add((InstructionOperands.RawOpcode(instruction), name));
                    needsLayout |= !Spans.Is(type) && MetadataValidation.IsAggregate(type, method.Module);
                }
            }
            // The method names each operand once, but its admission proof checks every object instruction in order.
            var proof = needsLayout ? ObjectOperandProof.Render($"method{index}", operands) : null;
            return (string.Join(", ", names.Distinct(StringComparer.Ordinal)), proof);
        }

        string RecordField(FieldRef field)
        {
            if (fields.TryGetValue(field, out var name)) return name;
            name = $"fieldRef{fields.Count}";
            fields.Add(field, name);
            var operand = field with
            {
                Owner = layouts.NamedOperandType(field.Owner), Type = layouts.NamedOperandType(field.Type)
            };
            text.AppendLine($"def {name} : Extraction.FieldRef := {operand.ToLean()}");
            text.AppendLine($"cil_field_shape {FrameMetadata.EnvironmentLean} {name}");
            return name;
        }

        string RecordType(string type)
        {
            if (types.TryGetValue(type, out var name)) return name;
            name = $"valueType{types.Count}";
            types.Add(type, name);
            text.AppendLine($"def {name} : Extraction.TypeExpr := {layouts.NamedOperandType(type)}");
            text.AppendLine($"cil_value_shape {FrameMetadata.EnvironmentLean} {name}");
            return name;
        }

        /// <summary>The definitions and facts of every recorded operand, in the order first seen.</summary>
        internal string Lean() => text.ToString();
    }
}
