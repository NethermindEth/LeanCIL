using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Raw metadata is serialized separately from computed sizes/offsets. Lean recomputes
// those values and checks their uses in the emitted method rather than trusting them.
internal sealed class LayoutEvidence
{
    readonly TypeReference[] rawTypes;
    readonly string[] identityTerms;
    readonly Dictionary<string, string> namedOperandTypes = new(StringComparer.Ordinal);
    // Raw metadata is topological; emitted layout constants retain the caller supplied order.
    readonly Dictionary<StructuralSignatures.Signature, int> emittedIndices = [];
    readonly Dictionary<StructuralSignatures.Signature, int> typeIndices = [];
    readonly MetadataValidation.LayoutContext layouts;
    string Architecture => layouts.Architecture;

    internal LayoutEvidence(TypeReference[] types, MetadataValidation.LayoutContext layouts)
    {
        this.layouts = layouts;
        for (var index = 0; index < types.Length; index++)
            emittedIndices.TryAdd(layouts.Signature(types[index]), index);
        rawTypes = Topological(types);
        identityTerms = new string[rawTypes.Length];
        for (var index = 0; index < rawTypes.Length; index++)
        {
            var type = rawTypes[index];
            var identity = Identity(type);
            typeIndices.Add(layouts.Signature(type), index);
            identityTerms[index] = rawTypes.Length == 1 ? IdentityText.Quote(identity) :
                ScopedIdentityTerm(identity, Scope(type).Length + "::".Length);
        }
    }

    TypeReference[] Topological(TypeReference[] entries)
    {
        var ordered = new List<TypeReference>();
        var seen = new HashSet<StructuralSignatures.Signature>();
        void Include(TypeReference type)
        {
            if (!seen.Add(layouts.Signature(type))) return;
            foreach (var field in layouts.Fields(type))
                if (MetadataValidation.IsAggregate(field.Type, type.Module)) Include(field.Type);
            ordered.Add(type);
        }
        foreach (TypeReference entry in entries.OrderBy(Identity, StringComparer.Ordinal)) Include(entry);
        return [.. ordered];
    }

    /// <summary>The original TypeRef and its declaring types, with the outermost type on top.</summary>
    internal static Stack<TypeReference> ForwardingPath(TypeReference type)
    {
        var path = new Stack<TypeReference>();
        var seen = new HashSet<TypeReference>(ReferenceEqualityComparer.Instance);
        for (var level = type; level is not null; level = level.DeclaringType)
        {
            if (!seen.Add(level))
                throw new InvalidDataException("Cyclic forwarding scope at " + level.MetadataToken);
            path.Push(level);
        }
        return path;
    }

    internal static string Scope(TypeReference type)
    {
        if (type.Scope is not AssemblyNameReference assembly) return type.Module.Assembly.Name.FullName;
        // Primitive signature elements carry their module's core AssemblyRef directly.
        var pins = PinnedAssemblies.Active;
        if (pins?.Signatures.IsPrimitiveElement(type) == true) return assembly.FullName;
        var module = pins?.ModuleOf(type);
        if (module is not { HasExportedTypes: true }) return assembly.FullName;
        var element = type.GetElementType();
        var outer = element.DeclaringType is null ? element : ForwardingPath(element).Peek();
        if (!module.ExportedTypes.Any(export => export.IsForwarder && export.FullName == outer.FullName))
            return assembly.FullName;
        return element.Resolve()?.Module.Assembly.Name.FullName ??
            throw new InvalidDataException("Unresolved forwarded type: " + element.FullName);
    }

    internal static string Identity(TypeReference type)
    {
        if (type is GenericInstanceType generic && (ValueTuples.Is(type) || GenericStructs.Is(type)))
            return ScopedArguments(generic);
        return Scope(type) + "::" + type.FullName;
    }

    // Same-assembly generic interfaces spell scoped arguments, as Lean closes interface constraints.
    internal static string InterfaceIdentity(TypeReference type) =>
        type is GenericInstanceType generic && generic.ElementType.Scope is ModuleDefinition
            ? ScopedArguments(generic) : Identity(type);

    static string ScopedArguments(GenericInstanceType generic) =>
        Identity(generic.ElementType) + "<" + string.Join(",", generic.GenericArguments.Select(argument =>
            MetadataValidation.IsAggregate(argument, generic.Module)
                ? Identity(argument) : ArgumentText(argument))) + ">";

    static string ArgumentText(TypeReference type) => type switch
    {
        GenericParameter parameter => $"{parameter.Type}:{parameter.Position}",
        ByReferenceType reference => ArgumentText(reference.ElementType) + "&",
        RequiredModifierType modifier when InReferences.Is(modifier) => ArgumentText(modifier.ElementType) + " in",
        RequiredModifierType modifier when InitAccessors.Is(modifier) => ArgumentText(modifier.ElementType) + " init",
        PointerType pointer => ArgumentText(pointer.ElementType) + "*",
        ArrayType { IsVector: true } array => ArgumentText(array.ElementType) + "[]",
        GenericInstanceType instance => Identity(instance.ElementType) + "<" +
            string.Join(",", instance.GenericArguments.Select(ArgumentText)) + ">",
        FunctionPointerType pointer => $"fn:{pointer.CallingConvention}:{pointer.HasThis}:{pointer.ExplicitThis}:" +
            ArgumentText(pointer.ReturnType) + "(" +
            string.Join(",", pointer.Parameters.Select(parameter => ArgumentText(parameter.ParameterType))) + ")",
        _ => Identity(type)
    };

    internal MetadataValidation.LayoutContext Metadata => layouts;

    internal string[] Identities => rawTypes.Select(Identity).ToArray();

    internal int Index(TypeReference type) => typeIndices.Count != 0 && type.GetElementType().MetadataToken.RID != 0
        ? typeIndices.GetValueOrDefault(layouts.Signature(type), -1) : -1;

    static string Declaration(TypeReference head)
    {
        var image = PinnedAssemblies.Active!.IdentityMetadata(head.Module);
        return "[" + string.Join(", ", TypeLevel.Levels(head, image).Select(level => level.ToLean())) + "]";
    }

    // Named signature occurrences and primitive element codes have distinct storage identities.
    static string LayoutArgument(TypeReference type)
    {
        if (StructuralSignatures.Current.IsPrimitiveElement(type)) return $".primitive {(int)type.MetadataType}";
        var head = type is GenericInstanceType generic ? generic.ElementType : type;
        var name = $"{IdentityText.Quote(Scope(head))} {Declaration(head)}";
        return type is GenericInstanceType instance
            ? $".instanceType {name} {LayoutArguments(instance)}" : $".named {name}";
    }

    static string LayoutArguments(GenericInstanceType instance)
    {
        var chain = new StringBuilder();
        foreach (var argument in instance.GenericArguments)
            chain.Append($"(.cons ({LayoutArgument(argument)}) ");
        return chain.Append(".nil").Append(')', instance.GenericArguments.Count).ToString();
    }

    // Layouts in one assembly share the UTF-8 encoding of its scope during kernel reduction.
    static string ScopedIdentityTerm(string identity, int boundary)
    {
        var scope = IdentityText.Quote(identity[..boundary]);
        var name = IdentityText.Quote(identity[boundary..]);
        return $"({scope} ++ {name})";
    }

    internal string IdentityTerm(int index) => identityTerms[index];

    /// <summary>The same operand type with a shared byte-backed name for a closed generic layout.</summary>
    internal string NamedOperandType(string term) => namedOperandTypes.GetValueOrDefault(term, term);

    internal string RawFieldType(TypeReference type, ModuleDefinition module)
    {
        if (MetadataValidation.IsAggregate(type, module) || layouts.IsImported(type))
        {
            var index = Index(type);
            if (index < 0) throw new InvalidDataException("Missing raw aggregate metadata: " + type.FullName);
            return $".aggregate {index}";
        }
        if (MetadataValidation.VectorFieldWidth(type) is int width) return $"(.vector{width * 8} {VectorLane(type)})";
        return EnumTypes.Storage(type).FullName switch
        {
            "System.SByte" => ".signed8", "System.Byte" => ".unsigned8", "System.Boolean" => ".boolean",
            "System.Int16" => ".signed16", "System.UInt16" => ".unsigned16", "System.Char" => ".character",
            "System.Int32" => ".signed32", "System.UInt32" => ".unsigned32",
            "System.Int64" => ".signed64", "System.UInt64" => ".unsigned64",
            "System.IntPtr" => ".nativeInt", "System.UIntPtr" => ".nativeUInt",
            _ => throw new InvalidDataException("Unsupported raw layout field: " + type.FullName)
        };
    }

    // A vector field's lane is its element's field kind; VectorFieldWidth admits only these elements.
    static string VectorLane(TypeReference vector) => ((GenericInstanceType)vector).GenericArguments[0].FullName switch
    {
        "System.Byte" => ".unsigned8", "System.Int32" => ".signed32", "System.UInt32" => ".unsigned32",
        "System.Int64" => ".signed64", "System.UInt64" => ".unsigned64",
        _ => throw new InvalidDataException($"Unsupported vector field lane: {vector.FullName}")
    };

    internal void EmitLayouts(StringBuilder lean, StringBuilder? decoderInputs = null)
    {
        var start = lean.Length;
        var rowIdentities = (string[])identityTerms.Clone();
        for (var index = 0; index < rawTypes.Length; index++)
        {
            if (rawTypes[index] is not GenericInstanceType) continue;
            var identity = Identity(rawTypes[index]);
            var name = $"layoutIdentity{index}";
            var bytes = ByteLiterals.Of(IdentityText.Utf8(identity));
            var spelling = IdentityText.Quote(identity);
            lean.AppendLine($"def {name} : String := Extraction.byteString {bytes} {spelling} (by cil_kernel_rfl)");
            rowIdentities[index] = name;
            // Field resolution compares the owner's and held type's bytes with the bytes in the layout row.
            namedOperandTypes[$".aggregate {identityTerms[index]} {index}"] = $".aggregate {name} {index}";
        }
        lean.AppendLine("def rawLayouts : List Extraction.RawLayout := [");
        lean.AppendLine(string.Join(",\n", rawTypes.Select((type, index) =>
        {
            var metadata = ValueTuples.Is(type) ? ((GenericInstanceType)type).ElementType.Resolve() : type.Resolve();
            var genericEvidence = "";
            if (GenericStructs.Is(type) && type is GenericInstanceType closed)
            {
                var serializer = new GenericEvidence(null, this);
                var owner = $".constructor {IdentityText.Quote(Scope(type))} {GenericEvidence.ClassName(metadata)}";
                var arguments = string.Join(", ", closed.GenericArguments.Select(serializer.Type));
                var parameters = $"arity := {metadata.GenericParameters.Count}, arguments := [{arguments}]";
                var openFields = string.Join(", ", metadata.Fields.Where(field => !field.IsStatic)
                    .Select(field => serializer.Type(field.FieldType)));
                var constraints = metadata.GenericParameters.Select(parameter =>
                {
                    var names = parameter.Constraints.Select(constraint =>
                        IdentityText.Quote(GenericEvidence.ConstraintType(constraint.ConstraintType)));
                    return $"({(uint)parameter.Attributes}, [{string.Join(", ", names)}])";
                });
                var members = $"fields := [{openFields}], constraints := [{string.Join(", ", constraints)}]";
                genericEvidence = $$"""generic := some { owner := {{owner}}, {{parameters}}, {{members}} }, """;
            }
            var fields = layouts.Fields(type).Select(field =>
                $"{{ type := {RawFieldType(field.Type, type.Module)}, offset := {(field.Definition.Offset < 0 ? "none" : $"some {field.Definition.Offset}")} }}");
            var kind = $"explicit := {metadata.IsExplicitLayout.ToString().ToLowerInvariant()}, ";
            var auto = metadata.IsAutoLayout ? "auto := true, " : "";
            var marker = MetadataValidation.IsByRefLike(type) ? "byRefLike := true, " : "";
            // An imported entry repeats its published layout, which carries no interfaces.
            var interfaces = layouts.IsImported(type) ? "" : $"interfaces := [{string.Join(", ",
                metadata.Interfaces.Select(implementation => IdentityText.Quote(InterfaceIdentity(
                    GenericStructs.Substitute(implementation.InterfaceType, type as GenericInstanceType)))))}], ";
            var head = type is GenericInstanceType constructed ? constructed.ElementType : metadata;
            var declaration = $"declaration := {Declaration(head)}, ";
            if (type is GenericInstanceType instance)
                declaration += $"genericArguments := some {LayoutArguments(instance)}, ";
            var attributes = $"{declaration}{genericEvidence}{kind}{auto}{marker}{interfaces}";
            var size = $"packing := {metadata.PackingSize}, declaredSize := {metadata.ClassSize}";
            var fieldList = string.Join(", ", fields);
            var identity = rowIdentities[index];
            return $$"""  { identity := {{identity}}, {{attributes}}{{size}}, fields := [{{fieldList}}] }""";
        })));
        lean.AppendLine("]");
        lean.AppendLine("def computedLayouts : Array Extraction.ComputedLayout := #[" +
            string.Join(", ", rawTypes.Select(type =>
            {
                var index = emittedIndices[layouts.Signature(type)];
                var alignment = layouts.AggregateLayout(type).Alignment;
                return $"⟨layout{index}, {alignment}⟩";
            })) + "]");
        decoderInputs?.Append(lean, start, lean.Length - start);
        lean.AppendLine("theorem layouts_validated : Extraction.LayoutsValid rawLayouts computedLayouts " +
            $".{Architecture} := " + LeanEmitter.Decide);
    }

    internal void EmitMethod(StringBuilder lean, MethodDefinition method, int number, HashSet<Instruction> reachable,
        int[] parameterIndices)
    {
        var uses = new List<string>();
        for (int pc = 0; pc < method.Body.Instructions.Count; pc++)
        {
            var instruction = method.Body.Instructions[pc];
            if (!reachable.Contains(instruction)) continue;
            if (instruction.OpCode.Code == Code.Newobj && instruction.Operand is MethodReference constructor &&
                MetadataValidation.IsAggregate(constructor.DeclaringType, method.Module))
                uses.Add($".size {pc} {Index(constructor is MethodDefinition closedConstructor
                    ? MethodSpecialization.DeclaringType(closedConstructor) : constructor.DeclaringType)}");
        }
        foreach (var local in method.Body.Variables)
            if (layouts.IsLayout(local.VariableType))
                uses.Add($".local {local.Index} {Index(local.VariableType)}");
        for (int home = 0; home < parameterIndices.Length; home++)
        {
            var type = MethodArguments.Type(method, parameterIndices[home]);
            if (MetadataValidation.IsAggregate(type, method.Module)) uses.Add($".parameter {home} {Index(type)}");
        }
        lean.AppendLine($"def method{number}LayoutUses : List Extraction.LayoutUse := [{string.Join(", ", uses)}]");
    }
}
