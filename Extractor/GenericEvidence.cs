using System.Buffers.Binary;
using System.Collections.Frozen;
using System.Globalization;
using System.Reflection.Metadata.Ecma335;
using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Read original definitions from a separate, untouched module over the same assembly
// bytes. The call-graph walk rewrites call operands in the working module.
internal sealed class GenericEvidence(PinnedAssemblies? pinned, LayoutEvidence layouts,
    ImportResolution? imports = null)
{
    // Closed instantiations share their definition's bytes; the first method to use a body names them.
    readonly ExternalIdentityEvidence externalIdentities = new();
    readonly MetadataSlices? metadata = pinned is null ? null : new(pinned);
    readonly Dictionary<MethodReference, string> declaredSignatures = new();
    int methodParameterCount;
    // Closed type operands are shared by the decoder, template descriptors and proof outlines.
    readonly Dictionary<Instruction, string> closedTypes = [];

    // Type serialization needs no method bodies; only method and dispatch evidence read originals.
    PinnedAssemblies Pinned => pinned ??
        throw new InvalidOperationException("Method evidence requires the pinned assemblies.");

    ModuleDefinition Original(ModuleDefinition module) => Pinned.Original(module);

    /// <summary>The Lean string literal of <paramref name="value"/>.</summary>
    internal static string Quote(string value) => IdentityText.Quote(value);
    static string Bool(bool value) => value.ToString().ToLowerInvariant();
    static string List(IEnumerable<string> entries) => "[" + string.Join(", ", entries) + "]";

    /// <summary>The Lean term of a type's assembly scope; a platform scope is the named string the decoder
    /// writes, so evidence and a decoded method spell the same scope with the same term.</summary>
    internal static string Scope(TypeReference type) => Scope(LayoutEvidence.Scope(type));

    /// <summary>The platform assembly scopes the Lean library names, with the term of each.</summary>
    static readonly (string Assembly, string Term)[] NamedScopes =
    [
        (TypeTests.RuntimeScope, "Extraction.runtimeScope"),
        (PlatformAssemblies.SystemRuntimeIntrinsics.ToDisplay(), "Extraction.intrinsicsScope"),
        (PlatformAssemblies.SystemMemory.ToDisplay(), "Extraction.spanMemoryScope"),
    ];

    static string Scope(string assembly) =>
        NamedScopes.FirstOrDefault(scope => scope.Assembly == assembly).Term ?? Quote(assembly);

    internal string Type(TypeReference type) => Type(type, false);

    /// <summary>The type expression naming a class instance type, as field operations carry it.</summary>
    internal static string ObjectType(TypeReference type) => ObjectType(LayoutEvidence.Scope(type), type.FullName);

    /// <summary>The type expression naming the class <paramref name="name"/> of the assembly
    /// <paramref name="assembly"/>.</summary>
    internal static string ObjectType(string assembly, string name) => $".object {Scope(assembly)} {Quote(name)}";

    // The kernel sees an `in` reference as the reference it is; the extractor compares the modifier exactly.
    string Parameter(TypeReference type) => Type(InReferences.Parameter(type));

    // The kernel sees an `init` accessor as the void method it is; its signature string keeps the modifier.
    static TypeReference Returned(MethodReference reference) =>
        InitAccessors.Return(CallReturnType.Resolve(reference));

    string Type(TypeReference type, bool preserveGeneric, bool declared = false)
        => RenderType(type, preserveGeneric, declared, methodParameterCount, layouts);

    // Callable identities name closed aggregates independently of any extraction's layout-table order.
    internal static string CallableArgument(TypeReference type) => RenderType(type, false, false, 0, null);

    static string RenderType(TypeReference type, bool preserveGeneric, bool declared, int methodParameterCount,
        LayoutEvidence? layouts)
    {
        string Nested(TypeReference element) => RenderType(element, false, declared, methodParameterCount, layouts);
        string? Aggregate(bool localOnly = false)
        {
            if (layouts is null)
                return MetadataValidation.IsAggregate(type, type.Module)
                    ? $".aggregate {Quote(LayoutEvidence.Identity(type))} 0" : null;
            var index = layouts.Index(type);
            return index >= 0 && (!localOnly || !layouts.Metadata.IsImported(type))
                ? $".aggregate {layouts.IdentityTerm(index)} {index}" : null;
        }
        if (declared && type is IModifierType modifier)
        {
            var required = Bool(type is RequiredModifierType);
            var name = Quote(modifier.ModifierType.FullName);
            return $".modified {required} {Scope(modifier.ModifierType)} {name} ({Nested(modifier.ElementType)})";
        }
        if (type is FunctionPointerType callable)
        {
            var parameters = ".void";
            foreach (var argument in callable.Parameters.Reverse())
                parameters = $".signatureParameter ({Nested(argument.ParameterType)}) ({parameters})";
            return $"""
                .functionPointer ({Nested(callable.ReturnType)}) ({parameters})
                {(int)callable.CallingConvention} {Bool(callable.HasThis)} {Bool(callable.ExplicitThis)}
                """.ReplaceLineEndings(" ");
        }
        if (type is GenericParameter parameter)
        {
            var ownerParameter = parameter.Type == GenericParameterType.Type;
            if (declared && ownerParameter) return $".ownerParameter {parameter.Position}";
            var offset = ownerParameter ? methodParameterCount : 0;
            return $".parameter {parameter.Position + offset}";
        }
        if (type is ByReferenceType byRef) return $".byref ({Nested(byRef.ElementType)})";
        // An element class outside the model is named as an object, as the array's reference slots hold it.
        if (type is ArrayType { IsVector: true } array)
        {
            var element = ReferenceArrays.Is(array) ? ObjectType(array.ElementType) : Nested(array.ElementType);
            return $".array ({element})";
        }
        if (type is PointerType pointer) return $".pointer ({Nested(pointer.ElementType)})";
        if (ValueTuples.Is(type) && Aggregate() is { } tuple) return tuple;
        if (type is GenericInstanceType generic)
        {
            if (!preserveGeneric && GenericStructs.Is(type) && Aggregate() is { } aggregate) return aggregate;
            var result = $"{Head(generic)} {Scope(generic.ElementType)} {Quote(generic.ElementType.FullName)}";
            foreach (var argument in generic.GenericArguments) result = $".apply ({result}) ({Nested(argument)})";
            return result;
        }
        if (type.FullName == "System.Void") return ".void";
        if (EnumTypes.IsEnum(type))
        {
            var underlying = type.Resolve().Fields.Single(field => !field.IsStatic).FieldType;
            return $".enum {Quote(LayoutEvidence.Identity(type))} ({Nested(underlying)})";
        }
        if (ObjectTypes.Reference(type)) return ObjectType(type);
        return Aggregate(localOnly: true) ?? $".atom {Scope(type)} {Quote(type.FullName)}";
    }

    // The head says whether the instances are values or references, as the signature's marker does.
    static string Head(GenericInstanceType generic) =>
        generic.ElementType.IsValueType ? ".constructor" : ".objectConstructor";

    // Signatures name an imported layout by scoped atom, as the import boundary requires; only a
    // local declaration binds it to the table entry that sizes its storage.
    string LocalType(TypeReference type)
    {
        if (!layouts.Metadata.IsImported(type)) return Type(type);
        int index = layouts.Index(type);
        if (index < 0) throw new InvalidDataException($"Missing imported layout for {type.FullName}");
        return $".aggregate {layouts.IdentityTerm(index)} {index}";
    }

    // The member in the untouched body retains its blob even when the call graph specializes its operand.
    string DeclaredSignature(MethodReference original)
    {
        var member = original.GetElementMethod();
        if (declaredSignatures.TryGetValue(member, out var signature)) return signature;
        var convention = (byte)member.CallingConvention |
            (member.HasThis ? 0x20 : 0) | (member.ExplicitThis ? 0x40 : 0);
        string DeclaredType(TypeReference type) => Type(type, true, true);
        signature = $$"""
            { convention := {{convention}}, returnType := {{DeclaredType(member.ReturnType)}},
            parameters := {{List(member.Parameters.Select(parameter => DeclaredType(parameter.ParameterType)))}} }
            """.ReplaceLineEndings(" ");
        declaredSignatures.Add(member, signature);
        return signature;
    }

    string Call(MethodReference reference, MethodReference original, Instruction instruction,
        IReadOnlySet<Instruction> reachable)
    {
        var (method, name, owners, extracted, typeArguments) = MethodOperand(reference);
        var definition = reference is GenericInstanceMethod generic ? generic.ElementMethod : reference;
        var resolved = extracted ? definition.Resolve() : null;
        var slot = InstructionPrefixes.IsStaticVirtualSlot(resolved) ? "staticVirtualInterfaceSlot := true, " : "";
        var target = extracted
            ? $".managed {resolved!.MetadataToken.ToUInt32()}"
            : ".external " + externalIdentities.Reference(imports?.Identity(instruction) ??
                (LayoutEvidence.Scope(definition.DeclaringType) + "::" + ExternalSignature(definition)),
                reachable.Contains(instruction));
        return $$"""
            { method := {{method.ToLean()}}, name := {{Quote(name)}}, target := {{target}},
            typeArguments := {{typeArguments}}, ownerArgumentCount := {{owners}},
            {{slot}}parameterCount := {{reference.Parameters.Count}},
            returnsValue := {{Bool(Returned(reference).FullName != "System.Void")}},
            declared := {{DeclaredSignature(original)}} }
            """.ReplaceLineEndings(" ");
    }

    /// <summary>
    /// The typed method a call operand names, its name as text, the number of its owner's type arguments, whether its
    /// callee is extracted, and the Lean list of its type arguments, method arguments first.
    /// </summary>
    (MethodRef Method, string Name, int Owners, bool Extracted, string TypeArguments) MethodOperand(
        MethodReference reference)
    {
        var definition = reference is GenericInstanceMethod generic ? generic.ElementMethod : reference;
        var arguments = reference is GenericInstanceMethod instance ? instance.GenericArguments.ToArray() :
            reference is MethodDefinition specialized ? MethodSpecialization.Arguments(specialized).ToArray() : [];
        // A pinned referenced callee is extracted like a same-assembly one, so its call is managed.
        var extracted = definition.DeclaringType.Scope is ModuleDefinition ||
            PinnedAssemblies.Active?.ModuleOf(definition.DeclaringType) is not null;
        var owners = !extracted ? [] :
            reference.DeclaringType is GenericInstanceType owner
            ? owner.GenericArguments.ToArray() : reference is MethodDefinition closed
                ? MethodSpecialization.OwnerArguments(closed).ToArray() : [];
        if (reference is not MethodDefinition) arguments = [.. arguments, .. owners];
        TypeReference declaringType = definition.DeclaringType;
        if (reference is MethodDefinition && owners.Length != 0)
        {
            var closedOwner = new GenericInstanceType(declaringType);
            foreach (var argument in owners) closedOwner.GenericArguments.Add(argument);
            declaringType = closedOwner;
        }
        var name = extracted
            ? ((MethodDefinition)Original(definition.Resolve().Module)
                .LookupToken(definition.Resolve().MetadataToken)).Name : definition.Name;
        var genericArity = (reference is MethodDefinition own ? MethodSpecialization.Definition(own) : definition)
            .GenericParameters.Count;
        // Types render in the order they always have, since rendering a type can number its layout.
        var ownerType = Type(declaringType, true);
        var typeArguments = List(arguments.Select(Type));
        var returnType = Type(Returned(reference));
        ValueList<string> parameters = [.. CallReturnType.Parameters(reference).Select(Parameter)];
        ValueList<string> methodArguments = [.. arguments[..^owners.Length].Select(Type)];
        return (new(ownerType, MetadataName.OfText(name), reference.HasThis, genericArity, returnType, parameters,
            methodArguments), name, owners.Length, extracted, typeArguments);
    }

    /// <summary>
    /// The typed constructor or method the call operand at <paramref name="pc"/> in <paramref name="method"/> names,
    /// as its raw operand states it; the executed instruction must carry the same reference.
    /// </summary>
    internal MethodRef MethodReferenceOf(MethodDefinition method, int pc)
    {
        methodParameterCount = method.GenericParameters.Count;
        return MethodOperand((MethodReference)method.Body.Instructions[pc].Operand).Method;
    }

    // An open owner spells caller parameters by position, so the certificate can instantiate it;
    // closed owners keep Cecil's spelling byte for byte.
    static string ExternalSignature(MethodReference definition)
    {
        var owner = definition.DeclaringType;
        if (!owner.ContainsGenericParameter) return definition.FullName;
        var named = definition.ReturnType.FullName + " " + owner.FullName + "::";
        if (!definition.FullName.StartsWith(named, StringComparison.Ordinal))
            throw new InvalidDataException("Unexpected external call signature: " + definition.FullName);
        return definition.ReturnType.FullName + " " + OwnerSpelling(owner) + "::" +
            definition.FullName[named.Length..];
    }

    // Matches the certificate's owner spelling: `!!n` method and `!n` declaring-type parameters.
    static string OwnerSpelling(TypeReference type) => type switch
    {
        GenericParameter parameter => (parameter.Type == GenericParameterType.Method ? "!!" : "!") +
            parameter.Position.ToString(CultureInfo.InvariantCulture),
        GenericInstanceType generic => generic.ElementType.FullName + "<" +
            string.Join(",", generic.GenericArguments.Select(OwnerSpelling)) + ">",
        _ => type.FullName
    };

    /// <summary>
    /// The declaring type, model index, held type and static flag of a field operand, which the raw operand and the
    /// typed field reference both state.
    /// </summary>
    (string Owner, int Index, string Held, bool IsStatic) FieldOperand(Instruction instruction, FieldReference field)
    {
        var isStatic = instruction.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda or Code.Ldtoken;
        var index = 0;
        // A field signature's `!n` is the declaring type's parameter: the declaring instance's argument.
        var fieldType = field.FieldType.ContainsGenericParameter &&
            field.DeclaringType is GenericInstanceType instance
            ? GenericStructs.Substitute((field.Resolve() ?? throw new InvalidDataException(
                "Unresolved generic field: " + field.FullName)).FieldType, instance) : field.FieldType;
        if (Carried(field))
        {
            var resolved = field.Resolve();
            index = layouts.Metadata.FieldIndex(field.DeclaringType, resolved, isStatic);
            if (!isStatic) fieldType = layouts.Metadata.Fields(field.DeclaringType)[index].Type;
            // A class field's index counts its bases' fields first, as its model slot does.
            if (!isStatic && ObjectTypes.Is(field.DeclaringType))
                index = ObjectTypes.FieldIndex(field.DeclaringType, resolved);
        }
        else if (!isStatic && ValueTuples.Is(field.DeclaringType))
        {
            // Tuple fields are typed by the instance's arguments, not the definition's T1/T2.
            var fields = layouts.Metadata.Fields(field.DeclaringType);
            index = layouts.Metadata.FieldIndex(field.DeclaringType, field.Resolve());
            if (index < 0) throw new InvalidDataException("Unresolved tuple field: " + field.FullName);
            fieldType = fields[index].Type;
        }
        // Lean refuses such an operand at every pc, reachable or not, so the access is a stated blocker.
        else if (!(instruction.OpCode.Code == Code.Ldsfld && FeatureProfile.PlatformField(field) is not null))
            throw new InvalidDataException(
                $"IL_{instruction.Offset:x4}: Unsupported field access: {field.FullName}\n" +
                "  Its owner has no carried definition, so no metadata row gives the field's position.");
        // A class field of a type outside the model holds an object reference like an admitted one.
        var heldType = !isStatic && ObjectTypes.Is(field.DeclaringType) && ObjectTypes.Opaque(fieldType) &&
            fieldType is not GenericInstanceType ? ObjectType(fieldType) : Type(fieldType);
        return (Type(field.DeclaringType), index, heldType, isStatic);
    }

    // A carried slice defines the field: its owner is in the method's module or a pinned assembly.
    static bool Carried(FieldReference field) => field.DeclaringType.Scope is ModuleDefinition ||
        PinnedAssemblies.Active?.ModuleOf(field.DeclaringType) is not null;

    // The static accesses whose field a carried row defines, which the Lean decoder records by instruction index.
    static bool BoundStatic(Instruction instruction) =>
        instruction.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda or Code.Ldtoken &&
        instruction.Operand is FieldReference field && Carried(field);

    /// <summary>
    /// The typed reference of the field operand at <paramref name="pc"/> in <paramref name="method"/>, the owner,
    /// index and held type its raw operand states and the name of the row the original body's token names.
    /// </summary>
    internal FieldRef FieldReferenceOf(MethodDefinition method, int pc)
    {
        methodParameterCount = method.GenericParameters.Count;
        var instruction = method.Body.Instructions[pc];
        var (owner, index, held, _) = FieldOperand(instruction, (FieldReference)instruction.Operand);
        return new(owner, index, held, FieldName(method, pc));
    }

    /// <summary>
    /// The name of the Field or MemberRef row the field operand at <paramref name="pc"/> names in the image of
    /// <paramref name="method"/>'s definition; the metadata check spells the operand's name against it.
    /// </summary>
    MetadataName FieldName(MethodDefinition method, int pc)
    {
        // A specialization's operands are references without a token; its definition's body holds the token.
        var original = (MethodDefinition)Original(method.Module).LookupToken(method.MetadataToken);
        var field = (FieldReference)original.Body.Instructions[pc].Operand;
        var image = Pinned.Metadata(original.Module);
        var token = field.MetadataToken;
        if (token.RID == 0)
            throw new InvalidDataException("Field operand without a metadata row: " + field.FullName);
        return token.TokenType switch
        {
            TokenType.Field => IdentityRows.Name(image,
                image.Reader.GetFieldDefinition(MetadataTokens.FieldDefinitionHandle((int)token.RID)).Name),
            TokenType.MemberRef => IdentityRows.Name(image,
                image.Reader.GetMemberReference(MetadataTokens.MemberReferenceHandle((int)token.RID)).Name),
            _ => throw new InvalidDataException("Field operand without a Field or MemberRef row: " + field.FullName)
        };
    }

    // An element class outside the model is named as an object, as the array's reference slots hold it.
    string ArrayElement(TypeReference type) => ReferenceArrays.Element(type) ? ObjectType(type) : Type(type);

    string Operand(MethodDefinition method, InstructionIndex instructions, Instruction instruction,
        Instruction original, Instruction admittedInstruction, IReadOnlySet<Instruction> reachable,
        Dictionary<Instruction, string>? typeOperands = null)
    {
        switch (instruction.Operand)
        {
            case null: return ".none";
            case Instruction target: return $".target {instructions.Position(target)}";
            case Instruction[] targets:
                return $".targets {List(targets.Select(target =>
                    instructions.Position(target).ToString(CultureInfo.InvariantCulture)))}";
            case ParameterDefinition parameter:
                var argument = parameter.Index < 0 && method.HasThis ? 0 : parameter.Index + (method.HasThis ? 1 : 0);
                if (argument < 0) throw new InvalidDataException("Invalid raw argument index");
                return $".argument {argument}";
            case VariableDefinition local: return $".local {local.Index}";
            case TypeReference type:
                var term = instruction.OpCode.Code == Code.Newarr ? ArrayElement(type) : Type(type);
                typeOperands?.Add(admittedInstruction, term);
                return $".type ({term})";
            case MethodReference callee:
                return $".call {Call(callee, (MethodReference)original.Operand, admittedInstruction, reachable)}";
            case Mono.Cecil.CallSite site when instruction.OpCode.Code == Code.Calli:
                return $".indirectCall ({Type(site.ReturnType)}) "+
                    $"{List(site.Parameters.Select(parameter => Type(parameter.ParameterType)))} "+
                    $"{Bool(site.HasThis)} {Bool(site.ExplicitThis)} {(int)site.CallingConvention}";
            case FieldReference field:
                var (owner, index, held, isStatic) = FieldOperand(instruction, field);
                var name = FieldName(method, instructions.Position(instruction)).ToLean();
                return $".field ({owner}) {index} ({held}) {name} {Bool(isStatic)}";
            case string text: return $".text {Quote(text)}";
            case float number: return $".text {Quote("float:" + BitConverter.SingleToInt32Bits(number).ToString(CultureInfo.InvariantCulture))}";
            case double number: return $".text {Quote("double:" + BitConverter.DoubleToInt64Bits(number).ToString(CultureInfo.InvariantCulture))}";
            case sbyte or byte or short or ushort or int or uint or long or ulong:
                return $".integer ({Convert.ToString(instruction.Operand, CultureInfo.InvariantCulture)})";
            default: throw new InvalidDataException("Unsupported raw CIL operand: " + instruction.Operand.GetType().Name);
        }
    }

    /// <summary>
    /// The type term of the type operand of <paramref name="instruction"/>, as the last method's
    /// <c>method{n}Closed</c> states it; the emitted instruction must carry the same term.
    /// </summary>
    internal string ClosedOperandOf(Instruction instruction) =>
        closedTypes.TryGetValue(instruction, out var term) ? term
            : throw new InvalidDataException("No closed operand term for the instruction at " + instruction.Offset);

    internal static string ConstraintType(TypeReference type) => type is RequiredModifierType modifier
        ? LayoutEvidence.Identity(modifier.ModifierType) + "!" + LayoutEvidence.Identity(modifier.ElementType)
        : LayoutEvidence.InterfaceIdentity(type);

    static readonly string ValueTypeConstraint = TypeTests.RuntimeScope + "::System.ValueType";
    static readonly string UnmanagedTypeConstraint = TypeTests.RuntimeScope +
        "::System.Runtime.InteropServices.UnmanagedType!" + ValueTypeConstraint;

    static string Constraint(TypeReference type)
    {
        var identity = ConstraintType(type);
        return identity == ValueTypeConstraint ? "Extraction.valueTypeConstraint" :
            identity == UnmanagedTypeConstraint ? "Extraction.unmanagedTypeConstraint" : Quote(identity);
    }

    // A constraint naming generic parameters, such as `T : I<T>`, is closed per instantiation in Lean.
    string ParameterConstraint(GenericParameter parameter)
    {
        var types = parameter.Constraints.Select(constraint => constraint.ConstraintType).ToArray();
        var open = types.Where(type => type.ContainsGenericParameter).Select(Type).ToArray();
        return $"{{ flags := {(uint)parameter.Attributes}, " +
            $"types := {List(types.Where(type => !type.ContainsGenericParameter).Select(Constraint))}" +
            (open.Length == 0 ? "" : $", interfaces := {List(open)}") + " }";
    }

    string Locals(MethodDefinition method) =>
        List(method.Body.Variables.Select(local => LocalType(local.VariableType)));

    string Method(MethodDefinition method, MethodDefinition original, MethodDefinition admitted,
        IReadOnlySet<Instruction> reachable, string staticInput, Dictionary<Instruction, string>? typeOperands = null)
    {
        methodParameterCount = method.GenericParameters.Count;
        var instructions = new InstructionIndex(method);
        var constraints = method.GenericParameters.Select(ParameterConstraint).ToArray();
        var ownerConstraints = MethodSpecialization.Source(method) is null
            ? method.DeclaringType.GenericParameters.Select(ParameterConstraint).ToArray() : [];
        if (method.MetadataToken.ToUInt32() != admitted.MetadataToken.ToUInt32() ||
            method.Body.Instructions.Count != admitted.Body.Instructions.Count)
            throw new InvalidDataException("Specialization instruction mapping differs from the original method.");
        IEnumerable<string> code = method.Body.Instructions.Select((instruction, index) =>
        {
            var selected = admitted.Body.Instructions[index];
            if (instruction.Offset != selected.Offset || instruction.OpCode.Value != selected.OpCode.Value)
                throw new InvalidDataException("Specialization instruction mapping changed an offset or opcode.");
            var operand = Operand(method, instructions, instruction, original.Body.Instructions[index],
                selected, reachable, typeOperands);
            return $"{{ offset := {instruction.Offset}, opcode := {Unadmitted.RawOpcode(instruction)}, " +
                $"operand := {operand} }}";
        });
        var owner = Quote(LayoutEvidence.Identity(method.DeclaringType));
        var classOwner = ObjectReceiver(method);
        var objectReceiver = Bool(classOwner);
        var objectFields = classOwner ? ObjectTypes.Fields(method.DeclaringType).Length : 0;
        var objectBases = classOwner ? ObjectTypes.BaseList(method.DeclaringType) : "[]";
        var (parameters, returnType) = SignatureTypes(method);
        var locals = Locals(method);
        // Lines break only after a comma, so the emitted definition stays on one line.
        return $$"""
            { token := {{method.MetadataToken.ToUInt32()}}, owner := {{owner}},
            ownerParameters := {{List(ownerConstraints)}},
            ownerArgumentCount := {{MethodSpecialization.OwnerArguments(method).Count}},
            objectReceiver := {{objectReceiver}}, objectFieldCount := {{objectFields}},
            objectBases := {{objectBases}},
            hasThis := {{Bool(method.HasThis)}},
            explicitThis := {{Bool(method.ExplicitThis)}}, callingConvention := {{(byte)method.CallingConvention}},
            attributes := {{(uint)method.Attributes}}, implementation := {{(uint)method.ImplAttributes}},
            returnType := {{returnType}}, parameters := {{parameters}},
            locals := {{locals}}, initLocals := {{Bool(method.Body.InitLocals)}},
            maxStack := {{method.Body.MaxStackSize}}, genericParameters := {{List(constraints)}},
            {{staticInput}}code := {{List(code)}} }
            """.ReplaceLineEndings(" ");
    }

    static bool ObjectReceiver(MethodDefinition method) =>
        method.HasThis && ObjectTypes.Is(method.DeclaringType);

    // The generic context is set here, so a type-level parameter is numbered by this method, not the last one.
    (string Parameters, string ReturnType) SignatureTypes(MethodDefinition method)
    {
        methodParameterCount = method.GenericParameters.Count;
        return (List(method.Parameters.Select(parameter => Parameter(parameter.ParameterType))),
            Type(InitAccessors.Return(method.ReturnType)));
    }

    /// <summary>
    /// The method's DeclaredSignature: the receiver kind, types and localsinit flag of method{n}Closed. Fields at
    /// their default are omitted.
    /// </summary>
    internal string Declared(MethodDefinition method)
    {
        var receiver = method.HasThis
            ? $"receiver := some .{(ObjectReceiver(method) ? "object" : "reference")}, " : "";
        var (parameters, returnType) = SignatureTypes(method);
        var initLocals = method.Body.InitLocals ? "" : ", initLocals := false";
        return $"{{ {receiver}parameters := {parameters}, returnType := {returnType}{initLocals} }}";
    }

    internal void EmitMethod(StringBuilder lean, MethodDefinition method, int number,
        IReadOnlySet<Instruction> reachable, string staticInput, StringBuilder? decoderInputs = null)
    {
        var original = (MethodDefinition)Original(method.Module).LookupToken(method.MetadataToken);
        var originalEvidence = Method(original, original, method, reachable, staticInput);
        // Token operands are spelled in the original's generic context, as its code is.
        var body = Body(original, method, reachable, number);
        closedTypes.Clear();
        var closedEvidence = Method(method, original, method, reachable, staticInput, closedTypes);
        externalIdentities.Emit(lean, decoderInputs);
        lean.AppendLine($"def method{number}Original : Extraction.RawMethod := {originalEvidence}");
        lean.AppendLine(body.Bytes);
        if (body.Slices.Length > 0)
            foreach (var line in body.Slices.Split('\n')) lean.AppendLine(line);
        lean.AppendLine(body.Definition);
        lean.AppendLine($"def method{number}TypeArgumentsRaw : List Extraction.TypeExpr := {List(MethodSpecialization.Arguments(method).Select(Type))}");
        var closed = $"def method{number}Closed : Extraction.RawMethod := {closedEvidence}";
        lean.AppendLine(closed);
        decoderInputs?.AppendLine(closed);
        lean.AppendLine($"def method{number}DispatchTypes : List Extraction.DispatchType := {DispatchTypes(method)}");
        // Direct equality proofs avoid a separate structural decision over the raw metadata.
        lean.AppendLine($"theorem method{number}_specialization_validated :" +
            $" Extraction.SpecializationValid rawLayouts method{number}Original method{number}TypeArgumentsRaw" +
            $" method{number}Closed method{number}RawArguments := by constructor <;> rfl");
        lean.AppendLine($"theorem method{number}_body_validated :" +
            $" Extraction.BodyDecodes assemblies ⟨{Quote(PinIdentity(method.Module))}⟩ method{number}Body" +
            $" method{number}Original method{number}TypeArgumentsRaw method{number}Signature :=" +
            $" ⟨{body.Identified}, {body.TablesValid}, by cil_kernel_rfl, pinned_identities_spelled," +
            " by cil_kernel_rfl, by cil_kernel_rfl, by cil_body_decodes⟩");
    }

    /// <summary>The decoded value opcodes whose operands need no storage, model or target resolution.</summary>
    internal static readonly FrozenSet<Code> SimpleOpcodes = new[]
    {
        Code.Nop, Code.Dup, Code.Pop, Code.Ret,
        Code.Ldarg_0, Code.Ldarg_1, Code.Ldarg_2, Code.Ldarg_3,
        Code.Ldloc_0, Code.Ldloc_1, Code.Ldloc_2, Code.Ldloc_3,
        Code.Stloc_0, Code.Stloc_1, Code.Stloc_2, Code.Stloc_3,
        Code.Localloc,
        Code.Ldc_I4_M1, Code.Ldc_I4_0, Code.Ldc_I4_1, Code.Ldc_I4_2, Code.Ldc_I4_3, Code.Ldc_I4_4, Code.Ldc_I4_5,
        Code.Ldc_I4_6, Code.Ldc_I4_7, Code.Ldc_I4_8, Code.Ldnull,
        Code.Ldind_I1, Code.Ldind_U1, Code.Ldind_I2, Code.Ldind_U2, Code.Ldind_I4, Code.Ldind_U4, Code.Ldind_I8,
        Code.Ldind_I, Code.Stind_I1, Code.Stind_I2, Code.Stind_I4, Code.Stind_I8, Code.Stind_I,
        Code.Ldlen, Code.Ldelem_I1, Code.Ldelem_U1, Code.Ldelem_I2, Code.Ldelem_U2, Code.Ldelem_I4, Code.Ldelem_U4,
        Code.Ldelem_I8, Code.Ldelem_I, Code.Ldelem_Ref, Code.Stelem_I, Code.Stelem_I1, Code.Stelem_I2,
        Code.Stelem_I4, Code.Stelem_I8, Code.Stelem_Ref,
        Code.Readonly,
        Code.Br_S, Code.Brfalse_S, Code.Brtrue_S, Code.Beq_S, Code.Bge_S, Code.Bgt_S, Code.Ble_S, Code.Blt_S,
        Code.Bne_Un_S, Code.Bge_Un_S, Code.Bgt_Un_S, Code.Ble_Un_S, Code.Blt_Un_S,
        Code.Br, Code.Brfalse, Code.Brtrue, Code.Beq, Code.Bge, Code.Bgt, Code.Ble, Code.Blt,
        Code.Bne_Un, Code.Bge_Un, Code.Bgt_Un, Code.Ble_Un, Code.Blt_Un,
        Code.Add, Code.Sub, Code.Mul, Code.Div, Code.Div_Un, Code.Rem, Code.Rem_Un, Code.And, Code.Or, Code.Xor,
        Code.Shl, Code.Shr, Code.Shr_Un, Code.Neg, Code.Not,
        Code.Add_Ovf, Code.Add_Ovf_Un, Code.Mul_Ovf, Code.Mul_Ovf_Un, Code.Sub_Ovf, Code.Sub_Ovf_Un,
        Code.Ceq, Code.Cgt, Code.Cgt_Un, Code.Clt, Code.Clt_Un,
        Code.Conv_I1, Code.Conv_I2, Code.Conv_I4, Code.Conv_I8, Code.Conv_I,
        Code.Conv_U1, Code.Conv_U2, Code.Conv_U4, Code.Conv_U8, Code.Conv_U,
        Code.Conv_Ovf_I1, Code.Conv_Ovf_I2, Code.Conv_Ovf_I4, Code.Conv_Ovf_I8, Code.Conv_Ovf_I,
        Code.Conv_Ovf_U1, Code.Conv_Ovf_U2, Code.Conv_Ovf_U4, Code.Conv_Ovf_U8, Code.Conv_Ovf_U,
        Code.Conv_Ovf_I1_Un, Code.Conv_Ovf_I2_Un, Code.Conv_Ovf_I4_Un, Code.Conv_Ovf_I8_Un, Code.Conv_Ovf_I_Un,
        Code.Conv_Ovf_U1_Un, Code.Conv_Ovf_U2_Un, Code.Conv_Ovf_U4_Un, Code.Conv_Ovf_U8_Un, Code.Conv_Ovf_U_Un,
    }.ToFrozenSet();

    /// <summary>
    /// The opcodes Lean's `Instruction.ofRaw?` decodes for some operand, the set `Instruction.valueOpcode` holds;
    /// `Instruction.ofRaw` writes a hole for every other one. Tests/DecodedOpcodes.cs compares the two.
    /// </summary>
    internal static readonly FrozenSet<Code> DecodedOpcodes = SimpleOpcodes.Concat(new[]
    {
        Code.Ldarg_S, Code.Ldarg, Code.Ldarga_S, Code.Ldarga, Code.Starg_S, Code.Starg,
        Code.Ldloc_S, Code.Ldloc, Code.Stloc_S, Code.Stloc, Code.Ldloca_S, Code.Ldloca,
        Code.Ldc_I4_S, Code.Ldc_I4, Code.Ldc_I8, Code.Ldstr, Code.Newarr, Code.Ldelem_Any,
        Code.Stelem_Any, Code.Ldelema, Code.Ldobj, Code.Stobj, Code.Initobj, Code.Cpobj, Code.Sizeof,
        Code.Castclass, Code.Isinst, Code.Ldfld, Code.Ldflda, Code.Stfld, Code.Call, Code.Constrained,
        Code.Callvirt, Code.Newobj, Code.Ldftn, Code.Calli, Code.Switch,
        Code.Cpblk, Code.Initblk, Code.Unaligned
    }).ToFrozenSet();

    /// <summary>The opcodes extraction takes the decoder to read: `DecodedOpcodes`, unless a test narrows the set in
    /// its own process to drive a decoder refusal through the extractor.</summary>
    internal static IReadOnlySet<Code> ExtractedOpcodes { get; set; } = DecodedOpcodes;

    /// <summary>A reachable opcode has no decoder, or its call operand has no matching resolved target.</summary>
    internal enum RefusalKind { Hole, UnboundCall }

    /// <summary>The first live pc, in body order, at which the decoder gives no instruction, with that
    /// instruction.</summary>
    internal sealed record DecodeRefusal(int Pc, Instruction At, RefusalKind Kind);

    /// <summary>The extraction refusal of a method whose decoder refuses a live pc; an admitted method is always
    /// defined from its decoder, so no extraction is written for it.</summary>
    internal sealed class UndecodedInstruction(MethodDefinition method, DecodeRefusal refusal) : Exception($"""
        IL_{refusal.At.Offset:x4}: Unsupported instruction: {Reason(refusal)}
          at pc {refusal.Pc} of {method.FullName}
        """)
    {
        /// <summary>The method whose decoder refuses the instruction.</summary>
        internal MethodDefinition Method { get; } = method;

        /// <summary>The refused pc and instruction.</summary>
        internal DecodeRefusal Refusal { get; } = refusal;

        static string Reason(DecodeRefusal refusal) => refusal.Kind == RefusalKind.Hole
            ? $"the decoder has no form for {refusal.At.OpCode.Name}"
            : $"the decoder cannot bind the {refusal.At.OpCode.Name} operand with its prefixes";
    }

    /// <summary>
    /// The first live instruction without an admitted opcode, field or call binding. Dead sites keep their raw opcode.
    /// </summary>
    internal static DecodeRefusal? FirstDecodeRefusal(MethodDefinition method, IReadOnlySet<Instruction> reachable,
        ResolvedCallSites calls, ImportResolution? imports)
    {
        var instructions = method.Body.Instructions;
        var throws = Throws.Analyze(method);
        var typeTests = TypeTests.Analyze(method);
        for (var pc = 0; pc < instructions.Count; pc++)
        {
            var instruction = instructions[pc];
            if (!reachable.Contains(instruction)) continue;
            if (throws.Operands.Contains(instruction) || throws.Raises.ContainsKey(instruction) ||
                typeTests.Operands.Contains(instruction) || typeTests.Results.ContainsKey(instruction))
                continue;
            if (instruction.OpCode.Code == Code.Tail && instruction.Next?.OpCode.Code is Code.Call or Code.Calli)
                continue;
            if (instruction.OpCode.Code is Code.Ldsfld or Code.Ldsflda ||
                instruction.OpCode.Code == Code.Ldtoken && instruction.Operand is FieldReference)
                continue;
            if (!ExtractedOpcodes.Contains(instruction.OpCode.Code) || UndecodedFieldAccess(instruction))
                return new(pc, instruction, RefusalKind.Hole);
            if (!calls.BindsOperand(instruction, imports)) return new(pc, instruction, RefusalKind.UnboundCall);
        }
        return null;
    }

    // The decoder reads a field instruction on any instance field except one of a generic class instance, whose
    // raw owner `Type` writes as an object application. A wrong answer fails at `cil_decoded_method`.
    static bool UndecodedFieldAccess(Instruction instruction) =>
        instruction.OpCode.Code is Code.Ldfld or Code.Ldflda or Code.Stfld &&
        ((FieldReference)instruction.Operand).DeclaringType is GenericInstanceType owner &&
        ObjectTypes.Reference(owner);

    static readonly HashSet<Instruction> EmptySet = [];

    // A body's metadata tokens are the four bytes after the opcode of these operand kinds.
    static bool HasToken(OpCode opcode) => opcode.OperandType is OperandType.InlineMethod or OperandType.InlineField
        or OperandType.InlineType or OperandType.InlineString or OperandType.InlineSig or OperandType.InlineTok;

    /// <summary>
    /// The body bytes of an original method and its token table: each token read from the body, with the operand
    /// the extractor resolved it to. The Lean decoder reads the same bytes and checks them against the code.
    /// </summary>
    (string Bytes, string Slices, string Definition, string Identified, string TablesValid) Body(
        MethodDefinition original, MethodDefinition admitted,
        IReadOnlySet<Instruction> reachable, int number)
    {
        var body = Pinned.Body(original);
        var bytes = body.Bytes;
        var instructions = new InstructionIndex(original);
        var operands = new List<(uint Token, string Key, string Operand)>();
        var positions = new Dictionary<uint, int>();
        var statics = new List<string>();
        for (var index = 0; index < original.Body.Instructions.Count; index++)
        {
            var instruction = original.Body.Instructions[index];
            if (!HasToken(instruction.OpCode)) continue;
            var token = TokenOperand(original, body, instruction);
            if (BoundStatic(instruction)) statics.Add($"({index}, {token})");
            var site = admitted.Body.Instructions[index];
            // An external identity is a materialized name at a reachable site and a literal at an unreachable
            // one. The literal spelling names the operand, so two sites share a token only if it agrees.
            var key = Operand(original, instructions, instruction, instruction, site, EmptySet);
            var operand = Operand(original, instructions, instruction, instruction, site, reachable);
            var known = positions.GetValueOrDefault(token, -1);
            if (known < 0)
            {
                positions[token] = operands.Count;
                operands.Add((token, key, operand));
            }
            else if (operands[known].Key != key)
                throw new InvalidDataException($"""
                    Metadata token 0x{token:X8} resolves to two operands in {original.FullName}.
                      The body evidence holds one operand per token.
                    """);
            // The kernel decides the equality of a literal and its materialized name, so the table may hold
            // either; the name spares the reachable site a conversion.
            else if (reachable.Contains(site)) operands[known] = (token, key, operand);
        }
        // Each closed instantiation carries its own bytes and metadata slice, built from the open definition and the
        // assembly, so a method's component names no other method and does not depend on which instantiations the
        // extraction holds or in which order.
        var data = MetadataSlices.Bytes(bytes);
        var classOwner = original.HasThis && ObjectTypes.Is(original.DeclaringType);
        var (rows, tables, assemblies) = (metadata ?? throw new InvalidOperationException(
            "Method evidence requires the pinned assemblies.")).Method(original,
            operands.Select(entry => entry.Token).Append(original.Body.LocalVarToken.ToUInt32())
                .Where(token => token != 0), classOwner);
        // The kernel decides once that the literal tables are the decoder's; the body check reads them by name.
        var slices = $"def method{number}Metadata : Extraction.MethodMetadata := {rows}\n" +
            $"def method{number}Tables : List Extraction.IndexTables := {tables}\n" +
            $"def method{number}Names : Extraction.MethodNames := {Names(original, classOwner, admitted.FullName)}\n" +
            $"theorem method{number}_tables_valid : Extraction.tablesMatch method{number}Metadata " +
            $"method{number}Tables = true := by decide +kernel";
        var table = List(operands.Select(entry => $"({entry.Token}, {entry.Operand})"));
        var identities = List(assemblies.Select(index => $"assembly{index}Identity"));
        var identified = assemblies.Reverse().Aggregate("Extraction.AllIdentified.nil",
            (rest, index) => $"(Extraction.AllIdentified.cons assembly{index}_identified {rest})");
        var arguments = MethodSpecialization.Arguments(admitted);
        var instantiation = arguments.Count == 0 ? "" : $", instantiation := {List(arguments.Select(Resolved))}";
        var staticTokens = statics.Count == 0 ? "" : $", statics := {List(statics)}";
        return ($"def method{number}Bytes : List Nat := {data}", slices,
            $"def method{number}Body : Extraction.BodyEvidence := {{ bytes := method{number}Bytes, " +
            $"tokens := {{ operands := {table} }}, metadata := method{number}Metadata, " +
            $"identities := {identities}, tables := method{number}Tables, names := method{number}Names, " +
            $"pinned := pinnedIndex{instantiation}{staticTokens} }}",
            identified, $"method{number}_tables_valid");
    }

    static string Utf8(string text) => MetadataSlices.Bytes(Encoding.UTF8.GetBytes(text));

    /// <summary>
    /// The owner and base class names the method's metadata spells and the signature the extraction selects it by,
    /// as UTF-8 bytes: Lean reads the same names from the carried rows and proves by <c>cil_kernel_rfl</c> that they
    /// spell the strings the evidence states.
    /// </summary>
    static string Names(MethodDefinition original, bool classOwner, string signature)
    {
        var bases = classOwner
            ? ObjectTypes.Bases(original.DeclaringType)
                .Select(type => $"({Utf8(LayoutEvidence.Scope(type))}, {Utf8(type.FullName)})")
            : [];
        return $"{{ owner := {Utf8(LayoutEvidence.Identity(original.DeclaringType))}, bases := {List(bases)}, " +
            $"signature := {Utf8(signature)} }}";
    }

    // A type argument of a generic instance as the resolved type the instance's signature names. Lean admits it
    // against the argument's type expression and spells the instance's full name from it, so only the element type
    // code or the scope and name, and of a generic head its value-type marker and scoped spelling, are stated.
    static string Resolved(TypeReference type) => type switch
    {
        _ when type.IsPrimitive || type.MetadataType is MetadataType.String or MetadataType.Object =>
            $".primitive {(int)type.MetadataType}",
        ArrayType { IsVector: true } array => $".szarray ({Resolved(array.ElementType)})",
        GenericInstanceType generic => $".genericInst {ResolvedHead(generic)} " +
            generic.GenericArguments.Reverse().Aggregate(".nil",
                (rest, argument) => $"(.cons ({Resolved(argument)}) {rest})"),
        _ => $".named {Named(type, false, null)}"
    };

    // A generic head states the value-type marker of the signature that names the instance.
    static string ResolvedHead(GenericInstanceType generic) =>
        Named(generic.ElementType, GenericStructs.Is(generic), generic.ElementType.IsValueType);

    static string Named(TypeReference type, bool scopedArguments, bool? valueType) =>
        $"{{ scope := {Utf8(LayoutEvidence.Scope(type))}, name := {Utf8(type.FullName)}, parts := [], " +
        $"kind := .external {(valueType is { } marker ? $"(some {Bool(marker)})" : "none")}, " +
        $"pinned := {Bool(scopedArguments)} }}";

    static uint TokenOperand(MethodDefinition original, MethodBodyBytes.Body body, Instruction instruction)
    {
        var at = body.HeaderLength + instruction.Offset + instruction.OpCode.Size;
        if (at + sizeof(uint) > body.Bytes.Length)
            throw new InvalidDataException($"Method body of {original.FullName} ends inside a token operand.");
        return BinaryPrimitives.ReadUInt32LittleEndian(body.Bytes.AsSpan(at, sizeof(uint)));
    }

    /// <summary>
    /// The identity block of each pinned assembly: its table header and <c>Assembly</c> row, a function of the
    /// assembly alone, so every extraction of it writes the same bytes.
    /// </summary>
    internal void EmitAssemblyMetadata(StringBuilder lean)
    {
        var slices = metadata ??
            throw new InvalidOperationException("Method evidence requires the pinned assemblies.");
        foreach (var (module, index) in Pinned.Modules.Select((module, index) => (module, index)))
        {
            var identity = Pinned.Original(module).Assembly.Name.FullName;
            lean.AppendLine($"def assembly{index}Metadata : Extraction.AssemblyMetadata := " +
                slices.AssemblyBlock(module));
            lean.AppendLine($"def assembly{index}Identity : List Nat := " +
                MetadataSlices.Bytes(Encoding.UTF8.GetBytes(identity)));
            // The assembly's header bytes decode to the stated header, its bytes spell this identity, and it is the
            // string the block states: one proof for every method of the assembly.
            lean.AppendLine($"theorem assembly{index}_identified : Extraction.AssemblyIdentified " +
                $"assembly{index}Metadata assembly{index}Identity := " +
                "⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩");
        }
        // Identities only: hashes and MVIDs change with every rebuild, so they stay in identity.json for `check`.
        var pins = Pinned.Pins.ToArray();
        for (var k = 0; k < pins.Length; k++)
            lean.AppendLine(
                $"def assembly{k} : Extraction.AssemblyPin := {{ identity := {Quote(pins[k].Identity)} }}");
        lean.AppendLine("def assemblies : List Extraction.AssemblyPin := [" +
            string.Join(", ", Enumerable.Range(0, pins.Length).Select(k => $"assembly{k}")) + "]");
        // Every body lists these identities; one proof that they spell the pins serves them all.
        lean.AppendLine("def pinnedIdentities : List (List Nat) := " +
            List(Pinned.Modules.Select((_, index) => $"assembly{index}Identity")));
        lean.AppendLine("def pinnedIndex : Extraction.PinnedIndex := cil_pin_index pinnedIdentities");
        lean.AppendLine("#print axioms pinnedIndex");
        lean.AppendLine("theorem pinned_identities_spelled : pinnedIdentities.mapM Extraction.spelled? = " +
            "some (assemblies.map (·.identity)) := by cil_kernel_rfl");
    }

    string DispatchTypes(MethodDefinition method)
    {
        var receivers = method.Body.Instructions.Where(instruction => instruction.OpCode.Code == Code.Constrained)
            .Select(instruction => (TypeReference)instruction.Operand)
            .Where(type => ConstrainedCalls.Extracted(type.Resolve().Module, method.Module)).ToArray();
        // Each receiver's interfaces are cataloged from whichever extracted assembly declares them, as resolution
        // requires; an interface outside them is left out, so Lean cannot select an interface-level body past it.
        // A virtual call's catalog holds every class deriving from the slot's class, so Lean can check that
        // the table resolves each one and omits none.
        var hierarchies = method.Body.Instructions.Where(VirtualDispatch.Is)
            .SelectMany(instruction => VirtualDispatch.Hierarchy((MethodReference)instruction.Operand));
        // A type test's class is cataloged so Lean can check it is a pinned class, not an interface.
        var tested = method.Body.Instructions.Where(ObjectTypes.Testable)
            .Select(instruction => (TypeReference)instruction.Operand);
        var types = receivers.Concat(receivers.SelectMany(type => type.Resolve().Interfaces
                .Select(implementation => GenericStructs.Substitute(implementation.InterfaceType,
                    type as GenericInstanceType))
                .Where(implementation => implementation.Resolve() is { } declared &&
                    ConstrainedCalls.Extracted(declared.Module, method.Module))))
            .Concat(hierarchies).Concat(tested)
            .DistinctBy(LayoutEvidence.Identity).OrderBy(LayoutEvidence.Identity, StringComparer.Ordinal);
        return List(types.Select(type =>
        {
            var module = type.Resolve().Module;
            var original = (TypeDefinition)Original(module).LookupToken(type.Resolve().MetadataToken);
            GenericInstanceType? owner = null;
            if (type is GenericInstanceType closed)
            {
                owner = new GenericInstanceType(original);
                foreach (var argument in closed.GenericArguments) owner.GenericArguments.Add(argument);
            }
            return $"{{ identity := {Type(type)}, valueType := {Bool(original.IsValueType)}, " +
                $"interfaceType := {Bool(original.IsInterface)}, " +
                $"interfaces := {List(original.Interfaces.Select(implementation =>
                    Type(GenericStructs.Substitute(implementation.InterfaceType, owner))))}, " +
                $"methods := {List(original.Methods.Select(member => DispatchMethod(member, owner)))}, " +
                $"assembly := {{ identity := {Quote(PinIdentity(module))} }}" + ClassEvidence(original) + " }";
        }));
    }

    // An admitted class's base, when that is an admitted class, and whether it is abstract; virtual dispatch walks
    // these, and other catalog entries keep the defaults.
    static string ClassEvidence(TypeDefinition type)
    {
        if (!ObjectTypes.Is(type)) return "";
        var parent = type.BaseType is { } baseType && ObjectTypes.Is(baseType)
            ? $", base := {ObjectType(baseType)}" : "";
        return parent + (type.IsAbstract ? ", abstractType := true" : "");
    }

    // The pin whose metadata supplied a catalog entry; Lean requires it to scope the entry's type.
    string PinIdentity(ModuleDefinition module) =>
        (pinned ?? throw new InvalidOperationException("Dispatch evidence requires the pinned assemblies."))
            .Pins.ElementAt(pinned.Index(module)).Identity;

    string DispatchMethod(MethodDefinition method, GenericInstanceType? owner)
    {
        // Method type parameters stay `.parameter i`; dispatch closes them at each site's arguments.
        TypeReference Closed(TypeReference type) => owner is null ? type : type switch
        {
            GenericParameter { Type: GenericParameterType.Method } => type,
            GenericParameter => GenericStructs.Substitute(type, owner),
            ArrayType array => new ArrayType(Closed(array.ElementType), array.Rank),
            _ => TypeSubstitution.Components(type, Closed)
        };
        var specialization = owner is null ? "" :
            $", owner := {Head(owner)} {Scope(owner.ElementType)} {Quote(owner.ElementType.FullName)}, " +
            $"ownerArguments := {List(owner.GenericArguments.Select(Type))}";
        return
        $"{{ token := {method.MetadataToken.ToUInt32()}, name := {Quote(method.Name)}, " +
        $"hasThis := {Bool(method.HasThis)}, isPublic := {Bool(method.IsPublic)}, " +
        $"isAbstract := {Bool(method.IsAbstract)}, isVirtual := {Bool(method.IsVirtual)}, " +
        $"hasBody := {Bool(method.HasBody)}, genericArity := {method.GenericParameters.Count}, " +
        $"explicitThis := {Bool(method.ExplicitThis)}, callingConvention := {(byte)method.CallingConvention}, " +
        $"attributes := {(uint)method.Attributes}, implementation := {(uint)method.ImplAttributes}, " +
        $"returnType := {Type(InitAccessors.Return(Closed(method.ReturnType)))}, " +
        $"parameters := {List(method.Parameters.Select(parameter => Parameter(Closed(parameter.ParameterType))))}, " +
        // A slot of any extracted assembly is recorded: dropping one would let a weaker candidate win in Lean.
        $"overrides := {List(method.Overrides
            .Where(slot => PinnedAssemblies.Declares(slot.DeclaringType, method.Module))
            .Select(slot => $"({slot.Resolve().MetadataToken.ToUInt32().ToString(CultureInfo.InvariantCulture)}, " +
                $"{Type(GenericStructs.Substitute(slot.DeclaringType, owner))})"))}{specialization} }}";
    }
}
