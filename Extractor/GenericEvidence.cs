using System.Buffers.Binary;
using System.Globalization;
using System.Text;
using System.Text.Json;
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
    int methodParameterCount;

    // Type serialization needs no method bodies; only method and dispatch evidence read originals.
    PinnedAssemblies Pinned => pinned ??
        throw new InvalidOperationException("Method evidence requires the pinned assemblies.");

    ModuleDefinition Original(ModuleDefinition module) => Pinned.Original(module);

    /// <summary>The Lean string literal of <paramref name="value"/>.</summary>
    internal static string Quote(string value) => JsonSerializer.Serialize(value);
    static string Bool(bool value) => value.ToString().ToLowerInvariant();
    static string List(IEnumerable<string> entries) => "[" + string.Join(", ", entries) + "]";

    static string Scope(TypeReference type) => Scope(LayoutEvidence.Scope(type));

    static string Scope(string assembly) =>
        assembly == TypeTests.RuntimeScope ? "Extraction.runtimeScope" : Quote(assembly);

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

    string Type(TypeReference type, bool preserveGeneric)
    {
        if (type is FunctionPointerType callable)
        {
            var parameters = ".void";
            foreach (var argument in callable.Parameters.Reverse())
                parameters = $".signatureParameter ({Type(argument.ParameterType)}) ({parameters})";
            return $".functionPointer ({Type(callable.ReturnType)}) ({parameters}) " +
                $"{(int)callable.CallingConvention} {callable.HasThis.ToString().ToLowerInvariant()} " +
                callable.ExplicitThis.ToString().ToLowerInvariant();
        }
        if (type is GenericParameter parameter)
            return $".parameter {parameter.Position +
                (parameter.Type == GenericParameterType.Method ? 0 : methodParameterCount)}";
        if (type is ByReferenceType byRef) return $".byref ({Type(byRef.ElementType)})";
        // An element class outside the model is named as an object, as the array's reference slots hold it.
        if (type is ArrayType { IsVector: true } array)
            return $".array ({(ReferenceArrays.Is(array) ? ObjectType(array.ElementType) : Type(array.ElementType))})";
        if (type is PointerType pointer) return $".pointer ({Type(pointer.ElementType)})";
        if (ValueTuples.Is(type) && layouts.Index(type) is >= 0 and var tuple)
            return $".aggregate {Quote(LayoutEvidence.Identity(type))} {tuple}";
        if (type is GenericInstanceType generic)
        {
            if (!preserveGeneric && GenericStructs.Is(type) && layouts.Index(type) is >= 0 and var aggregate)
                return $".aggregate {Quote(LayoutEvidence.Identity(type))} {aggregate}";
            var result = $".constructor {Scope(generic.ElementType)} {Quote(generic.ElementType.FullName)}";
            foreach (var argument in generic.GenericArguments) result = $".apply ({result}) ({Type(argument)})";
            return result;
        }
        if (type.FullName == "System.Void") return ".void";
        if (EnumTypes.IsEnum(type))
        {
            var underlying = type.Resolve().Fields.Single(field => !field.IsStatic).FieldType;
            return $".enum {Quote(LayoutEvidence.Identity(type))} ({Type(underlying)})";
        }
        if (ObjectTypes.Reference(type)) return ObjectType(type);
        var index = layouts.Index(type);
        if (index >= 0 && !layouts.Metadata.IsImported(type))
            return $".aggregate {Quote(LayoutEvidence.Identity(type))} {index}";
        return $".atom {Scope(type)} {Quote(type.FullName)}";
    }

    // Signatures name an imported layout by scoped atom, as the import boundary requires; only a
    // local declaration binds it to the table entry that sizes its storage.
    string LocalType(TypeReference type) => layouts.Metadata.IsImported(type)
        ? $".aggregate {Quote(LayoutEvidence.Identity(type))} {layouts.Index(type)}" : Type(type);

    string Call(MethodReference reference, Instruction instruction, IReadOnlySet<Instruction> reachable)
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
        var target = extracted
            ? $".managed {definition.Resolve().MetadataToken.ToUInt32()}"
            : ".external " + externalIdentities.Reference(imports?.Identity(instruction) ??
                (LayoutEvidence.Scope(definition.DeclaringType) + "::" + ExternalSignature(definition)),
                reachable.Contains(instruction));
        var name = extracted
            ? ((MethodDefinition)Original(definition.Resolve().Module)
                .LookupToken(definition.Resolve().MetadataToken)).Name : definition.Name;
        return $"{{ declaringType := {Type(declaringType, true)}, name := {Quote(name)}, target := {target}, typeArguments := {List(arguments.Select(Type))}, ownerArgumentCount := {owners.Length}, parameterCount := {reference.Parameters.Count}, hasThis := {Bool(reference.HasThis)}, returnsValue := {Bool(Returned(reference).FullName != "System.Void")}, returnType := {Type(Returned(reference))}, parameterTypes := {List(CallReturnType.Parameters(reference).Select(Parameter))} }}";
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

    string Operand(MethodDefinition method, InstructionIndex instructions, Instruction instruction,
        Instruction admittedInstruction, IReadOnlySet<Instruction> reachable)
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
            case TypeReference type when instruction.OpCode.Code == Code.Newarr && ReferenceArrays.Element(type):
                return $".type ({ObjectType(type)})";
            case TypeReference type: return $".type ({Type(type)})";
            case MethodReference callee: return $".call {Call(callee, admittedInstruction, reachable)}";
            case Mono.Cecil.CallSite site when instruction.OpCode.Code == Code.Calli:
                return $".indirectCall ({Type(site.ReturnType)}) "+
                    $"{List(site.Parameters.Select(parameter => Type(parameter.ParameterType)))} "+
                    $"{Bool(site.HasThis)} {Bool(site.ExplicitThis)} {(int)site.CallingConvention}";
            case FieldReference field:
                var isStatic = instruction.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda or Code.Ldtoken;
                var index = 0;
                // A field signature's `!n` is the declaring type's parameter: the declaring instance's argument.
                var fieldType = field.FieldType.ContainsGenericParameter &&
                    field.DeclaringType is GenericInstanceType instance
                    ? GenericStructs.Substitute((field.Resolve() ?? throw new InvalidDataException(
                        "Unresolved generic field: " + field.FullName)).FieldType, instance) : field.FieldType;
                if (field.DeclaringType.Scope is ModuleDefinition ||
                    PinnedAssemblies.Active?.ModuleOf(field.DeclaringType) is not null)
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
                // A class field of a type outside the model holds an object reference like an admitted one.
                var heldType = !isStatic && ObjectTypes.Is(field.DeclaringType) && ObjectTypes.Opaque(fieldType)
                    ? ObjectType(fieldType) : Type(fieldType);
                return $".field ({Type(field.DeclaringType)}) {index} ({heldType}) {Bool(isStatic)}";
            case string text: return $".text {Quote(text)}";
            case float number: return $".text {Quote("float:" + BitConverter.SingleToInt32Bits(number).ToString(CultureInfo.InvariantCulture))}";
            case double number: return $".text {Quote("double:" + BitConverter.DoubleToInt64Bits(number).ToString(CultureInfo.InvariantCulture))}";
            case sbyte or byte or short or ushort or int or uint or long or ulong:
                return $".integer ({Convert.ToString(instruction.Operand, CultureInfo.InvariantCulture)})";
            default: throw new InvalidDataException("Unsupported raw CIL operand: " + instruction.Operand.GetType().Name);
        }
    }

    internal static string ConstraintType(TypeReference type) => type is RequiredModifierType modifier
        ? LayoutEvidence.Identity(modifier.ModifierType) + "!" + LayoutEvidence.Identity(modifier.ElementType)
        : LayoutEvidence.InterfaceIdentity(type);

    static string Constraint(TypeReference type)
    {
        var identity = ConstraintType(type);
        return identity switch
        {
            TypeTests.RuntimeScope + "::System.ValueType" => "Extraction.valueTypeConstraint",
            TypeTests.RuntimeScope + "::System.Runtime.InteropServices.UnmanagedType!" +
                TypeTests.RuntimeScope + "::System.ValueType" => "Extraction.unmanagedTypeConstraint",
            _ => Quote(identity)
        };
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

    string Method(MethodDefinition method, MethodDefinition admitted, IReadOnlySet<Instruction> reachable)
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
            var operand = Operand(method, instructions, instruction, selected, reachable);
            return $"{{ offset := {instruction.Offset}, opcode := {(ushort)instruction.OpCode.Value}, " +
                $"operand := {operand} }}";
        });
        var owner = Quote(LayoutEvidence.Identity(method.DeclaringType));
        var classOwner = method.HasThis && ObjectTypes.Is(method.DeclaringType);
        var objectReceiver = Bool(classOwner);
        var objectFields = classOwner ? ObjectTypes.Fields(method.DeclaringType).Length : 0;
        var objectBases = classOwner ? ObjectTypes.BaseList(method.DeclaringType) : "[]";
        var parameters = List(method.Parameters.Select(parameter => Parameter(parameter.ParameterType)));
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
            returnType := {{Type(InitAccessors.Return(method.ReturnType))}}, parameters := {{parameters}},
            locals := {{locals}}, initLocals := {{Bool(method.Body.InitLocals)}},
            maxStack := {{method.Body.MaxStackSize}}, genericParameters := {{List(constraints)}},
            code := {{List(code)}} }
            """.ReplaceLineEndings(" ");
    }

    internal void EmitMethod(StringBuilder lean, MethodDefinition method, int number,
        IReadOnlySet<Instruction> reachable)
    {
        var original = (MethodDefinition)Original(method.Module).LookupToken(method.MetadataToken);
        var originalEvidence = Method(original, method, reachable);
        // Token operands are spelled in the original's generic context, as its code is.
        var body = Body(original, method, reachable, number);
        var closedEvidence = Method(method, method, reachable);
        externalIdentities.Emit(lean);
        lean.AppendLine($"def method{number}Original : Extraction.RawMethod := {originalEvidence}");
        lean.AppendLine(body.Bytes);
        if (body.Slices.Length > 0)
            foreach (var line in body.Slices.Split('\n')) lean.AppendLine(line);
        lean.AppendLine(body.Definition);
        lean.AppendLine($"def method{number}TypeArgumentsRaw : List Extraction.TypeExpr := {List(MethodSpecialization.Arguments(method).Select(Type))}");
        lean.AppendLine($"def method{number}Closed : Extraction.RawMethod := {closedEvidence}");
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
        for (var index = 0; index < original.Body.Instructions.Count; index++)
        {
            var instruction = original.Body.Instructions[index];
            if (!HasToken(instruction.OpCode)) continue;
            var token = TokenOperand(original, body, instruction);
            var site = admitted.Body.Instructions[index];
            // An external identity is a materialized name at a reachable site and a literal at an unreachable
            // one. The literal spelling names the operand, so two sites share a token only if it agrees.
            var key = Operand(original, instructions, instruction, site, EmptySet);
            var operand = Operand(original, instructions, instruction, site, reachable);
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
        var data = List(bytes.Select(value => value.ToString(CultureInfo.InvariantCulture)));
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
        return ($"def method{number}Bytes : List Nat := {data}", slices,
            $"def method{number}Body : Extraction.BodyEvidence := {{ bytes := method{number}Bytes, " +
            $"tokens := {{ operands := {table} }}, metadata := method{number}Metadata, " +
            $"identities := {identities}, tables := method{number}Tables, names := method{number}Names, " +
            $"pinned := pinnedIdentities{instantiation} }}",
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
    // code or the scope and name, and whether a generic head spells scoped arguments, are stated.
    static string Resolved(TypeReference type) => type switch
    {
        _ when type.IsPrimitive || type.MetadataType is MetadataType.String or MetadataType.Object =>
            $".primitive {(int)type.MetadataType}",
        ArrayType { IsVector: true } array => $".szarray ({Resolved(array.ElementType)})",
        GenericInstanceType generic => $".genericInst {Named(generic.ElementType, GenericStructs.Is(generic))} " +
            generic.GenericArguments.Reverse().Aggregate(".nil",
                (rest, argument) => $"(.cons ({Resolved(argument)}) {rest})"),
        _ => $".named {Named(type, false)}"
    };

    static string Named(TypeReference type, bool scopedArguments) =>
        $"{{ scope := {Utf8(LayoutEvidence.Scope(type))}, name := {Utf8(type.FullName)}, parts := [], " +
        $"kind := .external none, pinned := {Bool(scopedArguments)} }}";

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
                MetadataSlices.Bytes(System.Text.Encoding.UTF8.GetBytes(identity)));
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
            $", owner := .constructor {Scope(owner.ElementType)} {Quote(owner.ElementType.FullName)}, " +
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
