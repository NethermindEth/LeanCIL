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
    readonly ExternalIdentityEvidence externalIdentities = new();
    int methodParameterCount;

    // Type serialization needs no method bodies; only method and dispatch evidence read originals.
    ModuleDefinition Original(ModuleDefinition module) => (pinned ??
        throw new InvalidOperationException("Method evidence requires the pinned assemblies.")).Original(module);

    static string Quote(string value) => JsonSerializer.Serialize(value);
    static string Bool(bool value) => value.ToString().ToLowerInvariant();
    static string List(IEnumerable<string> entries) => "[" + string.Join(", ", entries) + "]";

    static string Scope(TypeReference type)
    {
        var scope = LayoutEvidence.Scope(type);
        return scope == TypeTests.RuntimeScope ? "Extraction.runtimeScope" : Quote(scope);
    }

    internal string Type(TypeReference type) => Type(type, false);

    // The kernel sees an `in` reference as the reference it is; the extractor compares the modifier exactly.
    string Parameter(TypeReference type) => Type(InReferences.Parameter(type));

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
        if (type is ArrayType { IsVector: true } array) return $".array ({Type(array.ElementType)})";
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
        return $"{{ declaringType := {Type(declaringType, true)}, name := {Quote(name)}, target := {target}, typeArguments := {List(arguments.Select(Type))}, ownerArgumentCount := {owners.Length}, parameterCount := {reference.Parameters.Count}, hasThis := {Bool(reference.HasThis)}, returnsValue := {Bool(reference.ReturnType.FullName != "System.Void")}, returnType := {Type(CallReturnType.Resolve(reference))}, parameterTypes := {List(CallReturnType.Parameters(reference).Select(Parameter))} }}";
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
            case TypeReference type: return $".type ({Type(type)})";
            case MethodReference callee: return $".call {Call(callee, admittedInstruction, reachable)}";
            case Mono.Cecil.CallSite site when instruction.OpCode.Code == Code.Calli:
                return $".indirectCall ({Type(site.ReturnType)}) "+
                    $"{List(site.Parameters.Select(parameter => Type(parameter.ParameterType)))} "+
                    $"{Bool(site.HasThis)} {Bool(site.ExplicitThis)} {(int)site.CallingConvention}";
            case FieldReference field:
                var isStatic = instruction.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda or Code.Ldtoken;
                var index = 0;
                var fieldType = field.FieldType;
                if (field.DeclaringType.Scope is ModuleDefinition ||
                    PinnedAssemblies.Active?.ModuleOf(field.DeclaringType) is not null)
                {
                    var resolved = field.Resolve();
                    index = layouts.Metadata.FieldIndex(field.DeclaringType, resolved, isStatic);
                    if (!isStatic) fieldType = layouts.Metadata.Fields(field.DeclaringType)[index].Type;
                }
                else if (!isStatic && ValueTuples.Is(field.DeclaringType))
                {
                    // Tuple fields are typed by the instance's arguments, not the definition's T1/T2.
                    var fields = layouts.Metadata.Fields(field.DeclaringType);
                    index = layouts.Metadata.FieldIndex(field.DeclaringType, field.Resolve());
                    if (index < 0) throw new InvalidDataException("Unresolved tuple field: " + field.FullName);
                    fieldType = fields[index].Type;
                }
                return $".field ({Type(field.DeclaringType)}) {index} ({Type(fieldType)}) {Bool(isStatic)}";
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
        return $"{{ token := {method.MetadataToken.ToUInt32()}, owner := {Quote(LayoutEvidence.Identity(method.DeclaringType))}, ownerParameters := {List(ownerConstraints)}, ownerArgumentCount := {MethodSpecialization.OwnerArguments(method).Count}, hasThis := {Bool(method.HasThis)}, explicitThis := {Bool(method.ExplicitThis)}, callingConvention := {(byte)method.CallingConvention}, attributes := {(uint)method.Attributes}, implementation := {(uint)method.ImplAttributes}, returnType := {Type(method.ReturnType)}, parameters := {List(method.Parameters.Select(parameter => Parameter(parameter.ParameterType)))}, locals := {List(method.Body.Variables.Select(local => LocalType(local.VariableType)))}, initLocals := {Bool(method.Body.InitLocals)}, maxStack := {method.Body.MaxStackSize}, genericParameters := {List(constraints)}, code := {List(code)} }}";
    }

    internal void EmitMethod(StringBuilder lean, MethodDefinition method, int number,
        IReadOnlySet<Instruction> reachable)
    {
        var original = (MethodDefinition)Original(method.Module).LookupToken(method.MetadataToken);
        var originalEvidence = Method(original, method, reachable);
        var closedEvidence = Method(method, method, reachable);
        externalIdentities.Emit(lean);
        lean.AppendLine($"def method{number}Original : Extraction.RawMethod := {originalEvidence}");
        lean.AppendLine($"def method{number}TypeArgumentsRaw : List Extraction.TypeExpr := {List(MethodSpecialization.Arguments(method).Select(Type))}");
        lean.AppendLine($"def method{number}Closed : Extraction.RawMethod := {closedEvidence}");
        lean.AppendLine($"def method{number}DispatchTypes : List Extraction.DispatchType := {DispatchTypes(method)}");
        // Direct equality proofs avoid a separate structural decision over the raw metadata.
        lean.AppendLine($"theorem method{number}_specialization_validated :" +
            $" Extraction.SpecializationValid rawLayouts method{number}Original method{number}TypeArgumentsRaw" +
            $" method{number}Closed method{number}RawArguments := by constructor <;> rfl");
    }

    string DispatchTypes(MethodDefinition method)
    {
        var receivers = method.Body.Instructions.Where(instruction => instruction.OpCode.Code == Code.Constrained)
            .Select(instruction => (TypeReference)instruction.Operand)
            .Where(type => type.Resolve().Module == method.Module).ToArray();
        var types = receivers.Concat(receivers.SelectMany(type => type.Resolve().Interfaces
                .Select(implementation => GenericStructs.Substitute(implementation.InterfaceType,
                    type as GenericInstanceType)))
                .Where(type => type.Resolve().Module == method.Module))
            .DistinctBy(LayoutEvidence.Identity).OrderBy(LayoutEvidence.Identity, StringComparer.Ordinal);
        return List(types.Select(type =>
        {
            var original = (TypeDefinition)Original(type.Resolve().Module).LookupToken(type.Resolve().MetadataToken);
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
                $"methods := {List(original.Methods.Select(member => DispatchMethod(member, owner)))} }}";
        }));
    }

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
        $"returnType := {Type(Closed(method.ReturnType))}, " +
        $"parameters := {List(method.Parameters.Select(parameter => Parameter(Closed(parameter.ParameterType))))}, " +
        $"overrides := {List(method.Overrides.Where(slot => slot.DeclaringType.Scope is ModuleDefinition)
            .Select(slot => $"({slot.Resolve().MetadataToken.ToUInt32().ToString(CultureInfo.InvariantCulture)}, " +
                $"{Type(GenericStructs.Substitute(slot.DeclaringType, owner))})"))}{specialization} }}";
    }
}
