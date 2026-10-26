using System.Globalization;
using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Read original definitions from a separate, untouched module over the same assembly
// bytes. The call-graph walk rewrites call operands in the working module.
internal sealed class GenericEvidence(ModuleDefinition originalModule, LayoutEvidence layouts, ImportResolution? imports = null)
{
    readonly ExternalIdentityEvidence externalIdentities = new();

    static string Quote(string value) => JsonSerializer.Serialize(value);
    static string Bool(bool value) => value.ToString().ToLowerInvariant();
    static string List(IEnumerable<string> entries) => "[" + string.Join(", ", entries) + "]";

    static string Scope(TypeReference type)
    {
        var scope = LayoutEvidence.Scope(type);
        return scope == TypeTests.RuntimeScope ? "Extraction.runtimeScope" : Quote(scope);
    }

    string Type(TypeReference type)
    {
        if (type is GenericParameter parameter)
            return parameter.Type == GenericParameterType.Method ? $".parameter {parameter.Position}" :
                $".atom \"\" {Quote("type-parameter:" + parameter.FullName)}";
        if (type is ByReferenceType byRef) return $".byref ({Type(byRef.ElementType)})";
        if (type is ArrayType { IsVector: true } array) return $".array ({Type(array.ElementType)})";
        if (type is PointerType pointer) return $".pointer ({Type(pointer.ElementType)})";
        if (ValueTuples.Is(type) && layouts.Index(type) is >= 0 and var tuple)
            return $".aggregate {Quote(LayoutEvidence.Identity(type))} {tuple}";
        if (type is GenericInstanceType generic)
        {
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
        if (index >= 0) return $".aggregate {Quote(LayoutEvidence.Identity(type))} {index}";
        return $".atom {Scope(type)} {Quote(type.FullName)}";
    }

    string Call(MethodReference reference, Instruction instruction, IReadOnlySet<Instruction> reachable)
    {
        var definition = reference is GenericInstanceMethod generic ? generic.ElementMethod : reference;
        var arguments = reference is GenericInstanceMethod instance ? instance.GenericArguments.ToArray() :
            reference is MethodDefinition specialized ? MethodSpecialization.Arguments(specialized).ToArray() : [];
        var target = definition.DeclaringType.Scope is ModuleDefinition
            ? $".managed {definition.Resolve().MetadataToken.ToUInt32()}"
            : ".external " + externalIdentities.Reference(imports?.Identity(instruction) ??
                (LayoutEvidence.Scope(definition.DeclaringType) + "::" + definition.FullName),
                reachable.Contains(instruction));
        var name = definition.DeclaringType.Scope is ModuleDefinition
            ? ((MethodDefinition)originalModule.LookupToken(definition.Resolve().MetadataToken)).Name : definition.Name;
        return $"{{ declaringType := {Type(definition.DeclaringType)}, name := {Quote(name)}, target := {target}, typeArguments := {List(arguments.Select(Type))}, parameterCount := {reference.Parameters.Count}, hasThis := {Bool(reference.HasThis)}, returnsValue := {Bool(reference.ReturnType.FullName != "System.Void")}, returnType := {Type(CallReturnType.Resolve(reference))}, parameterTypes := {List(CallReturnType.Parameters(reference).Select(Type))} }}";
    }

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
            case FieldReference field:
                var isStatic = instruction.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda or Code.Ldtoken;
                var index = 0;
                var fieldType = field.FieldType;
                if (field.DeclaringType.Scope is ModuleDefinition)
                {
                    var resolved = field.Resolve();
                    index = layouts.Metadata.FieldIndex(resolved.DeclaringType, resolved, isStatic);
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

    static string ConstraintType(TypeReference type) => type is RequiredModifierType modifier
        ? LayoutEvidence.Identity(modifier.ModifierType) + "!" + LayoutEvidence.Identity(modifier.ElementType)
        : LayoutEvidence.Identity(type);

    string Method(MethodDefinition method, MethodDefinition admitted, IReadOnlySet<Instruction> reachable)
    {
        var instructions = new InstructionIndex(method);
        var constraints = method.GenericParameters.Select(parameter =>
            $"{{ flags := {(uint)parameter.Attributes}, types := {List(parameter.Constraints.Select(constraint => Quote(ConstraintType(constraint.ConstraintType))))} }}");
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
        return $"{{ token := {method.MetadataToken.ToUInt32()}, owner := {Quote(LayoutEvidence.Identity(method.DeclaringType))}, hasThis := {Bool(method.HasThis)}, explicitThis := {Bool(method.ExplicitThis)}, callingConvention := {(byte)method.CallingConvention}, attributes := {(uint)method.Attributes}, implementation := {(uint)method.ImplAttributes}, returnType := {Type(method.ReturnType)}, parameters := {List(method.Parameters.Select(parameter => Type(parameter.ParameterType)))}, locals := {List(method.Body.Variables.Select(local => Type(local.VariableType)))}, initLocals := {Bool(method.Body.InitLocals)}, maxStack := {method.Body.MaxStackSize}, genericParameters := {List(constraints)}, code := {List(code)} }}";
    }

    internal void EmitMethod(StringBuilder lean, MethodDefinition method, int number,
        IReadOnlySet<Instruction> reachable)
    {
        var original = (MethodDefinition)originalModule.LookupToken(method.MetadataToken);
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
            .Select(instruction => ((TypeReference)instruction.Operand).Resolve())
            .Where(type => type.Module == method.Module).ToArray();
        var types = receivers.Concat(receivers.SelectMany(type => type.Interfaces)
                .Select(implementation => implementation.InterfaceType.Resolve())
                .Where(type => type.Module == method.Module))
            .DistinctBy(type => type.MetadataToken.ToUInt32()).OrderBy(type => type.MetadataToken.ToUInt32());
        return List(types.Select(type =>
        {
            var original = (TypeDefinition)originalModule.LookupToken(type.MetadataToken);
            return $"{{ identity := {Type(original)}, valueType := {Bool(original.IsValueType)}, " +
                $"interfaceType := {Bool(original.IsInterface)}, " +
                $"interfaces := {List(original.Interfaces.Select(implementation => Type(implementation.InterfaceType)))}, " +
                $"methods := {List(original.Methods.Select(DispatchMethod))} }}";
        }));
    }

    string DispatchMethod(MethodDefinition method) =>
        $"{{ token := {method.MetadataToken.ToUInt32()}, name := {Quote(method.Name)}, " +
        $"hasThis := {Bool(method.HasThis)}, isPublic := {Bool(method.IsPublic)}, " +
        $"isAbstract := {Bool(method.IsAbstract)}, isVirtual := {Bool(method.IsVirtual)}, " +
        $"hasBody := {Bool(method.HasBody)}, genericArity := {method.GenericParameters.Count}, " +
        $"explicitThis := {Bool(method.ExplicitThis)}, callingConvention := {(byte)method.CallingConvention}, " +
        $"attributes := {(uint)method.Attributes}, implementation := {(uint)method.ImplAttributes}, " +
        $"returnType := {Type(method.ReturnType)}, parameters := {List(method.Parameters.Select(parameter => Type(parameter.ParameterType)))}, " +
        $"overrides := {List(method.Overrides.Where(slot => slot.DeclaringType.Scope is ModuleDefinition).Select(slot => slot.Resolve().MetadataToken.ToUInt32().ToString(CultureInfo.InvariantCulture)))} }}";
}
