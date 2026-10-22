using System.Globalization;
using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Read original definitions from a separate, untouched module over the same assembly
// bytes. The call-graph walk rewrites call operands in the working module.
internal sealed class GenericEvidence(ModuleDefinition originalModule, LayoutEvidence layouts)
{
    static string Quote(string value) => JsonSerializer.Serialize(value);
    static string Bool(bool value) => value.ToString().ToLowerInvariant();
    static string List(IEnumerable<string> entries) => "[" + string.Join(", ", entries) + "]";

    string Type(TypeReference type)
    {
        if (type is GenericParameter parameter)
            return parameter.Type == GenericParameterType.Method ? $".parameter {parameter.Position}" :
                $".atom \"\" {Quote("type-parameter:" + parameter.FullName)}";
        if (type is ByReferenceType byRef) return $".byref ({Type(byRef.ElementType)})";
        if (type is PointerType pointer) return $".pointer ({Type(pointer.ElementType)})";
        if (ValueTuples.Is(type) && layouts.Index(type) is >= 0 and var tuple)
            return $".aggregate {Quote(LayoutEvidence.Identity(type))} {tuple}";
        if (type is GenericInstanceType generic)
        {
            var result = $".constructor {Quote(LayoutEvidence.Scope(generic.ElementType))} {Quote(generic.ElementType.FullName)}";
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
        return $".atom {Quote(LayoutEvidence.Scope(type))} {Quote(type.FullName)}";
    }

    string Call(MethodReference reference)
    {
        var definition = reference is GenericInstanceMethod generic ? generic.ElementMethod : reference;
        var arguments = reference is GenericInstanceMethod instance ? instance.GenericArguments.ToArray() :
            reference is MethodDefinition specialized ? MethodSpecialization.Arguments(specialized).ToArray() : [];
        var target = definition.DeclaringType.Scope is ModuleDefinition
            ? $".managed {definition.Resolve().MetadataToken.ToUInt32()}"
            : $".external {Quote(LayoutEvidence.Scope(definition.DeclaringType) + "::" + definition.FullName)}";
        var name = definition.DeclaringType.Scope is ModuleDefinition
            ? ((MethodDefinition)originalModule.LookupToken(definition.Resolve().MetadataToken)).Name : definition.Name;
        return $"{{ declaringType := {Type(definition.DeclaringType)}, name := {Quote(name)}, target := {target}, typeArguments := {List(arguments.Select(Type))}, parameterCount := {reference.Parameters.Count}, hasThis := {Bool(reference.HasThis)}, returnsValue := {Bool(reference.ReturnType.FullName != "System.Void")} }}";
    }

    string Operand(MethodDefinition method, Instruction instruction)
    {
        switch (instruction.Operand)
        {
            case null: return ".none";
            case Instruction target: return $".target {method.Body.Instructions.IndexOf(target)}";
            case Instruction[] targets: return $".targets {List(targets.Select(target => method.Body.Instructions.IndexOf(target).ToString(CultureInfo.InvariantCulture)))}";
            case ParameterDefinition parameter:
                var argument = parameter.Index < 0 && method.HasThis ? 0 : parameter.Index + (method.HasThis ? 1 : 0);
                if (argument < 0) throw new InvalidDataException("Invalid raw argument index");
                return $".argument {argument}";
            case VariableDefinition local: return $".local {local.Index}";
            case TypeReference type: return $".type ({Type(type)})";
            case MethodReference callee: return $".call {Call(callee)}";
            case FieldReference field:
                var isStatic = instruction.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda or Code.Ldtoken;
                var index = 0;
                var fieldType = field.FieldType;
                if (field.DeclaringType.Scope is ModuleDefinition)
                {
                    var resolved = field.Resolve();
                    var fields = resolved.DeclaringType.Fields.Where(candidate => isStatic || !candidate.IsStatic).ToList();
                    index = fields.IndexOf(resolved);
                }
                else if (!isStatic && ValueTuples.Is(field.DeclaringType))
                {
                    // Tuple fields are typed by the instance's arguments, not the definition's T1/T2.
                    var fields = MetadataValidation.Fields(field.DeclaringType);
                    index = Array.FindIndex(fields, candidate => candidate.Definition == field.Resolve());
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

    string Method(MethodDefinition method)
    {
        var constraints = method.GenericParameters.Select(parameter =>
            $"{{ flags := {(uint)parameter.Attributes}, types := {List(parameter.Constraints.Select(constraint => Quote(ConstraintType(constraint.ConstraintType))))} }}");
        var code = method.Body.Instructions.Select(instruction =>
            $"{{ offset := {instruction.Offset}, opcode := {(ushort)instruction.OpCode.Value}, operand := {Operand(method, instruction)} }}");
        return $"{{ token := {method.MetadataToken.ToUInt32()}, owner := {Quote(LayoutEvidence.Identity(method.DeclaringType))}, hasThis := {Bool(method.HasThis)}, explicitThis := {Bool(method.ExplicitThis)}, callingConvention := {(byte)method.CallingConvention}, attributes := {(uint)method.Attributes}, implementation := {(uint)method.ImplAttributes}, returnType := {Type(method.ReturnType)}, parameters := {List(method.Parameters.Select(parameter => Type(parameter.ParameterType)))}, locals := {List(method.Body.Variables.Select(local => Type(local.VariableType)))}, initLocals := {Bool(method.Body.InitLocals)}, maxStack := {method.Body.MaxStackSize}, genericParameters := {List(constraints)}, code := {List(code)} }}";
    }

    internal void EmitMethod(StringBuilder lean, MethodDefinition method, int number)
    {
        var original = (MethodDefinition)originalModule.LookupToken(method.MetadataToken);
        lean.AppendLine($"def method{number}Original : Extraction.RawMethod := {Method(original)}");
        lean.AppendLine($"def method{number}TypeArgumentsRaw : List Extraction.TypeExpr := {List(MethodSpecialization.Arguments(method).Select(Type))}");
        lean.AppendLine($"def method{number}Closed : Extraction.RawMethod := {Method(method)}");
        lean.AppendLine($"theorem method{number}_specialization_validated : Extraction.SpecializationValid rawLayouts method{number}Original method{number}TypeArgumentsRaw method{number}Closed method{number}RawArguments := {LeanEmitter.Decide}");
    }
}
