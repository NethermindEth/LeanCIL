using System.Runtime.CompilerServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Specialization substitutes metadata types; it never rewrites the compiled assembly.
internal sealed class MethodSpecialization(ModuleDefinition module)
{
    internal sealed record Origin(string Definition, string[] TypeArguments);
    static readonly ConditionalWeakTable<MethodDefinition, Origin> origins = new();
    readonly Dictionary<string, MethodDefinition> instances = new(StringComparer.Ordinal);

    internal static Origin? Source(MethodDefinition method) => origins.TryGetValue(method, out var origin) ? origin : null;

    internal MethodDefinition Instantiate(GenericInstanceMethod reference)
    {
        var definition = reference.Resolve() ?? throw new InvalidDataException("Unresolved generic method");
        if (definition.Module != module || definition.DeclaringType.HasGenericParameters ||
            reference.ElementMethod.FullName != definition.FullName || reference.HasThis != definition.HasThis ||
            reference.ExplicitThis || reference.GenericArguments.Count != definition.GenericParameters.Count ||
            !definition.HasGenericParameters || definition.IsConstructor || !definition.HasBody || definition.Body.ExceptionHandlers.Count != 0 ||
            (reference.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default ||
            (definition.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default)
            throw new InvalidDataException("Unsupported generic method signature or body");

        foreach (var argument in reference.GenericArguments)
        {
            if (argument is ByReferenceType or PointerType or GenericParameter)
                throw new InvalidDataException("Unsupported generic method type argument");
            MetadataValidation.Type(argument, module);
        }
        foreach (var parameter in definition.GenericParameters)
        {
            // 0x20 is the .NET allows-ref-struct anti-constraint. Other flags are
            // either reference/variance constraints or unsupported metadata bits.
            var allowed = GenericParameterAttributes.NotNullableValueTypeConstraint |
                GenericParameterAttributes.DefaultConstructorConstraint | (GenericParameterAttributes)0x20;
            if ((parameter.Attributes & ~allowed) != 0)
                throw new InvalidDataException("Unsupported generic method constraints");
            foreach (var constraint in parameter.Constraints)
            {
                var type = constraint.ConstraintType;
                if (type is RequiredModifierType modifier &&
                    modifier.ModifierType.FullName == "System.Runtime.InteropServices.UnmanagedType" &&
                    RuntimeModels.ExactScope(modifier.ModifierType.Scope, "System.Runtime"))
                    type = modifier.ElementType;
                if (type.FullName != "System.ValueType" || !RuntimeModels.ExactScope(type.Scope, "System.Runtime"))
                    throw new InvalidDataException("Unsupported generic method constraints");
                RuntimeModels.ValidateTypeIdentity(type, module);
            }
        }

        var key = reference.FullName;
        if (instances.TryGetValue(key, out var existing)) return existing;
        if (instances.Count >= 256)
            throw new InvalidDataException("Generic specialization limit exceeded (possible expanding recursion)");

        TypeReference Substitute(TypeReference type)
        {
            if (type is GenericParameter parameter && parameter.Type == GenericParameterType.Method && parameter.Owner == definition)
                return parameter.Position >= 0 && parameter.Position < reference.GenericArguments.Count
                    ? reference.GenericArguments[parameter.Position]
                    : throw new InvalidDataException("Malformed generic method type parameter");
            if (type is ByReferenceType byRef) return new ByReferenceType(Substitute(byRef.ElementType));
            if (type is PointerType pointer) return new PointerType(Substitute(pointer.ElementType));
            if (type is GenericInstanceType generic)
            {
                var result = new GenericInstanceType(generic.ElementType);
                foreach (var argument in generic.GenericArguments) result.GenericArguments.Add(Substitute(argument));
                return result;
            }
            return type;
        }

        MethodReference SubstituteMethod(MethodReference method)
        {
            if (method is GenericInstanceMethod generic)
            {
                var result = new GenericInstanceMethod(generic.ElementMethod);
                foreach (var argument in generic.GenericArguments) result.GenericArguments.Add(Substitute(argument));
                return result;
            }
            return method;
        }

        var clone = new MethodDefinition(definition.Name + "<" + string.Join(",", reference.GenericArguments.Select(t => t.FullName)) + ">",
            definition.Attributes, Substitute(definition.ReturnType))
        {
            DeclaringType = definition.DeclaringType,
            ImplAttributes = definition.ImplAttributes,
            CallingConvention = definition.CallingConvention & ~MethodCallingConvention.Generic,
            HasThis = definition.HasThis,
            ExplicitThis = definition.ExplicitThis,
            MetadataToken = definition.MetadataToken
        };
        // Materialize an empty collection: the retained source token must not lazily
        // reload the definition's open generic parameters into this closed body.
        clone.GenericParameters.Clear();
        foreach (var parameter in definition.Parameters)
            clone.Parameters.Add(new ParameterDefinition(parameter.Name, parameter.Attributes, Substitute(parameter.ParameterType)));
        clone.Body = new MethodBody(clone) { InitLocals = definition.Body.InitLocals, MaxStackSize = definition.Body.MaxStackSize };
        foreach (var local in definition.Body.Variables)
            clone.Body.Variables.Add(new VariableDefinition(Substitute(local.VariableType)));

        var instructions = new Dictionary<Instruction, Instruction>();
        foreach (var instruction in definition.Body.Instructions)
        {
            var copy = Instruction.Create(OpCodes.Nop);
            copy.OpCode = instruction.OpCode;
            copy.Offset = instruction.Offset;
            instructions.Add(instruction, copy);
            clone.Body.Instructions.Add(copy);
        }
        foreach (var instruction in definition.Body.Instructions)
            instructions[instruction].Operand = instruction.Operand switch
            {
                Instruction target => instructions[target],
                Instruction[] targets => targets.Select(t => instructions[t]).ToArray(),
                ParameterDefinition parameter => parameter.Index < 0 ? clone.Body.ThisParameter : clone.Parameters[parameter.Index],
                VariableDefinition local => clone.Body.Variables[local.Index],
                TypeReference type => Substitute(type),
                MethodReference method => SubstituteMethod(method),
                _ => instruction.Operand
            };

        instances.Add(key, clone);
        origins.Add(clone, new(definition.FullName, reference.GenericArguments.Select(t => t.FullName).ToArray()));
        return clone;
    }
}
