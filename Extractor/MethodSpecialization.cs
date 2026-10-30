using System.Runtime.CompilerServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Specialization substitutes metadata types; it never rewrites the compiled assembly.
internal sealed class MethodSpecialization(ModuleDefinition module, string architecture = "scalar")
{
    internal sealed record Origin(string Definition, string[] TypeArguments);
    static readonly ConditionalWeakTable<MethodDefinition, Origin> origins = new();
    static readonly ConditionalWeakTable<MethodDefinition, TypeReference[]> typeArguments = new();
    static readonly ConditionalWeakTable<MethodDefinition, TypeReference[]> ownerArguments = new();
    static readonly ConditionalWeakTable<MethodDefinition, MethodDefinition> definitions = new();
    static readonly ConditionalWeakTable<MethodDefinition, TypeReference> declaringTypes = new();
    readonly Dictionary<string, MethodDefinition> instances = new(StringComparer.Ordinal);

    internal static Origin? Source(MethodDefinition method) => origins.TryGetValue(method, out var origin) ? origin : null;

    // Clones keep the definition's instruction order and offsets, so its debug information applies.
    internal static MethodDefinition Definition(MethodDefinition method) => definitions.TryGetValue(method, out var definition) ? definition : method;

    internal static IReadOnlyList<TypeReference> Arguments(MethodDefinition method) =>
        typeArguments.TryGetValue(method, out var arguments) ? arguments : [];

    internal static IReadOnlyList<TypeReference> OwnerArguments(MethodDefinition method) =>
        ownerArguments.TryGetValue(method, out var arguments) ? arguments : [];

    internal static TypeReference DeclaringType(MethodDefinition method) =>
        declaringTypes.TryGetValue(method, out var owner) ? owner : method.DeclaringType;

    internal static string SignatureType(TypeReference type) => type switch
    {
        GenericParameter parameter => $"{parameter.Type}:{parameter.Position}",
        ByReferenceType reference => SignatureType(reference.ElementType) + "&",
        // Other modifiers keep their full spelling below and cannot equal an `in` reference.
        RequiredModifierType modifier when InReferences.Is(modifier) => SignatureType(modifier.ElementType) + " in",
        PointerType pointer => SignatureType(pointer.ElementType) + "*",
        ArrayType { IsVector: true } array => SignatureType(array.ElementType) + "[]",
        GenericInstanceType instance => LayoutEvidence.Identity(instance.ElementType) + "<" +
            string.Join(",", instance.GenericArguments.Select(SignatureType)) + ">",
        FunctionPointerType pointer => $"fn:{pointer.CallingConvention}:{pointer.HasThis}:{pointer.ExplicitThis}:" +
            SignatureType(pointer.ReturnType) + "(" +
            string.Join(",", pointer.Parameters.Select(parameter => SignatureType(parameter.ParameterType))) + ")",
        _ => LayoutEvidence.Identity(type)
    };

    internal MethodDefinition Instantiate(MethodReference reference)
    {
        var definition = reference.Resolve() ?? throw new InvalidDataException($"Unresolved generic method: {reference.FullName}");
        var methodArguments = reference is GenericInstanceMethod genericMethod
            ? genericMethod.GenericArguments.ToArray() : [];
        var declaringArguments = reference.DeclaringType is GenericInstanceType genericOwner
            ? genericOwner.GenericArguments.ToArray() : [];
        var member = reference is GenericInstanceMethod instance ? instance.ElementMethod : reference;
        if (definition.Module != module || reference.HasThis != definition.HasThis ||
            reference.ExplicitThis || methodArguments.Length != definition.GenericParameters.Count ||
            declaringArguments.Length != definition.DeclaringType.GenericParameters.Count ||
            (methodArguments.Length == 0 && declaringArguments.Length == 0) ||
            member.Name != definition.Name || SignatureType(member.ReturnType) != SignatureType(definition.ReturnType) ||
            !member.Parameters.Select(parameter => SignatureType(parameter.ParameterType))
                .SequenceEqual(definition.Parameters.Select(parameter => SignatureType(parameter.ParameterType))) ||
            (declaringArguments.Length != 0 && !definition.IsStatic && !GenericStructs.Is(reference.DeclaringType)) ||
            (definition.IsConstructor && (methodArguments.Length != 0 || definition.IsStatic)) ||
            !definition.HasBody || definition.Body.ExceptionHandlers.Count != 0 ||
            (reference.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default ||
            (definition.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default)
            throw new InvalidDataException($"Unsupported generic method signature or body: {reference.FullName}");

        var arguments = methodArguments.Concat(declaringArguments).ToArray();
        foreach (var argument in arguments)
        {
            if (argument is ByReferenceType or PointerType or GenericParameter)
                throw new InvalidDataException($"Unsupported generic method type argument: {argument.FullName}");
            MetadataValidation.Type(argument, module, architecture: architecture);
        }
        foreach (var (parameter, argument) in definition.GenericParameters
            .Concat(definition.DeclaringType.GenericParameters).Zip(arguments))
        {
            // 0x20 is the .NET allows-ref-struct anti-constraint. Other flags are
            // either reference/variance constraints or unsupported metadata bits.
            var allowed = GenericParameterAttributes.NotNullableValueTypeConstraint |
                GenericParameterAttributes.DefaultConstructorConstraint | (GenericParameterAttributes)0x20;
            if ((parameter.Attributes & ~allowed) != 0)
                throw new InvalidDataException($"Unsupported generic method constraints: {definition.FullName}");
            foreach (var constraint in parameter.Constraints)
            {
                var type = constraint.ConstraintType;
                if (type is RequiredModifierType modifier &&
                    modifier.ModifierType.FullName == "System.Runtime.InteropServices.UnmanagedType" &&
                    RuntimeModels.ExactScope(modifier.ModifierType.Scope, "System.Runtime"))
                    type = modifier.ElementType;
                if (GenericStructs.DirectInterfaceConstraint(type, argument, module))
                    continue;
                if (type.FullName != "System.ValueType" || !RuntimeModels.ExactScope(type.Scope, "System.Runtime"))
                    throw new InvalidDataException($"Unsupported generic method constraints: {definition.FullName}");
                RuntimeModels.ValidateTypeIdentity(type, module, architecture);
            }
        }

        var key = definition.MetadataToken.ToInt32() + ":" + SignatureType(reference.DeclaringType) +
            "<" + string.Join(",", methodArguments.Select(SignatureType)) + ">";
        if (instances.TryGetValue(key, out var existing)) return existing;
        if (instances.Count >= 256)
            throw new InvalidDataException("Generic specialization limit exceeded (possible expanding recursion)");

        TypeReference Substitute(TypeReference type)
        {
            if (type is GenericParameter parameter)
            {
                var expectedOwner = parameter.Type == GenericParameterType.Method
                    ? (IGenericParameterProvider)definition : definition.DeclaringType;
                if (parameter.Owner != expectedOwner)
                    throw new InvalidDataException("Foreign generic parameter owner in specialized body");
                var supplied = parameter.Type == GenericParameterType.Method ? methodArguments : declaringArguments;
                return parameter.Position >= 0 && parameter.Position < supplied.Length
                    ? supplied[parameter.Position]
                    : throw new InvalidDataException("Malformed generic method type parameter");
            }
            if (type is ArrayType { IsVector: true } array) return new ArrayType(Substitute(array.ElementType));
            if (type is FunctionPointerType pointerSignature)
            {
                var result = new FunctionPointerType
                {
                    ReturnType = Substitute(pointerSignature.ReturnType),
                    CallingConvention = pointerSignature.CallingConvention,
                    HasThis = pointerSignature.HasThis,
                    ExplicitThis = pointerSignature.ExplicitThis
                };
                foreach (var argument in pointerSignature.Parameters)
                    result.Parameters.Add(new ParameterDefinition(Substitute(argument.ParameterType)));
                return result;
            }
            return TypeSubstitution.Components(type, Substitute);
        }

        MethodReference SubstituteMethod(MethodReference method)
        {
            var member = method is GenericInstanceMethod instance ? instance.ElementMethod : method;
            if (member.DeclaringType is GenericInstanceType)
            {
                var closed = new MethodReference(member.Name, member.ReturnType, Substitute(member.DeclaringType))
                {
                    HasThis = member.HasThis,
                    ExplicitThis = member.ExplicitThis,
                    CallingConvention = member.CallingConvention
                };
                foreach (var parameter in member.Parameters)
                    closed.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
                foreach (var parameter in member.GenericParameters)
                    closed.GenericParameters.Add(new GenericParameter(parameter.Name, closed));
                member = closed;
            }
            if (method is GenericInstanceMethod generic)
            {
                var result = new GenericInstanceMethod(member);
                foreach (var argument in generic.GenericArguments) result.GenericArguments.Add(Substitute(argument));
                return result;
            }
            return member;
        }

        Mono.Cecil.CallSite SubstituteSite(Mono.Cecil.CallSite site)
        {
            var result = new Mono.Cecil.CallSite(Substitute(site.ReturnType))
            {
                CallingConvention = site.CallingConvention,
                HasThis = site.HasThis,
                ExplicitThis = site.ExplicitThis
            };
            foreach (var argument in site.Parameters)
                result.Parameters.Add(new ParameterDefinition(Substitute(argument.ParameterType)));
            return result;
        }

        var clone = new MethodDefinition(definition.IsConstructor ? definition.Name :
            definition.Name + "<" + string.Join(",", arguments.Select(t => t.FullName)) + ">",
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
                FieldReference field => new FieldReference(field.Name, field.FieldType, Substitute(field.DeclaringType)),
                MethodReference method => SubstituteMethod(method),
                Mono.Cecil.CallSite site => SubstituteSite(site),
                _ => instruction.Operand
            };

        instances.Add(key, clone);
        origins.Add(clone, new(definition.FullName, arguments.Select(t => t.FullName).ToArray()));
        typeArguments.Add(clone, arguments);
        ownerArguments.Add(clone, declaringArguments);
        declaringTypes.Add(clone, reference.DeclaringType);
        definitions.Add(clone, definition);
        return clone;
    }
}
