using System.Globalization;
using System.Text;
using System.Text.Json;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal sealed record ContractType(string Kind, string Scope, string Name, ContractType? Element = null)
{
    internal static ContractType Read(TypeReference type)
    {
        ContractMethodMetadata.RejectModifiers(type);
        if (type is ByReferenceType reference) return new("byref", "", "", Read(reference.ElementType));
        if (type is TypeSpecification or GenericParameter)
            throw new InvalidDataException("Unsupported imported signature type: " + type.FullName);
        if (type.MetadataType == MetadataType.Void) RuntimeModels.ValidateTypeIdentity(type, type.Module);
        return type.MetadataType == MetadataType.Void ? new("void", "", "") :
            new("atom", LayoutEvidence.Scope(type), type.FullName);
    }

    internal string Lean => Kind switch
    {
        "void" => ".void",
        "atom" => ".atom " + JsonSerializer.Serialize(Scope) + " " + JsonSerializer.Serialize(Name),
        "byref" when Element is not null => ".byref (" + Element.Lean + ")",
        _ => throw new InvalidDataException("Invalid imported type metadata.")
    };
}

internal sealed record ContractMethodSignature(ContractType Owner, string Name, ContractType[] Arguments,
    ContractType ReturnType, ContractType[] Parameters, int[] ParameterAttributes)
{
    internal static ContractMethodSignature Of(MethodReference reference, MethodDefinition definition,
        IReadOnlyList<TypeReference> arguments) => new(ContractType.Read(reference.DeclaringType), definition.Name,
        arguments.Select(ContractType.Read).ToArray(), ContractType.Read(CallReturnType.Resolve(reference)),
        CallReturnType.Parameters(reference).Select(ContractType.Read).ToArray(),
        definition.Parameters.Select(parameter => (int)parameter.Attributes).ToArray());

    internal string Lean => "{ owner := " + Owner.Lean + ", name := " + JsonSerializer.Serialize(Name) +
        ", arguments := [" + string.Join(", ", Arguments.Select(type => type.Lean)) + "]" +
        ", returnType := " + ReturnType.Lean + ", parameters := [" +
        string.Join(", ", Parameters.Select(type => type.Lean)) + "] }";
}

internal static class ContractMethodMetadata
{
    internal static void ValidatePublished(ContractMethodSignature signature, string[] arguments, int count, bool returned)
    {
        if (signature.Owner is null || signature.Owner.Kind != "atom" || string.IsNullOrWhiteSpace(signature.Name) ||
            signature.Arguments is null || signature.Parameters is null || signature.ReturnType is null ||
            signature.ParameterAttributes is null || signature.Parameters.Length != count ||
            signature.ParameterAttributes.Length != count || signature.Arguments.Length != arguments.Length ||
            (signature.ReturnType.Kind != "void") != returned || arguments.Any(string.IsNullOrWhiteSpace))
            throw new InvalidDataException("Invalid typed contract signature.");
        foreach (ContractType type in signature.Parameters.Concat(signature.Arguments).Append(signature.Owner).Append(signature.ReturnType))
            ValidateType(type);
        for (int index = 0; index < arguments.Length; index++)
            if (signature.Arguments[index].Kind != "atom" || signature.Arguments[index].Name != arguments[index])
                throw new InvalidDataException("Contract argument names differ from their scoped signature.");
    }

    internal static void ValidateType(ContractType type)
    {
        if (type is null || type.Kind is not ("atom" or "byref" or "void") ||
            (type.Kind == "atom" && (string.IsNullOrWhiteSpace(type.Scope) || string.IsNullOrWhiteSpace(type.Name) || type.Element is not null)) ||
            (type.Kind != "atom" && (type.Scope != "" || type.Name != "")) ||
            (type.Kind == "void" && type.Element is not null) || (type.Kind == "byref" && type.Element is null))
            throw new InvalidDataException("Invalid imported type metadata.");
        if (type.Element is not null) ValidateType(type.Element);
    }

    internal sealed record Selection(MethodDefinition Definition, MethodDefinition Closed, MethodReference Reference,
        TypeReference[] Arguments, string Identity)
    {
        internal ContractMethodSignature Signature => ContractMethodSignature.Of(Reference, Definition, Arguments);
        internal string[] ArgumentNames => Arguments.Select(type => type.FullName).ToArray();
    }

    internal static void RejectModifiers(TypeReference type)
    {
        if (type is RequiredModifierType or OptionalModifierType)
            throw new InvalidDataException("Custom modifiers are unsupported in typed contract signatures: " + type.FullName);
        if (type is GenericInstanceType generic)
            foreach (TypeReference argument in generic.GenericArguments) RejectModifiers(argument);
        if (type is TypeSpecification specification) RejectModifiers(specification.ElementType);
    }

    internal static void RejectModifiers(MethodReference method)
    {
        RejectModifiers(method.DeclaringType);
        RejectModifiers(method.ReturnType);
        foreach (ParameterDefinition parameter in method.Parameters) RejectModifiers(parameter.ParameterType);
        if (method is GenericInstanceMethod generic)
            foreach (TypeReference argument in generic.GenericArguments) RejectModifiers(argument);
    }

    internal static bool Primitive(TypeReference type) => type is not TypeSpecification &&
        RuntimeModels.ExactScope(type.Scope, "System.Runtime") && type.IsValueType && type.FullName is
        "System.SByte" or "System.Byte" or "System.Boolean" or "System.Int16" or "System.UInt16" or
        "System.Char" or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or
        "System.IntPtr" or "System.UIntPtr";

    static TypeReference Primitive(ModuleDefinition module, string name) => name switch
    {
        "System.SByte" => module.TypeSystem.SByte, "System.Byte" => module.TypeSystem.Byte,
        "System.Boolean" => module.TypeSystem.Boolean, "System.Int16" => module.TypeSystem.Int16,
        "System.UInt16" => module.TypeSystem.UInt16, "System.Char" => module.TypeSystem.Char,
        "System.Int32" => module.TypeSystem.Int32, "System.UInt32" => module.TypeSystem.UInt32,
        "System.Int64" => module.TypeSystem.Int64, "System.UInt64" => module.TypeSystem.UInt64,
        "System.IntPtr" => module.TypeSystem.IntPtr, "System.UIntPtr" => module.TypeSystem.UIntPtr,
        _ => throw new InvalidDataException("Closed contract type arguments require a primitive integer type: " + name)
    };

    internal static Selection Select(ModuleDefinition module, string selector, string[] arguments, string architecture)
    {
        MethodDefinition definition = MethodSelector.Resolve(module, selector);
        TypeReference[] types = arguments.Select(name => Primitive(module, name)).ToArray();
        return Instantiate(definition, types, architecture);
    }

    static Selection Instantiate(MethodDefinition definition, TypeReference[] arguments, string architecture)
    {
        RejectModifiers(definition);
        if (definition.DeclaringType.HasGenericParameters || definition.GenericParameters.Count != arguments.Length)
            throw new InvalidDataException("Contract method requires an exact closed generic instantiation.");
        if (arguments.Any(type => !Primitive(type)))
            throw new InvalidDataException("Contract type arguments require exact scoped primitive integers.");
        if (arguments.Length == 0)
            return new(definition, definition, definition, [], definition.Module.Assembly.Name.FullName + "::" + definition.FullName);
        GenericInstanceMethod reference = new(definition);
        foreach (TypeReference argument in arguments) reference.GenericArguments.Add(argument);
        MethodDefinition closed = new MethodSpecialization(definition.Module, architecture).Instantiate(reference);
        // Scalar certificates read the closed return and parameter types from the identity.
        // Keep the scoped instantiation key inside the method name, before the parameter list.
        StringBuilder identity = new(definition.Module.Assembly.Name.FullName + "::" + closed.ReturnType.FullName + " " +
            closed.DeclaringType.FullName + "::" + closed.Name + "|arguments|");
        foreach (TypeReference argument in arguments)
        {
            string scoped = OpenType(argument);
            identity.Append(scoped.Length.ToString(CultureInfo.InvariantCulture)).Append(':').Append(scoped);
        }
        identity.Append('(').AppendJoin(',', closed.Parameters.Select(parameter => parameter.ParameterType.FullName)).Append(')');
        return new(definition, closed, reference, arguments, identity.ToString());
    }

    internal static Selection ResolveImported(MethodReference reference, ModuleDefinition selected, string architecture)
    {
        RejectModifiers(reference);
        MethodReference open = reference is GenericInstanceMethod generic ? generic.ElementMethod : reference;
        if (open.DeclaringType is TypeSpecification || open.DeclaringType.HasGenericParameters || open.HasThis || open.ExplicitThis ||
            (open.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default)
            throw new InvalidDataException("Unsupported typed contract declaring type or calling convention.");
        MethodDefinition[] matches = selected.GetTypes().Where(type => type.FullName == open.DeclaringType.FullName)
            .SelectMany(type => type.Methods).Where(method => method.Name == open.Name &&
                method.GenericParameters.Count == open.GenericParameters.Count && SameSignature(method, open)).ToArray();
        if (matches.Length != 1) throw new InvalidDataException("Contract definition not present or ambiguous: " + reference.FullName);
        TypeReference[] arguments = reference is GenericInstanceMethod instance ? instance.GenericArguments.ToArray() : [];
        Selection result = Instantiate(matches[0], arguments, architecture);
        if (OpenType(CallReturnType.Resolve(reference)) != OpenType(result.Closed.ReturnType) ||
            !CallReturnType.Parameters(reference).Select(OpenType).SequenceEqual(result.Closed.Parameters.Select(parameter => OpenType(parameter.ParameterType))))
            throw new InvalidDataException("Contract exact closed signature mismatch.");
        return result;
    }

    static bool SameSignature(MethodDefinition definition, MethodReference reference)
    {
        RejectModifiers(definition);
        return definition.HasThis == reference.HasThis && definition.ExplicitThis == reference.ExplicitThis &&
            definition.CallingConvention == reference.CallingConvention &&
            OpenType(definition.ReturnType) == OpenType(reference.ReturnType) &&
            definition.Parameters.Select(parameter => OpenType(parameter.ParameterType)).SequenceEqual(
                reference.Parameters.Select(parameter => OpenType(parameter.ParameterType)), StringComparer.Ordinal);
    }

    static string Part(string value) => value.Length.ToString(CultureInfo.InvariantCulture) + ":" + value;

    internal static string OpenType(TypeReference type)
    {
        RejectModifiers(type);
        return type switch
        {
            GenericParameter parameter => (parameter.Type == GenericParameterType.Method ? "method:" : "type:") + parameter.Position,
            ByReferenceType reference => "byref:" + Part(OpenType(reference.ElementType)),
            TypeSpecification => throw new InvalidDataException("Unsupported imported signature type: " + type.FullName),
            _ => "atom:" + Part(LayoutEvidence.Scope(type)) + Part(type.FullName) + (type.IsValueType ? "v" : "r")
        };
    }
}
