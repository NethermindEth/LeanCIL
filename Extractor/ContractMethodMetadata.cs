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
    // Exception data naming the shape a rejection found, so a report can drop its restatements.
    internal const string ModifiedTypeKey = "Nethermind.LeanCIL.ModifiedType";
    internal const string InstantiationKey = "Nethermind.LeanCIL.Instantiation";

    static InvalidDataException Shape(string message, string key, string value)
    {
        InvalidDataException error = new(message);
        error.Data[key] = value;
        return error;
    }

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
        // Importers bind only primitive arguments, so an entry closed over its own value type cannot be published.
        if (!arguments.All(PrimitiveName))
            throw new InvalidDataException("Contract type arguments require exact scoped primitive integers.");
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
            throw Shape("Custom modifiers are unsupported in typed contract signatures: " + type.FullName,
                ModifiedTypeKey, type.FullName);
        if (type is GenericInstanceType generic)
            foreach (TypeReference argument in generic.GenericArguments) RejectModifiers(argument);
        if (type is TypeSpecification specification) RejectModifiers(specification.ElementType);
    }

    // Imported and exported signatures admit no modifier: their methods are static and non-virtual.
    internal static void RejectModifiers(MethodReference method) => RejectModifiers(method, inParameters: false);

    // A selected method may carry `modreq(InAttribute)` on a by-reference parameter and nowhere else.
    static void RejectModifiers(MethodReference method, bool inParameters)
    {
        RejectModifiers(method.DeclaringType);
        RejectModifiers(method.ReturnType);
        foreach (ParameterDefinition parameter in method.Parameters)
        {
            if (inParameters && InReferences.Is(parameter.ParameterType)) continue;
            if (inParameters && InReferences.Modified(parameter.ParameterType))
                throw Shape("Custom modifiers are unsupported in method signatures, except " +
                    "System.Runtime's modreq(InAttribute) directly on a by-reference parameter: " +
                    parameter.ParameterType.FullName, ModifiedTypeKey, parameter.ParameterType.FullName);
            RejectModifiers(parameter.ParameterType);
        }
        if (method is GenericInstanceMethod generic)
            foreach (TypeReference argument in generic.GenericArguments) RejectModifiers(argument);
    }

    internal static bool Primitive(TypeReference type) => type is not TypeSpecification &&
        RuntimeModels.ExactScope(type.Scope, "System.Runtime") && type.IsValueType && PrimitiveName(type.FullName);

    static bool PrimitiveName(string name) => name is
        "System.SByte" or "System.Byte" or "System.Boolean" or "System.Int16" or "System.UInt16" or
        "System.Char" or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or
        "System.IntPtr" or "System.UIntPtr";

    // An entry may also close over a non-generic value type of its own module; specialization validates its layout.
    static TypeReference EntryArgument(ModuleDefinition module, string name)
    {
        if (Primitive(module, name) is { } primitive) return primitive;
        // `Type, Assembly` names a value type of a pinned reference by simple or full assembly name.
        int separator = name.IndexOf(", ", StringComparison.Ordinal);
        if (separator > 0)
        {
            string assembly = name[(separator + 2)..];
            var owner = PinnedAssemblies.Active?.References.Select(reference => reference.Module)
                .Where(candidate => candidate.Assembly.Name.Name == assembly ||
                    candidate.Assembly.Name.FullName == assembly).ToArray() ?? [];
            if (owner.Length != 1)
                throw new InvalidDataException(
                    "Closed entry type argument names no single pinned --reference assembly: " + name);
            if (owner[0].GetType(name[..separator]) is not
                { IsValueType: true, HasGenericParameters: false } referenced)
                throw new InvalidDataException("Closed entry type argument is not a non-generic value type of " +
                    owner[0].Assembly.Name.FullName + ": " + name);
            return module.ImportReference(referenced);
        }
        return module.GetType(name) is { IsValueType: true, HasGenericParameters: false } local
            ? local : throw new InvalidDataException(
                "Closed entry type arguments require a primitive integer, a non-generic value type " +
                "of the selected module, or `Type, Assembly` for a pinned reference: " + name);
    }

    static TypeReference? Primitive(ModuleDefinition module, string name) => name switch
    {
        "System.SByte" => module.TypeSystem.SByte, "System.Byte" => module.TypeSystem.Byte,
        "System.Boolean" => module.TypeSystem.Boolean, "System.Int16" => module.TypeSystem.Int16,
        "System.UInt16" => module.TypeSystem.UInt16, "System.Char" => module.TypeSystem.Char,
        "System.Int32" => module.TypeSystem.Int32, "System.UInt32" => module.TypeSystem.UInt32,
        "System.Int64" => module.TypeSystem.Int64, "System.UInt64" => module.TypeSystem.UInt64,
        "System.IntPtr" => module.TypeSystem.IntPtr, "System.UIntPtr" => module.TypeSystem.UIntPtr,
        _ => null
    };

    internal static Selection Select(ModuleDefinition module, string selector, string[] arguments, string architecture)
    {
        (MethodDefinition definition, TypeReference[] types) = Resolve(module, selector, arguments);
        return Entry(definition, types, architecture);
    }

    /// <summary>The method a selector names and its closed type arguments, before its shape is checked.</summary>
    internal static (MethodDefinition Definition, TypeReference[] Arguments) Resolve(ModuleDefinition module,
        string selector, string[] arguments) =>
        (MethodSelector.Resolve(module, selector), arguments.Select(name => EntryArgument(module, name)).ToArray());

    /// <summary>The resolved method closed as an entry; rejects shapes no entry may have.</summary>
    internal static Selection Entry(MethodDefinition definition, TypeReference[] arguments, string architecture) =>
        Instantiate(definition, arguments, architecture, entry: true);

    static Selection Instantiate(MethodDefinition definition, TypeReference[] arguments, string architecture,
        bool entry = false)
    {
        RejectModifiers(definition, inParameters: true);
        InReferences.RejectTwins(definition);
        // An entry may be a static method of a generic class: method arguments come first, then the owner's.
        int ownerArity = definition.DeclaringType.GenericParameters.Count;
        if ((ownerArity != 0 && (!entry || !definition.IsStatic)) ||
            definition.GenericParameters.Count + ownerArity != arguments.Length)
            throw Shape("Contract method requires an exact closed generic instantiation." +
                (ownerArity == 0 ? "" : $"\n  Pass {definition.GenericParameters.Count} method type argument(s) " +
                    $"followed by {ownerArity} for {definition.DeclaringType.FullName}; only static methods " +
                    "of a generic type can be an entry."), InstantiationKey, definition.FullName);
        // Imported calls bind across assemblies, so only an entry may close over its own module's value types.
        if (arguments.Any(type => !Primitive(type) && !(entry && type.IsValueType &&
                (type.Module == definition.Module || PinnedAssemblies.Active?.ModuleOf(type) is not null))))
            throw new InvalidDataException("Contract type arguments require exact scoped primitive integers.");
        if (arguments.Length == 0)
            return new(definition, definition, definition, [], definition.Module.Assembly.Name.FullName + "::" + definition.FullName);
        MethodReference reference = Closed(definition, arguments);
        MethodDefinition closed = new MethodSpecialization(definition.Module, architecture).Instantiate(reference);
        // Scalar certificates read the closed return and parameter types from the identity.
        // Keep definition and scoped argument keys before the parameter list.
        string definitionHash = ContractInterface.Hash(Encoding.UTF8.GetBytes(DefinitionKey(definition, entry)));
        StringBuilder identity = new(definition.Module.Assembly.Name.FullName + "::" + closed.ReturnType.FullName + " " +
            closed.DeclaringType.FullName + "::" + closed.Name + "|definition|" + definitionHash + "|arguments|");
        foreach (TypeReference argument in arguments)
        {
            string scoped = OpenType(argument);
            identity.Append(scoped.Length.ToString(CultureInfo.InvariantCulture)).Append(':').Append(scoped);
        }
        identity.Append('(').AppendJoin(',', closed.Parameters.Select(parameter => parameter.ParameterType.FullName)).Append(')');
        return new(definition, closed, reference, arguments, identity.ToString());
    }

    // The closed reference a call site would spell: the owner closed over the trailing arguments.
    static MethodReference Closed(MethodDefinition definition, TypeReference[] arguments)
    {
        int methodArity = definition.GenericParameters.Count;
        MethodReference member = definition;
        if (definition.DeclaringType.HasGenericParameters)
        {
            GenericInstanceType owner = new(definition.DeclaringType);
            foreach (TypeReference argument in arguments.Skip(methodArity)) owner.GenericArguments.Add(argument);
            member = new MethodReference(definition.Name, definition.ReturnType, owner)
            {
                HasThis = definition.HasThis, ExplicitThis = definition.ExplicitThis,
                CallingConvention = definition.CallingConvention
            };
            foreach (ParameterDefinition parameter in definition.Parameters)
                member.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
            foreach (GenericParameter parameter in definition.GenericParameters)
                member.GenericParameters.Add(new GenericParameter(parameter.Name, member));
        }
        if (methodArity == 0) return member;
        GenericInstanceMethod generic = new(member);
        foreach (TypeReference argument in arguments.Take(methodArity)) generic.GenericArguments.Add(argument);
        return generic;
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

    static string DefinitionKey(MethodDefinition definition, bool entry)
    {
        Func<TypeReference, string> parameterKey = entry ? EntryParameter : OpenParameter;
        StringBuilder key = new("contract-definition-v1:");
        key.Append(Part(OpenType(definition.DeclaringType))).Append(Part(definition.Name))
            .Append(Part(definition.GenericParameters.Count.ToString(CultureInfo.InvariantCulture)))
            .Append(Part(((byte)definition.CallingConvention).ToString(CultureInfo.InvariantCulture)))
            .Append(Part(definition.HasThis ? "1" : "0")).Append(Part(definition.ExplicitThis ? "1" : "0"))
            .Append(Part(OpenType(definition.ReturnType)))
            .Append(Part(definition.Parameters.Count.ToString(CultureInfo.InvariantCulture)));
        foreach (ParameterDefinition parameter in definition.Parameters)
            key.Append(Part(parameterKey(parameter.ParameterType)));
        return key.ToString();
    }

    static string Part(string value) => value.Length.ToString(CultureInfo.InvariantCulture) + ":" + value;

    // The `in:` tag keeps an `in` reference distinct from a plain one; plain parameters keep their encoding.
    static string OpenParameter(TypeReference type) =>
        InReferences.Unwrap(type) is { } reference ? "in:" + Part(OpenType(reference)) : OpenType(type);

    // An entry parameter may also be a vector or pointer over a managed function pointer, the
    // handler-table shapes; imported signatures keep the stricter encoding below.
    static string EntryParameter(TypeReference type) =>
        InReferences.Unwrap(type) is { } reference ? "in:" + Part(EntryType(reference)) : EntryType(type);

    static string EntryType(TypeReference type)
    {
        RejectModifiers(type);
        return type switch
        {
            ByReferenceType reference => "byref:" + Part(EntryType(reference.ElementType)),
            ArrayType { IsVector: true } array => "vector:" + Part(EntryType(array.ElementType)),
            PointerType pointer => "pointer:" + Part(EntryType(pointer.ElementType)),
            FunctionPointerType callable when !callable.HasThis && !callable.ExplicitThis &&
                callable.CallingConvention == MethodCallingConvention.Default =>
                "managed:" + Part(EntryType(callable.ReturnType)) +
                Part(callable.Parameters.Count.ToString(CultureInfo.InvariantCulture)) +
                string.Concat(callable.Parameters.Select(parameter => Part(EntryType(parameter.ParameterType)))),
            FunctionPointerType => throw new InvalidDataException(
                "Unsupported entry function pointer calling convention: " + type.FullName),
            _ => OpenType(type)
        };
    }

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
