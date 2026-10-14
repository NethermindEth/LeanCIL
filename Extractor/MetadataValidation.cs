using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class MetadataValidation
{
    internal static bool IsAggregate(TypeReference type, ModuleDefinition module) =>
        type is not TypeSpecification && type.Scope == module && type.IsValueType;

    internal static int PrimitiveWidth(TypeReference type) => type.FullName switch
    {
        "System.Byte" or "System.SByte" or "System.Boolean" => 1,
        "System.Int16" or "System.UInt16" or "System.Char" => 2,
        "System.Int32" or "System.UInt32" => 4,
        "System.Int64" or "System.UInt64" => 8,
        _ => throw new InvalidDataException($"Unsupported field type: {type.FullName}")
    };

    // Explicit, reference-free layouts avoid guessing runtime packing or GC layout.
    internal static int Layout(TypeReference reference, ModuleDefinition module)
    {
        TypeDefinition type = reference.Resolve() ?? throw new InvalidDataException("Unresolved aggregate");
        if (reference.Scope != module || type.Module != module || !reference.IsValueType ||
            !type.IsValueType || !RuntimeModels.HasRuntimeValueTypeBase(type) || !type.IsExplicitLayout ||
            type.ClassSize <= 0 || type.ClassSize > 65536 || type.HasGenericParameters ||
            type.Methods.Any(m => m.IsConstructor && m.IsStatic) ||
            module.GetTypes().Count(t => t.FullName == type.FullName) != 1)
            throw new InvalidDataException($"Unsupported aggregate layout: {reference.FullName}");
        foreach (FieldDefinition field in type.Fields.Where(f => !f.IsStatic))
        {
            RuntimeModels.ValidateTypeIdentity(field.FieldType, module);
            int width = PrimitiveWidth(field.FieldType);
            if (field.Offset < 0 || (long)field.Offset + width > type.ClassSize ||
                type.Fields.Count(f => f.Name == field.Name) != 1)
                throw new InvalidDataException($"Invalid field layout: {field.FullName}");
        }
        return type.ClassSize;
    }

    internal static void Type(TypeReference type, ModuleDefinition module, bool returns = false)
    {
        if (type is ByReferenceType byRef)
        {
            if (byRef.ElementType is ByReferenceType)
                throw new InvalidDataException("Unsupported nested managed reference");
            Type(byRef.ElementType, module);
            return;
        }
        if (IsAggregate(type, module)) { Layout(type, module); return; }
        if (!(returns && type.FullName == "System.Void") && type.FullName is not
            ("System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or "System.Byte" or "System.Boolean" or
            "System.SByte" or "System.Int16" or "System.UInt16" or "System.Char") &&
            !(type is GenericInstanceType && type.FullName.StartsWith("System.Runtime.Intrinsics.Vector", StringComparison.Ordinal) && RuntimeModels.SupportedType(type)))
            throw new InvalidDataException($"Unsupported type: {type.FullName}");
        RuntimeModels.ValidateTypeIdentity(type, module);
    }

    internal static MethodDefinition[] Validate(ModuleDefinition module, string assemblyIdentity, string entrySignature, FeatureProfile profile)
    {
        profile.Validate();
        string? Attribute(string name) => module.Assembly.CustomAttributes
            .SingleOrDefault(a => a.AttributeType.FullName == name)?.ConstructorArguments.Single().Value as string;
        if ((module.Assembly.Name.FullName != assemblyIdentity && module.Assembly.Name.Name != assemblyIdentity) ||
            Attribute("System.Runtime.Versioning.TargetFrameworkAttribute") != ".NETCoreApp,Version=v10.0" ||
            Attribute("System.Reflection.AssemblyConfigurationAttribute") != "Release" ||
            (module.Attributes & ModuleAttributes.ILOnly) == 0 ||
            (module.Attributes & ModuleAttributes.Required32Bit) != 0)
            throw new InvalidDataException("Unsupported assembly identity, target framework or build configuration");
        MethodDefinition entry = MethodSelector.Resolve(module, entrySignature);
        Dictionary<MethodDefinition, int> state = [];
        List<MethodDefinition> ordered = [];
        void Visit(MethodDefinition method)
        {
            if (state.TryGetValue(method, out int visited))
            {
                if (visited == 1) throw new InvalidDataException("Recursive managed dependency");
                return;
            }
            if (method.Module != module || !method.IsStatic || method.ExplicitThis ||
                method.CallingConvention != MethodCallingConvention.Default || !method.HasBody ||
                method.IsPInvokeImpl ||
                (method.ImplAttributes & (MethodImplAttributes.CodeTypeMask | MethodImplAttributes.ManagedMask |
                    MethodImplAttributes.Synchronized | MethodImplAttributes.InternalCall | MethodImplAttributes.ForwardRef)) != 0 ||
                method.HasGenericParameters || method.DeclaringType.HasGenericParameters ||
                method.Body.Instructions.Count == 0 || method.Body.ExceptionHandlers.Count != 0 ||
                method.DeclaringType.Methods.Any(m => m.IsConstructor && m.IsStatic))
                throw new InvalidDataException($"Unsupported method metadata or static initialisation: {method.FullName}");
            Type(method.ReturnType, module, returns: true);
            foreach (ParameterDefinition parameter in method.Parameters) Type(parameter.ParameterType, module);
            foreach (VariableDefinition local in method.Body.Variables) Type(local.VariableType, module);
            state[method] = 1;
            foreach (Instruction instruction in Reachability.Analyze(method, profile))
            {
                if (instruction.OpCode.Code != Code.Call || instruction.Operand is not MethodReference reference ||
                    InstructionTranslation.RuntimeModel(reference, profile) is not null) continue;
                if (reference is GenericInstanceMethod || reference.HasThis || reference.ExplicitThis ||
                    reference.CallingConvention != MethodCallingConvention.Default)
                    throw new InvalidDataException("Unsupported call signature");
                MethodDefinition callee = reference.Resolve() ?? throw new InvalidDataException("Unresolved call");
                if (callee.Module != module || reference.FullName != callee.FullName)
                    throw new InvalidDataException("External or mismatched managed dependency");
                Visit(callee);
            }
            state[method] = 2;
            ordered.Add(method);
        }
        Visit(entry);
        ordered.Reverse();
        // Validate translation before producing any artifact.
        for (int i = 0; i < ordered.Count; i++)
            foreach (Instruction instruction in Reachability.Analyze(ordered[i], profile))
                InstructionTranslation.Translate(instruction, ordered[i], ordered.ToArray(), i, profile);
        return ordered.ToArray();
    }
}
