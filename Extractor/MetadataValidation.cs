using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class MetadataValidation
{
    static string ScopeName(IMetadataScope scope) => scope switch
    {
        AssemblyNameReference assembly => assembly.Name,
        ModuleDefinition module => module.Assembly?.Name.Name ?? module.Name,
        _ => scope.Name
    };

    static InvalidDataException Call(string reason, MethodReference reference, MethodDefinition caller,
        Instruction instruction, string? detail = null, Exception? inner = null) =>
        Rejections.Tag(Rejection.Call, new InvalidDataException(
            $"{reason}: {reference.FullName}\n  Caller: {caller.FullName} at IL_{instruction.Offset:x4}" +
            (detail is null ? "" : "\n  " + detail), inner));

    // Names the method whose own metadata or body failed validation.
    static T InMethod<T>(MethodDefinition method, Func<T> validate)
    {
        try { return validate(); }
        catch (InvalidDataException error) when (Rejections.Of(error) is null)
        {
            throw new InvalidDataException($"{error.Message}\n  Method: {method.FullName}", error);
        }
    }

    internal static bool IsAggregate(TypeReference type, ModuleDefinition module) =>
        type is not TypeSpecification && type.Scope == module && type.IsValueType && !EnumTypes.IsEnum(type);

    internal static int PrimitiveWidth(TypeReference type) => EnumTypes.Storage(type).FullName switch
    {
        "System.Byte" or "System.SByte" or "System.Boolean" => 1,
        "System.Int16" or "System.UInt16" or "System.Char" => 2,
        "System.Int32" or "System.UInt32" => 4,
        // Every admitted profile is validated as 64-bit before type/layout validation.
        "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" => 8,
        _ => throw new InvalidDataException($"Unsupported field type: {type.FullName}")
    };

    internal sealed record AggregateInfo(int Size, int Alignment, IReadOnlyDictionary<string, int> Offsets);

    internal static int Layout(TypeReference reference, ModuleDefinition module) => AggregateLayout(reference, module).Size;

    internal static int FieldSize(TypeReference type, ModuleDefinition module) =>
        IsAggregate(type, module) ? Layout(type, module) : PrimitiveWidth(type);

    internal static int FieldOffset(FieldDefinition field, ModuleDefinition module) =>
        AggregateLayout(field.DeclaringType, module).Offsets[field.FullName];

    // Managed layout for primitive, reference-free fields on the admitted 64-bit
    // CoreCLR targets. This is not interop marshalling layout (notably for bool).
    internal static AggregateInfo AggregateLayout(TypeReference reference, ModuleDefinition module)
        => AggregateLayout(reference, module, [], new Dictionary<string, AggregateInfo>());

    static AggregateInfo AggregateLayout(TypeReference reference, ModuleDefinition module,
        HashSet<string> active, Dictionary<string, AggregateInfo> layouts)
    {
        var type = reference.Resolve() ?? throw new InvalidDataException("Unresolved aggregate");
        if (reference.Scope != module || type.Module != module || !reference.IsValueType ||
            !type.IsValueType || !RuntimeModels.HasRuntimeValueTypeBase(type) ||
            !(type.IsExplicitLayout || type.IsSequentialLayout) || type.HasGenericParameters ||
            type.ClassSize is < -1 or > 65536 || (type.IsExplicitLayout && type.ClassSize <= 0) ||
            type.CustomAttributes.Any(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.InlineArrayAttribute") ||
            module.GetTypes().Count(t => t.FullName == type.FullName) != 1)
            throw new InvalidDataException($"Unsupported aggregate layout: {reference.FullName}");

        if (layouts.TryGetValue(type.FullName, out var cached)) return cached;
        if (active.Count >= 128 || !active.Add(type.FullName))
            throw new InvalidDataException($"Recursive or excessively nested aggregate layout: {reference.FullName}");

        var packing = type.PackingSize;
        if (packing is not (-1 or 0 or 1 or 2 or 4 or 8 or 16 or 32 or 64 or 128))
            throw new InvalidDataException($"Invalid aggregate packing: {reference.FullName}");
        var pack = packing <= 0 ? 8 : packing;
        var offsets = new Dictionary<string, int>();
        var end = 0;
        var alignment = 1;
        foreach (var field in type.Fields.Where(f => !f.IsStatic))
        {
            if (field.FieldType is TypeSpecification)
                throw new InvalidDataException($"Unsupported field type: {field.FieldType.FullName}");
            var nested = IsAggregate(field.FieldType, module)
                ? AggregateLayout(field.FieldType, module, active, layouts) : null;
            var width = nested?.Size ?? PrimitiveWidth(field.FieldType);
            if (nested is null) RuntimeModels.ValidateTypeIdentity(field.FieldType, module);
            var fieldAlignment = Math.Min(pack, nested?.Alignment ?? width);
            alignment = Math.Max(alignment, fieldAlignment);
            var offset = type.IsExplicitLayout ? field.Offset : (end + fieldAlignment - 1) / fieldAlignment * fieldAlignment;
            if (offset < 0 || offset > 65536 - width ||
                (type.IsExplicitLayout && offset + width > type.ClassSize) ||
                (type.IsSequentialLayout && field.Offset >= 0) || type.Fields.Count(f => f.Name == field.Name) != 1)
                throw new InvalidDataException($"Invalid field layout: {field.FullName}");
            offsets.Add(field.FullName, offset);
            end = Math.Max(end, offset + width);
        }

        // An explicit metadata size suppresses final alignment rounding in CoreCLR.
        // A smaller declared size cannot truncate fields; empty value types occupy one byte.
        var size = type.ClassSize > 0 ? Math.Max(end, type.ClassSize) : (end + alignment - 1) / alignment * alignment;
        size = Math.Max(1, size);
        if (size > 65536) throw new InvalidDataException($"Unsupported aggregate size: {reference.FullName}");
        active.Remove(type.FullName);
        var result = new AggregateInfo(size, alignment, offsets);
        layouts.Add(type.FullName, result);
        return result;
    }

    internal static void Type(TypeReference type, ModuleDefinition module, bool returns = false, bool span = false)
    {
        if (type is ByReferenceType byRef)
        {
            if (byRef.ElementType is ByReferenceType)
                throw new InvalidDataException("Unsupported nested managed reference");
            Type(byRef.ElementType, module);
            return;
        }
        type = EnumTypes.Storage(type);
        if (IsAggregate(type, module)) { Layout(type, module); return; }
        if (!(returns && type.FullName == "System.Void") && type.FullName is not
            ("System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" or "System.Byte" or "System.Boolean" or
            "System.SByte" or "System.Int16" or "System.UInt16" or "System.Char") &&
            !(type is GenericInstanceType && type.FullName.StartsWith("System.Runtime.Intrinsics.Vector", StringComparison.Ordinal) && RuntimeModels.SupportedType(type)) &&
            // Spans are admitted only as by-value returns and folded receivers; elsewhere their reference field would sit in unmodelled storage.
            !((returns || span) && Spans.Width(type) is not null))
            throw new InvalidDataException($"Unsupported type: {type.FullName}");
        RuntimeModels.ValidateTypeIdentity(type, module);
    }

    internal static MethodDefinition[] Validate(ModuleDefinition module, string assemblyIdentity, string entrySignature, FeatureProfile profile,
        IReadOnlyCollection<string>? initializedTypes = null)
    {
        profile.Validate();
        initializedTypes ??= [];
        foreach (var name in initializedTypes)
            if (!module.GetTypes().Any(t => t.FullName == name && t.Methods.Any(m => m.IsConstructor && m.IsStatic)))
                throw new InvalidDataException($"Initialization assumption must name a type with a static constructor in this assembly: {name}");
        string? Attribute(string name) => module.Assembly.CustomAttributes
            .SingleOrDefault(a => a.AttributeType.FullName == name)?.ConstructorArguments.Single().Value as string;
        if ((module.Assembly.Name.FullName != assemblyIdentity && module.Assembly.Name.Name != assemblyIdentity) ||
            Attribute("System.Runtime.Versioning.TargetFrameworkAttribute") != ".NETCoreApp,Version=v10.0" ||
            Attribute("System.Reflection.AssemblyConfigurationAttribute") != "Release" ||
            (module.Attributes & ModuleAttributes.ILOnly) == 0 ||
            (module.Attributes & ModuleAttributes.Required32Bit) != 0)
            throw new InvalidDataException("Unsupported assembly identity, target framework or build configuration");
        MethodDefinition entry = MethodSelector.Resolve(module, entrySignature);
        var specializations = new MethodSpecialization(module);
        Dictionary<MethodDefinition, int> state = [];
        List<MethodDefinition> ordered = [];
        void Visit(MethodDefinition method)
        {
            if (state.TryGetValue(method, out int visited))
            {
                if (visited == 1) throw new InvalidDataException($"Recursive managed dependency: {method.FullName}");
                return;
            }
            if (method.Module != module || method.IsStatic == method.HasThis || method.ExplicitThis ||
                (!method.IsStatic && !IsAggregate(method.DeclaringType, module)) ||
                method.CallingConvention != MethodCallingConvention.Default || !method.HasBody ||
                method.IsPInvokeImpl ||
                (method.ImplAttributes & (MethodImplAttributes.CodeTypeMask | MethodImplAttributes.ManagedMask |
                    MethodImplAttributes.Synchronized | MethodImplAttributes.InternalCall | MethodImplAttributes.ForwardRef)) != 0 ||
                method.HasGenericParameters || method.DeclaringType.HasGenericParameters ||
                method.Body.Instructions.Count == 0 || method.Body.ExceptionHandlers.Count != 0 ||
                (method.IsConstructor && method.IsStatic) ||
                (method.DeclaringType.Methods.Any(m => m.IsConstructor && m.IsStatic) &&
                    !initializedTypes.Contains(method.DeclaringType.FullName, StringComparer.Ordinal)))
                throw new InvalidDataException($"Unsupported method metadata or static initialisation: {method.FullName}");
            var reachable = InMethod(method, () =>
            {
                if (method.HasThis) Layout(method.DeclaringType, module);
                if (method.IsConstructor && (method.Name != ".ctor" || !method.HasThis || method.ReturnType.MetadataType != MetadataType.Void))
                    throw new InvalidDataException($"Unsupported constructor signature: {method.FullName}");
                Type(method.ReturnType, module, returns: true);
                foreach (ParameterDefinition parameter in method.Parameters) Type(parameter.ParameterType, module);
                var spans = Spans.Analyze(method);
                foreach (VariableDefinition local in method.Body.Variables)
                    Type(local.VariableType, module, span: spans.Locals.Contains(local.Index));
                return Reachability.Analyze(method, profile);
            });
            state[method] = 1;
            void Enter(MethodDefinition callee, MethodReference reference, Instruction instruction)
            {
                if (state.GetValueOrDefault(callee) == 1)
                    throw Call("Recursive managed dependency", reference, method, instruction);
                Visit(callee);
            }
            var typeTests = TypeTests.Analyze(method);
            var throws = Throws.Analyze(method);
            foreach (Instruction instruction in reachable)
            {
                if (instruction.OpCode.Code is not (Code.Call or Code.Newobj) || instruction.Operand is not MethodReference reference ||
                    typeTests.Operands.Contains(instruction) || typeTests.Results.ContainsKey(instruction) || throws.Operands.Contains(instruction) ||
                    InstructionTranslation.RuntimeModel(reference, profile) is not null) continue;
                if (reference is GenericInstanceMethod generic)
                {
                    if (instruction.OpCode.Code != Code.Call)
                        throw Call("Unsupported generic constructor call", reference, method, instruction);
                    MethodDefinition specialized;
                    try { specialized = specializations.Instantiate(generic); }
                    catch (InvalidDataException error) when (Rejections.Of(error) is null)
                    {
                        throw Call("Unsupported generic call", reference, method, instruction, error.Message, error);
                    }
                    instruction.Operand = specialized;
                    Enter(specialized, reference, instruction);
                    continue;
                }
                if (reference.ExplicitThis || reference.CallingConvention != MethodCallingConvention.Default)
                    throw Call("Unsupported call signature", reference, method, instruction,
                        reference.ExplicitThis ? "Explicit this is not supported" : $"Calling convention: {reference.CallingConvention}");
                MethodDefinition callee = reference.Resolve() ??
                    throw Call("Unresolved call", reference, method, instruction, $"Callee scope: {ScopeName(reference.DeclaringType.Scope)}");
                if (callee.Module != module)
                {
                    var assembly = ScopeName(callee.Module);
                    var referenced = ScopeName(reference.DeclaringType.Scope);
                    throw Call("External managed dependency", reference, method, instruction,
                        $"Callee assembly: {assembly}" + (referenced == assembly ? "" : $" (referenced as {referenced})"));
                }
                if (reference.FullName != callee.FullName)
                    throw Call("Mismatched managed dependency", reference, method, instruction,
                        $"FullName differs from the resolved definition {callee.FullName}");
                if (reference.HasThis != callee.HasThis)
                    throw Call("Mismatched managed dependency", reference, method, instruction,
                        $"HasThis differs (reference {reference.HasThis}, definition {callee.HasThis})");
                if (instruction.OpCode.Code == Code.Newobj &&
                    (!callee.IsConstructor || !callee.HasThis || !IsAggregate(callee.DeclaringType, module)))
                    throw Call("Unsupported newobj constructor", reference, method, instruction,
                        "newobj must construct a reference-free struct declared in this assembly");
                Enter(callee, reference, instruction);
            }
            state[method] = 2;
            ordered.Add(method);
        }
        Visit(entry);
        ordered.Reverse();
        // Validate translation before producing any artifact.
        for (int i = 0; i < ordered.Count; i++)
        {
            var index = i;
            InMethod(ordered[index], () =>
            {
                var nativeOperands = NativeOperands.Analyze(ordered[index], profile);
                var parameterHomes = ParameterStorage.Analyze(ordered[index], profile);
                foreach (Instruction instruction in Reachability.Analyze(ordered[index], profile))
                    InstructionTranslation.Translate(instruction, ordered[index], ordered.ToArray(), index, profile, nativeOperands, parameterHomes);
                return 0;
            });
        }
        return ordered.ToArray();
    }
}
