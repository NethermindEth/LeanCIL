using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class MetadataValidation
{
    sealed record RefLikeMetadata(bool IsByRefLike);

    internal static bool IsByRefLike(TypeReference type) =>
        EnumTypes.Cached(type, RefLikeMarker).IsByRefLike;

    static RefLikeMetadata RefLikeMarker(TypeReference type)
    {
        var markers = type.Resolve().CustomAttributes.Where(attribute =>
            attribute.AttributeType.FullName == "System.Runtime.CompilerServices.IsByRefLikeAttribute").ToArray();
        if (markers.Length == 0) return new(false);
        var marker = markers[0];
        var constructor = marker.Constructor;
        if (markers.Length != 1 || marker.AttributeType is TypeSpecification ||
            !RuntimeModels.ExactScope(marker.AttributeType.Scope, "System.Runtime") ||
            constructor.Name != ".ctor" || !constructor.HasThis || constructor.ExplicitThis ||
            constructor.CallingConvention != MethodCallingConvention.Default ||
            constructor.HasGenericParameters || constructor.Parameters.Count != 0 ||
            constructor.ReturnType.MetadataType != MetadataType.Void ||
            marker.HasConstructorArguments || marker.HasFields || marker.HasProperties)
            throw new InvalidDataException("Unsupported byref-like marker: " + type.FullName);
        return new(true);
    }

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
            throw new InvalidDataException($"{error.Message}\n  Method: {method.FullName}{Symbols.Locate(method, error.Message)}", error);
        }
    }

    internal static bool IsAggregate(TypeReference type, ModuleDefinition module) =>
        (type is not TypeSpecification && type.Scope == module && type.IsValueType && !EnumTypes.IsEnum(type)) ||
        ValueTuples.Is(type) || GenericStructs.Is(type);

    internal static int PrimitiveWidth(TypeReference type) => EnumTypes.Storage(type).FullName switch
    {
        "System.Byte" or "System.SByte" or "System.Boolean" => 1,
        "System.Int16" or "System.UInt16" or "System.Char" => 2,
        "System.Int32" or "System.UInt32" => 4,
        // Every admitted profile is validated as 64-bit before type/layout validation.
        "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" => 8,
        _ => throw new InvalidDataException($"Unsupported field type: {type.FullName}")
    };

    internal static int? IntegerVectorWidth(TypeReference type)
    {
        if (type is not GenericInstanceType { GenericArguments.Count: 1 } vector ||
            !RuntimeModels.ExactScope(vector.ElementType.Scope, "System.Runtime.Intrinsics") ||
            !RuntimeModels.ExactScope(vector.GenericArguments[0].Scope, "System.Runtime") ||
            vector.GenericArguments[0].FullName is not ("System.Byte" or "System.Int32" or "System.UInt32" or
                "System.Int64" or "System.UInt64")) return null;
        return vector.ElementType.FullName switch
        {
            "System.Runtime.Intrinsics.Vector128`1" => 16,
            "System.Runtime.Intrinsics.Vector256`1" => 32,
            "System.Runtime.Intrinsics.Vector512`1" => 64,
            _ => null
        };
    }

    // Vector512 field alignment is not established by the admitted aggregate layout model.
    internal static int? VectorFieldWidth(TypeReference type) => IntegerVectorWidth(type) switch
    {
        16 => 16, 32 => 32, _ => null
    };

    internal sealed record AggregateInfo(int Size, int Alignment, IReadOnlyDictionary<string, int> Offsets);

    // Type is the field's type as seen from the owner, after substituting a tuple's type arguments.
    internal sealed record InstanceField(string Name, TypeReference Type, FieldDefinition Definition);

    internal static InstanceField[] Fields(TypeReference owner) => ValueTuples.Is(owner) ? ValueTuples.Fields(owner) :
        [.. (owner.Resolve() ?? throw new InvalidDataException("Unresolved aggregate")).Fields
            .Where(field => !field.IsStatic).Select(field => new InstanceField(field.Name, owner is GenericInstanceType generic
                ? GenericStructs.Substitute(field.FieldType, generic) : field.FieldType, field))];

    internal static InstanceField InstanceFieldOf(FieldReference reference)
    {
        var definition = reference.Resolve() ?? throw new InvalidDataException("Unresolved aggregate field");
        if (definition.IsStatic || reference.Name != definition.Name ||
            MethodSpecialization.SignatureType(reference.FieldType) !=
                MethodSpecialization.SignatureType(definition.FieldType))
            throw new InvalidDataException("Mismatched aggregate field signature: " + reference.FullName);
        return Fields(reference.DeclaringType).Single(field => field.Definition == definition);
    }

    // A read-only validation/emission phase owns its context; metadata rewrites require a new one.
    internal sealed class LayoutContext(ModuleDefinition module, string architecture)
    {
        readonly Dictionary<string, AggregateInfo> validated = new(StringComparer.Ordinal);
        readonly Dictionary<TypeReference, FieldSet> fields = new(ReferenceEqualityComparer.Instance);
        Dictionary<string, int>? typeCounts;
        internal string Architecture => architecture;

        internal void Require(ModuleDefinition owner, string requestedArchitecture)
        {
            if (!ReferenceEquals(module, owner) || architecture != requestedArchitecture)
                throw new InvalidDataException("Layout context does not match module or architecture.");
        }

        sealed class FieldSet(TypeReference owner)
        {
            internal readonly InstanceField[] Fields = MetadataValidation.Fields(owner);
            internal readonly Dictionary<FieldDefinition, int> InstanceIndices =
                new(ReferenceEqualityComparer.Instance);
            internal readonly Dictionary<FieldDefinition, int> AllIndices = new(ReferenceEqualityComparer.Instance);

            internal void Index(TypeReference owner)
            {
                for (var index = 0; index < Fields.Length; index++)
                    InstanceIndices.TryAdd(Fields[index].Definition, index);
                var all = owner.Resolve().Fields;
                for (var index = 0; index < all.Count; index++) AllIndices.TryAdd(all[index], index);
            }
        }

        FieldSet FieldSnapshot(TypeReference owner)
        {
            if (fields.TryGetValue(owner, out var cached)) return cached;
            var snapshot = new FieldSet(owner);
            snapshot.Index(owner);
            fields.Add(owner, snapshot);
            return snapshot;
        }

        internal InstanceField[] Fields(TypeReference owner) => FieldSnapshot(owner).Fields;

        internal int FieldIndex(TypeReference owner, FieldDefinition field, bool includeStatic = false)
        {
            var snapshot = FieldSnapshot(owner);
            return (includeStatic ? snapshot.AllIndices : snapshot.InstanceIndices).GetValueOrDefault(field, -1);
        }

        internal AggregateInfo AggregateLayout(TypeReference reference)
        {
            if (validated.TryGetValue(LayoutEvidence.Identity(reference), out var cached)) return cached;
            typeCounts ??= module.GetTypes().CountBy(type => type.FullName, StringComparer.Ordinal).ToDictionary();
            // A new root keeps its own recursion-depth check, even if a child was validated earlier.
            var layout = MetadataValidation.AggregateLayout(reference, module, architecture, [],
                new Dictionary<string, AggregateInfo>(), typeCounts);
            validated.Add(LayoutEvidence.Identity(reference), layout);
            return layout;
        }

        internal int Size(TypeReference reference) => AggregateLayout(reference).Size;
        internal int FieldSize(TypeReference type) => IsAggregate(type, module)
            ? Size(type) : VectorFieldWidth(type) ?? PrimitiveWidth(type);
        internal int FieldOffset(TypeReference owner, FieldDefinition field) =>
            AggregateLayout(owner).Offsets[field.FullName];
    }

    internal static int Layout(TypeReference reference, ModuleDefinition module, string architecture = "scalar") =>
        AggregateLayout(reference, module, architecture).Size;

    internal static int FieldSize(TypeReference type, ModuleDefinition module, string architecture = "scalar") =>
        IsAggregate(type, module) ? Layout(type, module, architecture) : VectorFieldWidth(type) ?? PrimitiveWidth(type);

    internal static int FieldOffset(TypeReference owner, FieldDefinition field, ModuleDefinition module, string architecture = "scalar") =>
        AggregateLayout(owner, module, architecture).Offsets[field.FullName];

    // Managed layout for primitive, reference-free fields on the admitted 64-bit
    // CoreCLR targets. This is not interop marshalling layout (notably for bool).
    internal static AggregateInfo AggregateLayout(TypeReference reference, ModuleDefinition module, string architecture = "scalar")
        => AggregateLayout(reference, module, architecture, [], new Dictionary<string, AggregateInfo>(),
            module.GetTypes().CountBy(type => type.FullName, StringComparer.Ordinal).ToDictionary());

    static AggregateInfo AggregateLayout(TypeReference reference, ModuleDefinition module, string architecture,
        HashSet<string> active, Dictionary<string, AggregateInfo> layouts, Dictionary<string, int> typeCounts)
    {
        if (ValueTuples.Is(reference)) return TupleLayout(reference, module, architecture);
        var type = reference.Resolve() ?? throw new InvalidDataException("Unresolved aggregate");
        if (reference is GenericInstanceType closed) GenericStructs.Validate(closed);
        if (reference.Scope != module || type.Module != module || !reference.IsValueType ||
            !type.IsValueType || !RuntimeModels.HasRuntimeValueTypeBase(type) ||
            !(type.IsExplicitLayout || type.IsSequentialLayout) || (type.HasGenericParameters && reference is not GenericInstanceType) ||
            type.ClassSize is < -1 or > 65536 || (type.IsExplicitLayout && type.ClassSize <= 0) ||
            type.CustomAttributes.Any(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.InlineArrayAttribute") ||
            typeCounts.GetValueOrDefault(type.FullName) != 1)
            throw new InvalidDataException($"Unsupported aggregate layout: {reference.FullName}");

        if (layouts.TryGetValue(LayoutEvidence.Identity(reference), out var cached)) return cached;
        if (active.Count >= 128 || !active.Add(LayoutEvidence.Identity(reference)))
            throw new InvalidDataException($"Recursive or excessively nested aggregate layout: {reference.FullName}");

        if (reference is GenericInstanceType instance)
            foreach (var argument in instance.GenericArguments)
            {
                if (IsAggregate(argument, module))
                    _ = AggregateLayout(argument, module, architecture, active, layouts, typeCounts);
                else
                {
                    RuntimeModels.ValidateTypeIdentity(argument, module, architecture);
                    _ = VectorFieldWidth(argument) ?? PrimitiveWidth(argument);
                }
            }

        var packing = type.PackingSize;
        if (packing is not (-1 or 0 or 1 or 2 or 4 or 8 or 16 or 32 or 64 or 128))
            throw new InvalidDataException($"Invalid aggregate packing: {reference.FullName}");
        int pack = packing <= 0 ? 64 : packing;
        var fieldCounts = type.Fields.CountBy(field => field.Name, StringComparer.Ordinal).ToDictionary();
        var offsets = new Dictionary<string, int>();
        var end = 0;
        var alignment = 1;
        var byRefLike = IsByRefLike(reference);
        foreach (var actual in Fields(reference))
        {
            var field = actual.Definition;
            var fieldType = actual.Type;
            var aggregate = IsAggregate(fieldType, module);
            if (!byRefLike && aggregate && IsByRefLike(fieldType))
                throw new InvalidDataException("Byref-like field in a heap-storable struct: " + field.FullName);
            int? vectorWidth = VectorFieldWidth(fieldType);
            if (fieldType is TypeSpecification && vectorWidth is null && !aggregate)
                throw new InvalidDataException($"Unsupported field type: {fieldType.FullName}");
            var nested = aggregate
                ? AggregateLayout(fieldType, module, architecture, active, layouts, typeCounts) : null;
            int width = nested?.Size ?? vectorWidth ?? PrimitiveWidth(fieldType);
            if (vectorWidth == 32 && pack > 16 && architecture is not ("x64" or "arm64"))
                throw new InvalidDataException($"Unsupported vector field packing: {field.FullName}");
            if (nested is null) RuntimeModels.ValidateTypeIdentity(fieldType, module, architecture);
            int naturalAlignment = vectorWidth == 32 && architecture == "arm64" ? 16 : width;
            int fieldAlignment = Math.Min(pack, nested?.Alignment ?? naturalAlignment);
            alignment = Math.Max(alignment, fieldAlignment);
            var offset = type.IsExplicitLayout ? field.Offset : (end + fieldAlignment - 1) / fieldAlignment * fieldAlignment;
            if (offset < 0 || offset > 65536 - width ||
                (type.IsExplicitLayout && offset + width > type.ClassSize) ||
                (type.IsSequentialLayout && field.Offset >= 0) || fieldCounts[field.Name] != 1)
                throw new InvalidDataException($"Invalid field layout: {field.FullName}");
            offsets.Add(field.FullName, offset);
            end = Math.Max(end, offset + width);
        }

        // An explicit metadata size suppresses final alignment rounding in CoreCLR.
        // A smaller declared size cannot truncate fields; empty value types occupy one byte.
        var size = type.ClassSize > 0 ? Math.Max(end, type.ClassSize) : (end + alignment - 1) / alignment * alignment;
        size = Math.Max(1, size);
        if (size > 65536) throw new InvalidDataException($"Unsupported aggregate size: {reference.FullName}");
        active.Remove(LayoutEvidence.Identity(reference));
        var result = new AggregateInfo(size, alignment, offsets);
        layouts.Add(LayoutEvidence.Identity(reference), result);
        return result;
    }

    // Equal-width primitive fields, where auto layout coincides with sequential placement.
    static AggregateInfo TupleLayout(TypeReference reference, ModuleDefinition module, string architecture)
    {
        RuntimeModels.ValidateTypeIdentity(reference, module, architecture);
        var fields = ValueTuples.Fields(reference);
        foreach (var field in fields)
            if (field.Type is TypeSpecification || EnumTypes.IsEnum(field.Type) || IsAggregate(field.Type, module))
                throw new InvalidDataException($"Unsupported field type: {field.Type.FullName}");
        var width = PrimitiveWidth(fields[0].Type);
        if (fields.Any(field => PrimitiveWidth(field.Type) != width))
            throw new InvalidDataException($"Unsupported aggregate layout: {reference.FullName} (auto layout reorders fields of different widths)");
        var offsets = fields.Select((field, index) => (field.Definition.FullName, index * width)).ToDictionary();
        return new AggregateInfo(fields.Length * width, width, offsets);
    }

    internal static void Type(TypeReference type, ModuleDefinition module, bool returns = false, string architecture = "scalar")
    {
        if (ManagedPointers.Signature(type) is { } managed)
        {
            ManagedPointers.Validate(managed, module, architecture);
            return;
        }
        if (type is PointerType pointer)
        {
            var element = EnumTypes.Storage(pointer.ElementType);
            if (!IsAggregate(pointer.ElementType, module) && IntegerVectorWidth(pointer.ElementType) is null &&
                (element is TypeSpecification ||
                element.MetadataType is not (MetadataType.SByte or MetadataType.Byte or
                    MetadataType.Int16 or MetadataType.UInt16 or MetadataType.Char or
                    MetadataType.Int32 or MetadataType.UInt32 or
                    MetadataType.Int64 or MetadataType.UInt64 or MetadataType.IntPtr or MetadataType.UIntPtr)))
                throw new InvalidDataException("Unsupported stack-storage pointer element type");
            Type(pointer.ElementType, module, architecture: architecture);
            return;
        }
        if (type is ArrayType array)
        {
            if (Arrays.Of(array) is null)
                throw new InvalidDataException("Unsupported array shape or element type: " + type.FullName);
            Type(array.ElementType, module, architecture: architecture);
            return;
        }
        if (type is ByReferenceType byRef)
        {
            if (ManagedPointers.Signature(byRef.ElementType) is not null)
                throw new InvalidDataException("Unsupported address of managed callable root");
            if (byRef.ElementType is ArrayType)
                throw new InvalidDataException("Unsupported by-reference array root");
            if (Spans.Is(byRef.ElementType))
                throw new InvalidDataException("Unsupported by-reference span");
            if (byRef.ElementType is ByReferenceType)
                throw new InvalidDataException("Unsupported nested managed reference");
            Type(byRef.ElementType, module, architecture: architecture);
            return;
        }
        type = EnumTypes.Storage(type);
        if (IsAggregate(type, module)) { Layout(type, module, architecture); return; }
        if (!(returns && type.FullName == "System.Void") && type.FullName is not
            ("System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" or "System.Byte" or "System.Boolean" or
            "System.SByte" or "System.Int16" or "System.UInt16" or "System.Char") &&
            !(type is GenericInstanceType && type.FullName.StartsWith("System.Runtime.Intrinsics.Vector", StringComparison.Ordinal) && RuntimeModels.SupportedType(type)) &&
            !Spans.Is(type))
            throw new InvalidDataException($"Unsupported type: {type.FullName}");
        RuntimeModels.ValidateTypeIdentity(type, module, architecture);
    }

    internal sealed record Blocked(MethodDefinition Method, Instruction? At, Exception Error, MethodDefinition[] Chain);

    // With `blocked`, failures after entry selection are recorded and the walk continues past them;
    // without it, the first failure throws. Either way only profile-reachable code is checked.
    internal static MethodDefinition[] Validate(ModuleDefinition module, string assemblyIdentity, string entrySignature, FeatureProfile profile,
        IReadOnlyCollection<string>? initializedTypes = null, List<Blocked>? blocked = null, ImportResolution? imports = null,
        string[]? typeArguments = null, Func<TypeReference, bool>? importedByref = null)
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
        MethodDefinition entry = ContractMethodMetadata.Select(module, entrySignature, typeArguments ?? [], profile.Architecture).Closed;
        MethodSpecialization specializations = new(module, profile.Architecture);
        var staticValues = new StaticValues.Context(module);
        // 1 while visiting, 2 once admitted to the walk, 3 when its body could not be analysed.
        Dictionary<MethodDefinition, int> state = [];
        List<MethodDefinition> ordered = [];
        Dictionary<MethodDefinition, MethodDefinition[]> chains = [];
        Dictionary<MethodDefinition, List<(MethodDefinition Method, bool Deferred)>> dependencies = [];
        MethodReference[]? addressedMethods = null;
        Dictionary<string, MethodDefinition[]> indirectTargets = new(StringComparer.Ordinal);
        // Call sites already reported, or whose callee was not analysed, have no translation to check.
        HashSet<Instruction> skipped = [];
        bool Check(MethodDefinition method, Instruction? at, Action check, bool named = false)
        {
            if (blocked is null)
            {
                if (named) InMethod(method, () => { check(); return 0; });
                else check();
                return true;
            }
            try { check(); return true; }
            catch (Exception error)
            {
                blocked.Add(new(method, at, error, chains[method]));
                return false;
            }
        }
        void Visit(MethodDefinition method)
        {
            var pending = new Stack<(MethodDefinition Method, bool Finish, bool Deferred,
                MethodDefinition? Caller)>();
            pending.Push((method, false, false, null));
            while (pending.TryPop(out var item))
            {
                if (item.Finish)
                {
                    state[item.Method] = 2;
                    ordered.Add(item.Method);
                    continue;
                }
                if (state.TryGetValue(item.Method, out var visited))
                {
                    if (visited == 1 && !item.Deferred)
                        throw new InvalidDataException($"Recursive managed dependency: {item.Method.FullName}");
                    continue;
                }
                chains[item.Method] = item.Caller is { } caller
                    ? [.. chains[caller], item.Method] : [item.Method];
                dependencies[item.Method] = [];
                Walk(item.Method);
                if (state[item.Method] == 3) continue;
                pending.Push((item.Method, true, false, item.Caller));
                foreach (var dependency in dependencies[item.Method].AsEnumerable().Reverse())
                    pending.Push((dependency.Method, false, dependency.Deferred,
                        item.Method));
            }
        }
        void Walk(MethodDefinition method)
        {
            state[method] = 3;
            if (!Check(method, null, () =>
            {
                if (method.Module != module || method.IsStatic == method.HasThis || method.ExplicitThis ||
                    (!method.IsStatic && !IsAggregate(MethodSpecialization.DeclaringType(method), module)) ||
                    method.CallingConvention != MethodCallingConvention.Default || !method.HasBody ||
                    method.IsPInvokeImpl ||
                    (method.ImplAttributes & (MethodImplAttributes.CodeTypeMask | MethodImplAttributes.ManagedMask |
                        MethodImplAttributes.Synchronized | MethodImplAttributes.InternalCall | MethodImplAttributes.ForwardRef)) != 0 ||
                    method.HasGenericParameters || (method.DeclaringType.HasGenericParameters &&
                        MethodSpecialization.OwnerArguments(method).Count == 0) ||
                    method.Body.Instructions.Count == 0 || method.Body.ExceptionHandlers.Count != 0 ||
                    (method.IsConstructor && method.IsStatic) ||
                    (method.DeclaringType.Methods.Any(m => m.IsConstructor && m.IsStatic) &&
                        !initializedTypes.Contains(method.DeclaringType.FullName, StringComparer.Ordinal)))
                    throw new InvalidDataException($"Unsupported method metadata or static initialisation: {method.FullName}");
            })) return;
            Check(method, null, () =>
            {
                if (method.HasThis) Layout(MethodSpecialization.DeclaringType(method), module, profile.Architecture);
                if (method.IsConstructor && (method.Name != ".ctor" || !method.HasThis || method.ReturnType.MetadataType != MetadataType.Void))
                    throw new InvalidDataException($"Unsupported constructor signature: {method.FullName}");
                Type(method.ReturnType, module, returns: true, architecture: profile.Architecture);
            }, named: true);
            foreach (ParameterDefinition parameter in method.Parameters)
                Check(method, null, () =>
                {
                    if (parameter.ParameterType is ByReferenceType && importedByref?.Invoke(parameter.ParameterType) == true) return;
                    Type(parameter.ParameterType, module, architecture: profile.Architecture);
                }, named: true);
            if (Check(method, null, () => Spans.Analyze(method, profile), named: true))
                foreach (VariableDefinition local in method.Body.Variables)
                    Check(method, null, () => Type(local.VariableType, module,
                        architecture: profile.Architecture), named: true);
            HashSet<Instruction> reachable = [];
            TypeTests.Analysis? typeTests = null;
            Throws.Analysis? throws = null;
            if (!Check(method, null, () => reachable = Reachability.Analyze(method, profile), named: true) ||
                !Check(method, null, () => (typeTests, throws) = (TypeTests.Analyze(method), Throws.Analyze(method))))
                return;
            var instructions = new InstructionIndex(method);
            state[method] = 1;
            void Enter(MethodDefinition callee, MethodReference reference, Instruction instruction)
            {
                var deferred = TailCalls.IsCall(instruction) ||
                    instruction.OpCode.Code is Code.Ldftn or Code.Calli;
                if (state.GetValueOrDefault(callee) == 1 && !deferred)
                    throw Call("Recursive managed dependency", reference, method, instruction);
                dependencies[method].Add((callee, deferred));
            }
            void CallSite(Instruction instruction, MethodReference reference)
            {
                if (instruction.OpCode.Code == Code.Callvirt)
                {
                    var resolved = ConstrainedCalls.Resolve(method, instruction, instructions, profile.Architecture);
                    Enter(ConstrainedCalls.Specialize(resolved, instruction, specializations), reference, instruction);
                    return;
                }
                if (ImportResolution.External(reference, module))
                {
                    if (imports is null)
                        throw Call("External managed dependency", reference, method, instruction,
                            $"Next: supply --import {ScopeName(reference.DeclaringType.Scope)}.leancil.contracts.");
                    try { imports.Admit(reference, instruction, profile); }
                    catch (InvalidDataException error) when (Rejections.Of(error) is null)
                    {
                        throw Call("Rejected external call", reference, method, instruction,
                            $"Callee scope: {ScopeName(reference.DeclaringType.Scope)}\n  {error.Message}", error);
                    }
                    return;
                }
                if (reference is GenericInstanceMethod || reference.DeclaringType is GenericInstanceType)
                {
                    if (instruction.OpCode.Code is not (Code.Call or Code.Ldftn or Code.Calli or Code.Newobj))
                        throw Call("Unsupported generic constructor call", reference, method, instruction);
                    MethodDefinition specialized;
                    try { specialized = specializations.Instantiate(reference); }
                    catch (InvalidDataException error) when (Rejections.Of(error) is null)
                    {
                        throw Call("Unsupported generic call", reference, method, instruction, error.Message, error);
                    }
                    if (instruction.OpCode.Code == Code.Newobj &&
                        (!specialized.IsConstructor || !specialized.HasThis ||
                         !IsAggregate(MethodSpecialization.DeclaringType(specialized), module)))
                        throw Call("Unsupported generic newobj constructor", reference, method, instruction);
                    instruction.Operand = specialized;
                    Enter(specialized, reference, instruction);
                    return;
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
            void StaticLoad(Instruction instruction, FieldReference loaded)
            {
                StaticValues.Value value;
                try
                {
                    FieldDefinition field = StaticValues.Field(loaded, module, profile.Architecture);
                    if (!initializedTypes.Contains(field.DeclaringType.FullName, StringComparer.Ordinal))
                        throw new InvalidDataException($"Unsupported static field load: {loaded.FullName}\n  Loading it requires --assume-initialized {field.DeclaringType.FullName}.");
                    value = staticValues.Resolve(loaded, profile.Architecture);
                }
                catch (InvalidDataException error) when (Rejections.Of(error) is null)
                {
                    throw new InvalidDataException($"{error.Message}\n  Site: {instruction}", error);
                }
                if (value.Initializer is { } initializer) Enter(initializer, initializer, instruction);
            }
            foreach (Instruction instruction in reachable)
            {
                if (instruction.OpCode.Code == Code.Calli && instruction.Operand is Mono.Cecil.CallSite site)
                {
                    Check(method, instruction, () =>
                    {
                        ManagedPointers.Validate(site, module, profile.Architecture);
                        var signature = ManagedPointers.SignatureEvidence(site);
                        if (!indirectTargets.TryGetValue(signature, out var targets))
                        {
                            addressedMethods ??= ManagedPointers.AddressedMethods(module)
                                .Where(target => target.DeclaringType.Scope == module).ToArray();
                            targets = addressedMethods
                                .Where(target => ManagedPointers.SameSignature(site, ManagedPointers.ReferenceSignature(target)))
                                .Select(target => target is GenericInstanceMethod ||
                                        target.DeclaringType is GenericInstanceType
                                    ? specializations.Instantiate(target) : target.Resolve())
                                .Where(target => target is not null && ManagedPointers.SameSignature(site, target))
                                .Distinct().ToArray()!;
                            indirectTargets.Add(signature, targets);
                        }
                        foreach (var target in targets) CallSite(instruction, target);
                    });
                    continue;
                }
                if (instruction.OpCode.Code == Code.Ldsfld && instruction.Operand is FieldReference platform &&
                    FeatureProfile.PlatformFieldQuery(platform))
                {
                    if (!Check(method, instruction, () => FeatureProfile.PlatformField(platform), named: true))
                        skipped.Add(instruction);
                    continue;
                }
                if (StaticValues.IsLoad(instruction) && instruction.Operand is FieldReference loaded)
                {
                    if (!Check(method, instruction, () => StaticLoad(instruction, loaded), named: true))
                        skipped.Add(instruction);
                    continue;
                }
                if (instruction.OpCode.Code is not (Code.Call or Code.Callvirt or Code.Newobj or Code.Ldftn or Code.Ldvirtftn) || instruction.Operand is not MethodReference reference ||
                    typeTests!.Operands.Contains(instruction) || typeTests.Results.ContainsKey(instruction) || throws!.Operands.Contains(instruction))
                    continue;
                if (!Check(method, instruction, () =>
                    {
                        // Fold recognition scans the whole body, but only reachable unsupported throws are rejected.
                        if (instruction.OpCode.Code == Code.Newobj && instruction.Next?.OpCode.Code == Code.Throw)
                            throw Call("Unsupported exception constructor", reference, method, instruction,
                                "Folded throws require an allowlisted System.Runtime constructor with literal strings or null arguments.");
                        if (instruction.OpCode.Code != Code.Newobj && reference.Name == ".ctor" &&
                            Spans.Is(reference.DeclaringType) &&
                            !Spans.Analyze(method, profile).Constructors.ContainsKey(instruction))
                            throw Call("Unsupported in-place span constructor", reference, method, instruction,
                                "The receiver must be a local address followed by at most three simple argument pushes.");
                        if (InstructionTranslation.RuntimeModel(reference, profile) is null) CallSite(instruction, reference);
                    }))
                    skipped.Add(instruction);
            }
        }
        Visit(entry);
        ordered.Reverse();
        // Validate translation before producing any artifact.
        var methods = ordered.ToArray();
        var methodIndices = methods.Select((method, index) => (method, index))
            .ToDictionary(pair => pair.method, pair => pair.index);
        var constrainedTargets = new ConstrainedCalls.TargetIndex(methods);
        var layoutContext = new LayoutContext(module, profile.Architecture);
        for (int i = 0; i < methods.Length; i++)
        {
            var index = i;
            var method = methods[index];
            var instructions = new InstructionIndex(method);
            NativeOperands.Certificate? nativeOperands = null;
            Dictionary<int, int>? parameterHomes = null;
            HashSet<Instruction>? reachable = null;
            if (!Check(method, null, () =>
                {
                    reachable = Reachability.Analyze(method, profile);
                    nativeOperands = NativeOperands.Certify(method, reachable, profile);
                    parameterHomes = ParameterStorage.IndexHomes(ParameterStorage.Analyze(method, reachable));
                }, named: true))
                continue;
            foreach (Instruction instruction in reachable!)
                if (!skipped.Contains(instruction))
                    Check(method, instruction, () =>
                        InstructionTranslation.Translate(instruction, method, methodIndices, index, instructions,
                            profile, nativeOperands, parameterHomes, imports, layoutContext, constrainedTargets), named: true);
        }
        return methods;
    }
}
