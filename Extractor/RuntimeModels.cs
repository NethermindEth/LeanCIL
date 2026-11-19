using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class RuntimeModels
{
    private static string Vector(int width, string element) => $"System.Runtime.Intrinsics.Vector{width}`1<{element}>";

    private static readonly int[] VectorWidths = [128, 256, 512];
    private static readonly string[] VectorElements =
    [
        "System.UInt64", "System.Int64", "System.UInt32", "System.Int32",
        "System.Byte", "System.Double", "System.Single"
    ];

    private const string Intrinsics = "System.Runtime.Intrinsics";
    private const string X86 = $"{Intrinsics}.X86";
    private const string Avx = $"{X86}.Avx";
    private const string Avx2 = $"{X86}.Avx2";
    private const string Avx512FVL = $"{X86}.Avx512F/VL";
    private const string Avx512DQ = $"{X86}.Avx512DQ";
    private const string V128Byte = $"{Intrinsics}.Vector128`1<System.Byte>";
    private const string V128UInt64 = $"{Intrinsics}.Vector128`1<System.UInt64>";
    private const string V128UInt32 = $"{Intrinsics}.Vector128`1<System.UInt32>";
    private const string V256Byte = $"{Intrinsics}.Vector256`1<System.Byte>";
    private const string V256UInt64 = $"{Intrinsics}.Vector256`1<System.UInt64>";
    private const string V256UInt32 = $"{Intrinsics}.Vector256`1<System.UInt32>";
    private const string V256Int32 = $"{Intrinsics}.Vector256`1<System.Int32>";
    private const string V256Int64 = $"{Intrinsics}.Vector256`1<System.Int64>";
    private const string V256Double = $"{Intrinsics}.Vector256`1<System.Double>";
    private const string V256Single = $"{Intrinsics}.Vector256`1<System.Single>";
    private const string V512UInt64 = $"{Intrinsics}.Vector512`1<System.UInt64>";
    private const string UInt64Pair = "System.ValueTuple`2<System.UInt64,System.UInt64>";
    private const string Unsafe = "System.Runtime.CompilerServices.Unsafe";

    /// <summary>Whether a scope is the row that names <paramref name="platform"/>, column for column.</summary>
    internal static bool ExactScope(TypeReference type, AssemblyName platform) =>
        type.Scope is AssemblyNameReference && AssemblyName.OfScope(type, IdentityImage(type)) == platform;

    static MetadataImage IdentityImage(TypeReference type) =>
        (PinnedAssemblies.Active ?? throw new InvalidDataException("Type identity without a pinned module image"))
        .IdentityMetadata(type.Module);

    internal static bool SupportedType(TypeReference type)
    {
        string name = type.FullName;
        return name is "System.UInt32" or "System.Byte" or "System.UIntPtr" or "System.IntPtr" or
            "System.RuntimeFieldHandle" || Spans.Is(type) ||
            (type is ByReferenceType byRef && SupportedType(byRef.ElementType)) ||
            IsSupportedVector(name);
    }

    private static bool IsSupportedVector(string name) =>
        VectorWidths.Any(width => VectorElements.Any(element => name == Vector(width, element)));

    internal static bool HasRuntimeValueTypeBase(TypeDefinition type) =>
        type.BaseType is { FullName: "System.ValueType" } parent &&
        ExactScope(parent, PlatformAssemblies.SystemRuntime);

    internal static void ValidateTypeIdentity(TypeReference type, ModuleDefinition module,
        string architecture = "scalar")
    {
        if (PinnedAssemblies.Declares(type, module) && type.IsValueType && type is not TypeSpecification)
        {
            if (EnumTypes.IsEnum(type)) EnumTypes.Storage(type);
            else MetadataValidation.Layout(type, module, architecture);
            return;
        }
        if (type is GenericParameter) return;
        if (GenericStructs.Is(type) && type is GenericInstanceType closedStruct)
        {
            foreach (var argument in closedStruct.GenericArguments)
                ValidateTypeIdentity(argument, module, architecture);
            MetadataValidation.Layout(type, module, architecture);
            return;
        }
        if (type is GenericInstanceType generic)
        {
            if (generic.IsValueType != generic.ElementType.IsValueType)
                throw new InvalidDataException(
                    $"Unsupported type identity: {generic.FullName} (generic value-type encoding)");
            ValidateTypeIdentity(generic.ElementType, module, architecture);
            foreach (TypeReference argument in generic.GenericArguments)
                ValidateTypeIdentity(argument, module, architecture);
            return;
        }
        if (type is TypeSpecification specification)
        {
            if (type is RequiredModifierType required)
                ValidateTypeIdentity(required.ModifierType, module, architecture);
            if (type is OptionalModifierType optional)
                ValidateTypeIdentity(optional.ModifierType, module, architecture);
            ValidateTypeIdentity(specification.ElementType, module, architecture);
            return;
        }
        bool expectedValueType = IsModeledValueType(type.FullName);
        var expectedScope = DefiningAssembly(type.FullName);
        bool valid = type.IsValueType == expectedValueType && ExactScope(type, expectedScope) &&
            (type.FullName != "System.Void" || type.MetadataType == MetadataType.Void);
        if (!valid) throw new InvalidDataException($"Unsupported type identity: {type.FullName} [{type.Scope}]");
    }

    private static bool IsModeledValueType(string name) => name is "System.UInt64" or "System.Int64" or
        "System.SByte" or "System.Int16" or "System.UInt16" or "System.Char" or
        "System.UInt32" or "System.Int32" or "System.Byte" or "System.Boolean" or "System.Double" or "System.Single" or
        "System.IntPtr" or "System.UIntPtr" or "System.ReadOnlySpan`1" or "System.Span`1" or "System.RuntimeFieldHandle" or
        "System.Runtime.Intrinsics.Vector128`1" or "System.Runtime.Intrinsics.Vector256`1" or
        "System.Runtime.Intrinsics.Vector512`1" or "System.ValueTuple`2";

    private static AssemblyName DefiningAssembly(string name) =>
        name is "System.Buffers.Binary.BinaryPrimitives" or "System.MemoryExtensions"
            ? PlatformAssemblies.SystemMemory :
        name.StartsWith("System.Runtime.Intrinsics.", StringComparison.Ordinal)
            ? PlatformAssemblies.SystemRuntimeIntrinsics : PlatformAssemblies.SystemRuntime;

    internal static void ValidateSignature(MethodReference reference, string architecture = "scalar")
    {
        ValidateTypeIdentity(reference.DeclaringType, reference.Module, architecture);
        ValidateTypeIdentity(reference.ReturnType, reference.Module, architecture);
        foreach (ParameterDefinition parameter in reference.Parameters)
            ValidateTypeIdentity(parameter.ParameterType, reference.Module, architecture);
        if (reference is GenericInstanceMethod generic)
            foreach (TypeReference argument in generic.GenericArguments)
                ValidateTypeIdentity(argument, reference.Module, architecture);
    }

    /// <summary>
    /// <c>call System.Object::.ctor()</c> on the receiver of an admitted class constructor. The runtime's
    /// constructor has no effect on an instance, so the model only pops the receiver.
    /// </summary>
    internal static bool ObjectConstructor(MethodReference reference) =>
        reference is { Name: ".ctor", HasThis: true, ExplicitThis: false, Parameters.Count: 0 } &&
        reference is not GenericInstanceMethod && reference.CallingConvention == MethodCallingConvention.Default &&
        reference.ReturnType.MetadataType == MetadataType.Void &&
        reference.DeclaringType is { FullName: "System.Object" } owner &&
        ExactScope(owner, PlatformAssemblies.SystemRuntime);

    /// <summary>
    /// A modelled call keeps its method operand. Analyses use the returned operation, including
    /// the checked write for an integer helper with an out parameter.
    /// </summary>
    internal static Operation? CallModel(MethodReference reference, FeatureProfile profile)
    {
        if (FeatureProfile.PlatformConstant(reference) is int constant) return new Constant(32, constant, true);
        if (FeatureProfile.Getter(reference) is Feature feature) return new FeatureTest(feature);
        if (ReferenceQueries.Constant(reference, profile.Architecture) is int referenceContent)
            return new Constant(32, referenceContent, true);
        if (ArgumentGuards.CallModel(reference, profile.Architecture) is { } guard) return guard;
        if (Spans.ArrayExtension(reference, profile.Architecture) is { } arrayView) return arrayView;
        if (Spans.CoreMember(reference, profile.Architecture) is { } span) return span;
        if (MarshalModels.CallModel(reference, profile.Architecture) is { } marshal) return marshal;
        if (BinaryModels.CallModel(reference, profile.Architecture) is { } binary) return binary;
        if (ObjectConstructor(reference)) return new StackOperation(StackOpcode.Pop);
        if (VectorModel(reference) is { } vector)
        {
            ValidateSignature(reference, profile.Architecture);
            return vector;
        }
        if (BitModels.Call(reference, profile) is { } bits) return bits;
        if (UnsafeModels.CallModel(reference, profile.Architecture) is { } helper) return helper;
        if (reference.HasThis || reference.ExplicitThis || reference.HasGenericParameters ||
            reference is GenericInstanceMethod ||
            reference.CallingConvention != MethodCallingConvention.Default ||
            !ExactScope(reference.DeclaringType, PlatformAssemblies.SystemRuntime)) return null;
        var model = reference.FullName switch
        {
            $"System.Void {Unsafe}::CopyBlock(System.Byte&,System.Byte&,System.UInt32)" or
            $"System.Void {Unsafe}::CopyBlock(System.Void*,System.Void*,System.UInt32)" =>
                MemoryOperation.Other("(.copyBlock 8)"),
            $"System.Void {Unsafe}::CopyBlockUnaligned(System.Byte&,System.Byte&,System.UInt32)" or
            $"System.Void {Unsafe}::CopyBlockUnaligned(System.Void*,System.Void*,System.UInt32)" =>
                MemoryOperation.Other("(.copyBlock 1)"),
            $"System.Void {Unsafe}::InitBlock(System.Byte&,System.Byte,System.UInt32)" or
            $"System.Void {Unsafe}::InitBlock(System.Void*,System.Byte,System.UInt32)" =>
                MemoryOperation.Other("(.initBlock 8)"),
            $"System.Void {Unsafe}::InitBlockUnaligned(System.Byte&,System.Byte,System.UInt32)" or
            $"System.Void {Unsafe}::InitBlockUnaligned(System.Void*,System.Byte,System.UInt32)" =>
                MemoryOperation.Other("(.initBlock 1)"),
            _ => IntegerMathCalls.GetValueOrDefault(reference.FullName)
        };
        if (model is null) return null;
        ValidateSignature(reference, profile.Architecture);
        if (ValueTuples.Is(reference.ReturnType))
            ValueTuples.RequirePair(reference.ReturnType, reference.Module, profile.Architecture);
        return model;
    }

    internal static Operation? Translate(MethodReference reference, FeatureProfile profile)
    {
        if (reference.ExplicitThis || reference.CallingConvention == MethodCallingConvention.VarArg ||
            (reference.HasThis && reference.Name is not
                (".ctor" or "Clear" or "Fill" or "CopyTo" or "TryCopyTo")) ||
            (reference.Name == ".ctor" && !reference.HasThis)) return null;
        string scope = reference.DeclaringType.Scope.Name;
        if (PlatformAssemblies.Claimed(AssemblyName.OfScope(
                reference.DeclaringType, IdentityImage(reference.DeclaringType))) is { } platform &&
            !ExactScope(reference.DeclaringType, platform))
            throw new InvalidDataException(
                $"Unsupported runtime assembly scope: {reference.FullName} [{reference.DeclaringType.Scope}]");
        Operation? op = scope switch
        {
            "System.Runtime" => UnsafeModels.Translate(reference, profile.Architecture)
                ?? ElementSpan(reference, profile.Architecture) ?? Runtime(reference.FullName),
            "System.Runtime.Intrinsics" => Intrinsic(reference.FullName, profile),
            _ => null
        };
        if (op is not null) ValidateSignature(reference, profile.Architecture);
        if (op is not null && ValueTuples.Is(reference.ReturnType))
            ValueTuples.RequirePair(reference.ReturnType, reference.Module, profile.Architecture);
        return op;
    }

    internal static readonly (string Type, int Width, bool Signed)[] MathIntegers =
    [
        ("System.SByte", 8, true), ("System.Byte", 8, false),
        ("System.Int16", 16, true), ("System.UInt16", 16, false),
        ("System.Int32", 32, true), ("System.UInt32", 32, false),
        ("System.Int64", 64, true), ("System.UInt64", 64, false),
        ("System.IntPtr", 64, true), ("System.UIntPtr", 64, false)
    ];
    private static readonly (string Name, ScalarFunction Function, int Arity)[] MathOperations =
    [
        ("Min", ScalarFunction.Min, 2), ("Max", ScalarFunction.Max, 2), ("Clamp", ScalarFunction.Clamp, 3),
        ("Abs", ScalarFunction.Abs, 1), ("Sign", ScalarFunction.Sign, 1)
    ];

    // Vector helpers must bind a static declaration in the exact intrinsics assembly.
    static Operation? VectorModel(MethodReference reference)
    {
        var convention = reference is GenericInstanceMethod
            ? MethodCallingConvention.Generic : MethodCallingConvention.Default;
        if (reference.HasThis || reference.ExplicitThis || reference.CallingConvention != convention ||
            !ExactScope(reference.DeclaringType, PlatformAssemblies.SystemRuntimeIntrinsics)) return null;
        if (reference is GenericInstanceMethod generic &&
            generic.GenericArguments.Count != generic.ElementMethod.GenericParameters.Count) return null;
        if (reference is not GenericInstanceMethod && reference.HasGenericParameters) return null;
        string signature = reference.FullName;
        if (VectorHelperCalls.TryGetValue(signature, out var helper)) return helper;
        if (signature == $"{V128UInt64} {Intrinsics}.Vector128::CreateScalarUnsafe(System.UInt64)")
            return new VectorCreateScalarUnsafe64();
        foreach (int width in new[] { 128, 256 })
        {
            string element = $"!!0 {Intrinsics}.Vector{width}::GetElement<System.UInt64>";
            if (signature == $"{element}({Vector(width, "!!0")},System.Int32)")
                return Hardware($".vector (.extract64 {width})", 2);
        }
        return null;
    }

    private static readonly Dictionary<string, Operation> IntegerMathCalls = BuildIntegerMathCalls();

    private static ScalarIntrinsic Scalar(ScalarFunction function, int width, bool signed, int arguments,
        int result = 32) => new(function, width, signed, result, arguments);

    // The overload's complete signature selects its scalar intrinsic or checked out-parameter write.
    private static Dictionary<string, Operation> BuildIntegerMathCalls()
    {
        var calls = new Dictionary<string, Operation>(StringComparer.Ordinal)
        {
            ["System.UInt64 System.Math::BigMul(System.UInt32,System.UInt32)"] =
                Scalar(ScalarFunction.BigMul32, 32, false, 2),
            ["System.Int64 System.Math::BigMul(System.Int32,System.Int32)"] =
                Scalar(ScalarFunction.BigMul32, 32, true, 2),
            ["System.UInt64 System.Math::BigMul(System.UInt64,System.UInt64,System.UInt64&)"] =
                MemoryOperation.Other("(.bigMul64 false)"),
            ["System.Int64 System.Math::BigMul(System.Int64,System.Int64,System.Int64&)"] =
                MemoryOperation.Other("(.bigMul64 true)"),
            ["System.Int32 System.Math::DivRem(System.Int32,System.Int32,System.Int32&)"] =
                MemoryOperation.Other("(.divRemOut 32)"),
            ["System.Int64 System.Math::DivRem(System.Int64,System.Int64,System.Int64&)"] =
                MemoryOperation.Other("(.divRemOut 64)")
        };
        foreach (var (type, width, signed) in MathIntegers)
            calls.Add($"System.ValueTuple`2<{type},{type}> System.Math::DivRem({type},{type})",
                Scalar(ScalarFunction.DivRem, width, signed, 2));
        foreach (var (type, width, signed) in MathIntegers)
        foreach (var (name, function, arity) in MathOperations)
        {
            if (!signed && arity == 1) continue;
            var result = name == "Sign" ? "System.Int32" : type;
            var parameters = string.Join(",", Enumerable.Repeat(type, arity));
            var model = Scalar(function, width, signed, arity);
            calls.Add($"{result} System.Math::{name}({parameters})", model);
            calls.Add($"{result} {type}::{name}({parameters})", model);
        }
        return calls;
    }

    private static Operation? Runtime(string signature) => signature switch
    {
        "System.Void System.ReadOnlySpan`1<System.Byte>::.ctor(System.Void*,System.Int32)" =>
            MemoryOperation.Of(new SpanCreate()),
        _ => Span(signature)
    };

    private static readonly Dictionary<string, Operation> SpanOperations = BuildSpanOperations();

    // Signatures are immutable: runtime lookup performs no interpolation or per-element scan.
    private static Operation? Span(string signature) => SpanOperations.GetValueOrDefault(signature);

    private sealed class ElementSpanOperations
    {
        internal readonly Dictionary<string, Dictionary<string, Operation>> Architectures =
            new(StringComparer.Ordinal);
    }

    private static Operation? ElementSpan(MethodReference method, string architecture)
    {
        var element = method.DeclaringType is GenericInstanceType { GenericArguments.Count: 1 } owner
            ? owner.GenericArguments[0]
            : method is GenericInstanceMethod { GenericArguments.Count: 1 } generic
                ? generic.GenericArguments[0] : null;
        if (element is null || Arrays.Primitive(element) is not null ||
            Spans.ElementWidth(element, architecture) is null) return null;
        if (EnumTypes.IsEnum(element)) EnumTypes.Storage(element);
        var architectures = EnumTypes.Cached(element, _ => new ElementSpanOperations()).Architectures;
        if (!architectures.TryGetValue(architecture, out var operations))
        {
            operations = BuildSpanOperations(element, architecture);
            architectures.Add(architecture, operations);
        }
        return operations.GetValueOrDefault(method.FullName);
    }

    private static Dictionary<string, Operation> BuildSpanOperations(
        TypeReference? elementType = null, string architecture = "scalar")
    {
        var operations = new Dictionary<string, Operation>(StringComparer.Ordinal);
        var primitives = new[]
        {
            ("System.Byte", 1), ("System.SByte", 1), ("System.Int16", 2), ("System.UInt16", 2),
            ("System.Int32", 4), ("System.UInt32", 4), ("System.Int64", 8), ("System.UInt64", 8),
            ("System.IntPtr", 8), ("System.UIntPtr", 8), ("System.Char", 2), ("System.Boolean", 1)
        };
        foreach (var (element, width) in elementType is null ? primitives :
            [(elementType.FullName, Spans.ElementWidth(elementType, architecture)!.Value)])
        {
            var arrayElement = elementType is null ? Arrays.Primitive(element) :
                Arrays.Storage(elementType, architecture);
            var staticElement = elementType is null || Arrays.Primitive(elementType) is not null ||
                EnumTypes.IsEnum(elementType);
            if (staticElement && arrayElement is not null)
            {
                operations.Add($"System.Void System.Array::Fill<{element}>(!!0[],!!0)",
                    MemoryOperation.Other($"(.arrayFill {arrayElement.Expression} false)"));
                operations.Add($"System.Void System.Array::Fill<{element}>(!!0[],!!0,System.Int32,System.Int32)",
                    MemoryOperation.Other($"(.arrayFill {arrayElement.Expression} true)"));
            }
            if (staticElement) operations.Add("System.ReadOnlySpan`1<!!0> System.Runtime.CompilerServices.RuntimeHelpers::" +
                $"CreateSpan<{element}>(System.RuntimeFieldHandle)", MemoryOperation.Other($"(.createSpan {width})"));
            foreach (var name in new[] { "System.Span`1", "System.ReadOnlySpan`1" })
            {
                var owner = $"{name}<{element}>";
                var writable = name == "System.Span`1";
                if (arrayElement is not null)
                {
                    var arrayWhole = MemoryOperation.Of(new ArraySpan(arrayElement, writable, ArrayRange.Whole));
                    operations.Add($"System.Void {owner}::.ctor(!0[])", arrayWhole);
                    operations.Add($"System.Void {owner}::.ctor(!0[],System.Int32,System.Int32)",
                        MemoryOperation.Of(new ArraySpan(arrayElement, writable, ArrayRange.Counted)));
                }
                operations.Add($"System.Void {owner}::.ctor(System.Void*,System.Int32)",
                    MemoryOperation.Of(new SpanFromReference(width, writable)));
                operations.Add($"System.Void {owner}::.ctor(!0&)",
                    MemoryOperation.Of(new SpanSingleReference(width, writable)));
                operations.Add($"System.Void {owner}::CopyTo(System.Span`1<!0>)",
                    MemoryOperation.Other($"(.spanCopy {width} false)"));
                operations.Add($"System.Boolean {owner}::TryCopyTo(System.Span`1<!0>)",
                    MemoryOperation.Other($"(.spanCopy {width} true)"));
                if (writable)
                {
                    operations.Add($"System.Void {owner}::Clear()",
                        MemoryOperation.Other($"(.spanFill {width} true)"));
                    operations.Add($"System.Void {owner}::Fill(!0)",
                        MemoryOperation.Other($"(.spanFill {width} false)"));
                }
            }
        }
        return operations;
    }

    private static readonly Dictionary<string, Operation> PortableVectorOperations = BuildPortableVectorOperations();

    private static HardwareIntrinsic Hardware(string family, int arguments) => new(family, arguments);

    // Lane-independent integer aliases bind exact signatures to the existing whole-vector operations.
    private static Dictionary<string, Operation> BuildPortableVectorOperations()
    {
        var operations = new Dictionary<string, Operation>(StringComparer.Ordinal);
        foreach (var width in new[] { 128, 256, 512 })
        {
            var genericVector = Vector(width, "!!0");
            var memberVector = Vector(width, "!0");
            var owner = $"System.Runtime.Intrinsics.Vector{width}";
            foreach (var element in new[]
                { "System.Byte", "System.Int64", "System.UInt64", "System.UInt32", "System.Int32" })
            {
                var vectorOwner = Vector(width, element);
                foreach (var (name, op) in new[]
                    { ("op_BitwiseAnd", "band"), ("op_BitwiseOr", "bor"), ("op_ExclusiveOr", "bxor") })
                    operations.Add($"{memberVector} {vectorOwner}::{name}({memberVector},{memberVector})",
                        Hardware($".vector (.{op} {width})", 2));
                operations.Add($"{memberVector} {vectorOwner}::op_OnesComplement({memberVector})",
                    Hardware($".vector (.bnot {width})", 1));
                operations.Add($"System.Boolean {owner}::EqualsAll<{element}>({genericVector},{genericVector})",
                    Hardware($".vector (.equalsAll {width})", 2));
                operations.Add($"{memberVector} {vectorOwner}::get_Zero()", Hardware($".vector (.zero {width})", 0));
                operations.Add($"{memberVector} {vectorOwner}::get_AllBitsSet()",
                    Hardware($".vector (.ones {width})", 0));
            }
        }
        return operations;
    }

    private static readonly Dictionary<string, Operation> VectorHelperCalls = BuildVectorHelperCalls();

    // Every key fixes the open member declaration and the element used by the call.
    private static Dictionary<string, Operation> BuildVectorHelperCalls()
    {
        var calls = new Dictionary<string, Operation>(StringComparer.Ordinal);
        foreach (int width in VectorWidths)
        {
            var owner = $"{Intrinsics}.Vector{width}";
            var open = Vector(width, "!0");
            foreach (var element in new[] { "Byte", "Int32", "UInt32", "Int64", "UInt64" })
            {
                var vector = Vector(width, $"System.{element}");
                calls.Add($"System.Boolean {vector}::op_Equality({open},{open})",
                    Hardware($".vector (.equalsAll {width})", 2));
            }
            if (width == 512)
            {
                calls.Add($"{V512UInt64} {owner}::Create({V256UInt64},{V256UInt64})",
                    Hardware(".vector .combine256", 2));
                continue;
            }
            foreach (var (element, bits, count) in new[]
            {
                ("System.UInt64", 64, 1), ("System.UInt64", 64, width / 64), ("System.UInt32", 32, width / 32)
            })
            {
                var parameters = string.Join(",", Enumerable.Repeat(element, count));
                calls.Add($"{Vector(width, element)} {owner}::Create({parameters})",
                    Hardware($".vector (.create{bits} {width})", count));
            }
            var result = Vector(width, "!!0");
            calls.Add($"{result} {owner}::Create<System.Byte>(System.ReadOnlySpan`1<!!0>)",
                MemoryOperation.Other($"(.marshalRead (.snapshot .vector{width}) false)"));
        }
        var source = Vector(128, "!!0");
        foreach (var (suffix, offset) in new[] { ("", "false"), (",System.UIntPtr", "true") })
        {
            calls.Add($"{source} {Intrinsics}.Vector128::LoadUnsafe<System.Byte>(!!0&{suffix})",
                MemoryOperation.Other($"(.vector128Unsafe false {offset})"));
            calls.Add($"System.Void {Intrinsics}.Vector128::StoreUnsafe<System.Byte>({source},!!0&{suffix})",
                MemoryOperation.Other($"(.vector128Unsafe true {offset})"));
        }
        return calls;
    }

    private static Operation? Intrinsic(string signature, FeatureProfile profile)
    {
        if (PortableVectorOperations.TryGetValue(signature, out var operation)) return operation;
        Operation Finish(string family, int argc, Feature? required = null) =>
            Require(Hardware(family, argc), required);
        Operation Require(Operation intrinsic, Feature? required = null)
        {
            if (required is Feature feature && !profile.Get(feature))
                throw new InvalidDataException($"Reachable intrinsic lacks {feature}: {signature}");
            return intrinsic;
        }
        if (signature == $"{V256UInt64} {Avx2}::And({V256UInt64},{V256UInt64})")
            return Finish(".avx2 .band", 2, Feature.Avx2);
        if (signature == $"{V256UInt64} {Avx2}::Or({V256UInt64},{V256UInt64})")
            return Finish(".avx2 .bor", 2, Feature.Avx2);
        if (signature == $"{V256UInt64} {Avx2}::Xor({V256UInt64},{V256UInt64})")
            return Finish(".avx2 .bxor", 2, Feature.Avx2);
        if (signature == $"{V256UInt64} {Avx2}::AndNot({V256UInt64},{V256UInt64})")
            return Finish(".avx2 .andNot", 2, Feature.Avx2);
        if (signature == $"{V256UInt64} {Avx2}::ShiftLeftLogical({V256UInt64},{V128UInt64})")
            return Finish(".avx2 .shl64Count", 2, Feature.Avx2);
        if (signature == $"{V256UInt64} {Avx2}::ShiftRightLogical({V256UInt64},{V128UInt64})")
            return Finish(".avx2 .shr64Count", 2, Feature.Avx2);
        if (signature == $"{V512UInt64} {X86}.Avx512F::CompareLessThan({V512UInt64},{V512UInt64})")
            return Finish(".avx512 .ltu512", 2, Feature.Avx512F);
        if (signature == $"{V512UInt64} {X86}.Avx512F::CompareGreaterThan({V512UInt64},{V512UInt64})")
            return Finish(".avx512 .gtu512", 2, Feature.Avx512F);
        if (signature == $"System.Int32 {Avx512DQ}::MoveMask({V512UInt64})")
            return Finish(".avx512DQ .moveMask512", 1, Feature.Avx512DQ);
        foreach (int width in new[] { 128, 256 })
        {
            string ulongVector = Vector(width, "System.UInt64");
            string genericVector = Vector(width, "!!0");
            string memberVector = Vector(width, "!0");
            string owner = $"System.Runtime.Intrinsics.Vector{width}";
            string genericOwner = Vector(width, "System.UInt64");
            foreach ((string name, string op) in new[] { ("op_Addition", "add64"), ("op_Subtraction", "sub64") })
                if (signature == $"{memberVector} {genericOwner}::{name}({memberVector},{memberVector})")
                    return Finish($".vector (.{op} {width})", 2);
            foreach ((string name, string op) in new[] { ("LessThan", "ltu64"), ("Equals", "eq64") })
                if (signature == $"{genericVector} {owner}::{name}<System.UInt64>({genericVector},{genericVector})")
                    return Finish($".vector (.{op} {width})", 2);
            if (signature == $"{genericVector} {owner}::LessThan<System.Int64>({genericVector},{genericVector})")
                return Finish($".vector (.lt64 {width})", 2);
            foreach ((string method, string target) in new[] { ("AsByte", "System.Byte"), ("AsUInt32", "System.UInt32"),
                ("AsInt64", "System.Int64"), ("AsDouble", "System.Double"), ("AsUInt64", "System.UInt64"),
                ("AsInt32", "System.Int32"), ("AsSingle", "System.Single") })
                foreach (string source in new[]
                {
                    "System.UInt64", "System.Byte", "System.UInt32", "System.Int64", "System.Int32", "System.Single"
                })
                    if (signature == $"{Vector(width, target)} {owner}::{method}<{source}>({genericVector})")
                        return Finish($".vector (.reinterpret {width})", 1);
            string longVector = Vector(width, "System.Int64");
            if (signature == $"{longVector} {owner}::ShiftRightArithmetic({longVector},System.Int32)")
                return Finish($".vector (.ashr64 {width})", 2);
            if (signature == $"{ulongVector} {owner}::CreateScalar(System.UInt64)")
                return Finish($".vector (.createScalar64 {width})", 1);
            if (signature == $"{Vector(width, "System.UInt32")} {owner}::CreateScalar(System.UInt32)")
                return Finish($".vector (.createScalar32 {width})", 1);
            if (signature == $"System.UInt32 {owner}::ExtractMostSignificantBits<System.UInt64>({genericVector})")
                return Finish($".vector (.extractMSB64 {width})", 1);
            if (signature == $"!!0 {owner}::Sum<System.UInt64>({genericVector})")
                return Finish($".vector (.sum64 {width})", 1);
        }
        return signature switch
        {
            $"{V128UInt64} {Intrinsics}.Arm.AdvSimd::ExtractVector128({V128UInt64},{V128UInt64},System.Byte)" =>
                Finish(".advSimd .extract64", 3, Feature.AdvSimd),
            $"{V128UInt64} {Intrinsics}.Arm.AdvSimd::ReverseElement8({V128UInt64})" =>
                Finish(".advSimd .reverseElement8", 1, Feature.AdvSimd),
            $"{V128UInt64} {X86}.Sse2::ShiftLeftLogical128BitLane({V128UInt64},System.Byte)" =>
                Finish(".sse .shiftLeftBytes", 2, Feature.Sse2),
            $"{V128UInt64} {X86}.Sse2::Multiply({V128UInt32},{V128UInt32})" =>
                Finish(".sse .multiplyEven32", 2, Feature.Sse2),
            $"{V128Byte} {X86}.Ssse3::AlignRight({V128Byte},{V128Byte},System.Byte)" =>
                Finish(".sse .alignBytes", 3, Feature.Ssse3),
            $"{V128Byte} {X86}.Ssse3::Shuffle({V128Byte},{V128Byte})" =>
                Finish(".sse .shuffleBytes", 2, Feature.Ssse3),
            $"{V256Byte} {Avx2}::Shuffle({V256Byte},{V256Byte})" =>
                Finish(".avx2 .shuffleBytes", 2, Feature.Avx2),
            $"{V128Byte} {X86}.Aes::Encrypt({V128Byte},{V128Byte})" => Finish(".aes .encrypt", 2, Feature.Aes),
            $"{V128Byte} {Intrinsics}.Arm.Aes::Encrypt({V128Byte},{V128Byte})" =>
                Finish(".armAes .encrypt", 2, Feature.ArmAes),
            $"{V128Byte} {Intrinsics}.Arm.Aes::MixColumns({V128Byte})" =>
                Finish(".armAes .mixColumns", 1, Feature.ArmAes),
            $"{V256UInt64} {Avx2}::Permute4x64({V256UInt64},System.Byte)" =>
                Finish(".avx2 .permute4x64", 2, Feature.Avx2),
            $"{V256UInt32} {Avx2}::Blend({V256UInt32},{V256UInt32},System.Byte)" =>
                Finish(".avx2 .blend32", 3, Feature.Avx2),
            $"{V256Int32} {Avx2}::Blend({V256Int32},{V256Int32},System.Byte)" =>
                Finish(".avx2 .blend32", 3, Feature.Avx2),
            $"{V256UInt64} {Avx2}::Add({V256UInt64},{V256UInt64})" =>
                Finish(".avx2 .add64", 2, Feature.Avx2),
            $"{V256UInt64} {Avx2}::CompareEqual({V256UInt64},{V256UInt64})" =>
                Finish(".avx2 .eq64", 2, Feature.Avx2),
            $"{V256UInt64} {Avx2}::ShiftLeftLogical({V256UInt64},System.Byte)" =>
                Finish(".avx2 .shl64", 2, Feature.Avx2),
            $"{V256Int64} {Avx2}::CompareGreaterThan({V256Int64},{V256Int64})" =>
                Finish(".avx2 .signedgt64", 2, Feature.Avx2),
            $"{V256UInt64} {Avx2}::Multiply({V256UInt32},{V256UInt32})" =>
                Finish(".avx2 .multiplyEven32", 2, Feature.Avx2),
            $"{V256UInt64} {Avx2}::ShiftRightLogical({V256UInt64},System.Byte)" =>
                Finish(".avx2 .shr64", 2, Feature.Avx2),
            $"{V256UInt64} {Avx512FVL}::AlignRight64({V256UInt64},{V256UInt64},System.Byte)" =>
                Finish(".avx512 .alignRight64", 3, Feature.Avx512FVL),
            $"{V256UInt64} {Avx512FVL}::TernaryLogic({V256UInt64},{V256UInt64},{V256UInt64},System.Byte)" =>
                Finish(".avx512 .ternaryLogic", 4, Feature.Avx512FVL),
            $"{V256UInt64} {Avx512FVL}::PermuteVar4x64x2({V256UInt64},{V256UInt64},{V256UInt64})" =>
                Finish(".avx512 .permuteVar4x64x2", 3, Feature.Avx512FVL),
            $"{V256UInt64} {Avx512FVL}::CompareLessThan({V256UInt64},{V256UInt64})" =>
                Finish(".avx512 .ltu64", 2, Feature.Avx512FVL),
            $"{V256UInt64} {Avx512FVL}::CompareGreaterThan({V256UInt64},{V256UInt64})" =>
                Finish(".avx512 .gtu64", 2, Feature.Avx512FVL),
            $"{V256UInt64} {Avx512FVL}::CompareGreaterThanOrEqual({V256UInt64},{V256UInt64})" =>
                Finish(".avx512 .geu64", 2, Feature.Avx512FVL),
            $"System.Int32 {Avx512DQ}::MoveMask({V256UInt64})" =>
                Finish(".avx512DQ .moveMask64", 1, Feature.Avx512DQ),
            $"{V256UInt64} {Avx512DQ}/VL::MultiplyLow({V256UInt64},{V256UInt64})" =>
                Finish(".avx512DQ .mul64", 2, Feature.Avx512DQVL),
            $"System.Int32 {Avx}::MoveMask({V256Double})" => Finish(".avx .moveMask64", 1, Feature.Avx),
            $"System.Int32 {Avx}::MoveMask({V256Single})" => Finish(".avx .moveMask32", 1, Feature.Avx),
            $"{V256Single} {Avx}::Blend({V256Single},{V256Single},System.Byte)" =>
                Finish(".avx .blend32", 3, Feature.Avx),
            $"System.Boolean {Avx}::TestZ({V256UInt64},{V256UInt64})" => Finish(".avx .testZ64", 2, Feature.Avx),
            $"System.UInt32 {X86}.Bmi1::BitFieldExtract(System.UInt32,System.Byte,System.Byte)" =>
                Finish(".bmi1 .bextr32", 3, Feature.Bmi1),
            $"System.UInt64 {X86}.Bmi2/X64::MultiplyNoFlags(System.UInt64,System.UInt64)" =>
                Finish(".bmi2 .multiplyHigh64", 2, Feature.Bmi2),
            $"System.UInt64 {Intrinsics}.Arm.ArmBase/Arm64::MultiplyHigh(System.UInt64,System.UInt64)" =>
                Finish(".armBase64 .multiplyHigh64", 2, Feature.ArmBase64),
            $"{UInt64Pair} {X86}.X86Base/X64::DivRem(System.UInt64,System.UInt64,System.UInt64)" =>
                Require(new X86BaseDivRem64(), Feature.X86Base64),
            _ => null
        };
    }
}
