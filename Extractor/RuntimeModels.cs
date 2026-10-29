using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class RuntimeModels
{
    private static string Vector(int width, string element) => $"System.Runtime.Intrinsics.Vector{width}`1<{element}>";

    private static readonly Version RuntimeAssemblyVersion = new(10, 0, 0, 0);
    // The Open key signs System.Memory and System.Runtime.Intrinsics; the Microsoft key signs the rest.
    private const string OpenKeyToken = "cc7b13ffcd2ddd51";
    private const string MicrosoftKeyToken = "b03f5f7f11d50a3a";

    private static readonly int[] VectorWidths = [128, 256, 512];
    private static readonly string[] VectorElements =
    [
        "System.UInt64", "System.Int64", "System.UInt32", "System.Int32",
        "System.Byte", "System.Double", "System.Single"
    ];

    private const string Intrinsics = "System.Runtime.Intrinsics";
    private const string X86 = Intrinsics + ".X86";
    private const string Avx = X86 + ".Avx";
    private const string Avx2 = X86 + ".Avx2";
    private const string Avx512FVL = X86 + ".Avx512F/VL";
    private const string Avx512DQ = X86 + ".Avx512DQ";
    private const string V128Byte = Intrinsics + ".Vector128`1<System.Byte>";
    private const string V128UInt64 = Intrinsics + ".Vector128`1<System.UInt64>";
    private const string V256UInt64 = Intrinsics + ".Vector256`1<System.UInt64>";
    private const string V256UInt32 = Intrinsics + ".Vector256`1<System.UInt32>";
    private const string V256Int32 = Intrinsics + ".Vector256`1<System.Int32>";
    private const string V256Int64 = Intrinsics + ".Vector256`1<System.Int64>";
    private const string V256Double = Intrinsics + ".Vector256`1<System.Double>";
    private const string V256Single = Intrinsics + ".Vector256`1<System.Single>";
    private const string V512UInt64 = Intrinsics + ".Vector512`1<System.UInt64>";
    private const string UInt64Pair = "System.ValueTuple`2<System.UInt64,System.UInt64>";
    private const string Unsafe = "System.Runtime.CompilerServices.Unsafe";

    internal static bool ExactScope(IMetadataScope scope, string name) => scope is AssemblyNameReference assembly &&
        assembly.Name == name && assembly.Version == RuntimeAssemblyVersion &&
        string.IsNullOrEmpty(assembly.Culture) && Convert.ToHexString(assembly.PublicKeyToken).ToLowerInvariant() ==
            (name is "System.Runtime.Intrinsics" or "System.Memory" ? OpenKeyToken : MicrosoftKeyToken);

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
        type.BaseType is { FullName: "System.ValueType" } parent && ExactScope(parent.Scope, "System.Runtime");

    internal static void ValidateTypeIdentity(TypeReference type, ModuleDefinition module,
        string architecture = "scalar")
    {
        if (type.Scope == module && type.IsValueType && type is not TypeSpecification)
        {
            if (EnumTypes.IsEnum(type)) EnumTypes.Storage(type);
            else MetadataValidation.Layout(type, module, architecture);
            return;
        }
        if (type is GenericParameter) return;
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
        bool valid = type.IsValueType == expectedValueType && ExactScope(type.Scope, expectedScope) &&
            (type.FullName != "System.Void" || type.MetadataType == MetadataType.Void);
        if (!valid) throw new InvalidDataException($"Unsupported type identity: {type.FullName} [{type.Scope}]");
    }

    private static bool IsModeledValueType(string name) => name is "System.UInt64" or "System.Int64" or
        "System.SByte" or "System.Int16" or "System.UInt16" or "System.Char" or
        "System.UInt32" or "System.Int32" or "System.Byte" or "System.Boolean" or "System.Double" or "System.Single" or
        "System.IntPtr" or "System.UIntPtr" or "System.ReadOnlySpan`1" or "System.Span`1" or "System.RuntimeFieldHandle" or
        "System.Runtime.Intrinsics.Vector128`1" or "System.Runtime.Intrinsics.Vector256`1" or
        "System.Runtime.Intrinsics.Vector512`1" or "System.ValueTuple`2";

    private static string DefiningAssembly(string name) =>
        name is "System.Buffers.Binary.BinaryPrimitives" or "System.MemoryExtensions" ? "System.Memory" :
        name.StartsWith("System.Runtime.Intrinsics.", StringComparison.Ordinal) ? "System.Runtime.Intrinsics" :
        "System.Runtime";

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

    internal static string? Translate(MethodReference reference, FeatureProfile profile)
    {
        if (reference.ExplicitThis || reference.CallingConvention == MethodCallingConvention.VarArg ||
            (reference.HasThis && reference.Name is not
                (".ctor" or "get_Item" or "get_Length" or "Slice" or "Clear" or "Fill" or
                 "CopyTo" or "TryCopyTo" or "get_IsEmpty" or "GetPinnableReference")) ||
            (reference.Name == ".ctor" && !reference.HasThis)) return null;
        string scope = reference.DeclaringType.Scope.Name;
        if (scope is "System.Runtime" or "System.Runtime.Intrinsics" or "System.Memory" &&
            !ExactScope(reference.DeclaringType.Scope, scope))
            throw new InvalidDataException(
                $"Unsupported runtime assembly scope: {reference.FullName} [{reference.DeclaringType.Scope}]");
        string? op = scope switch
        {
            "System.Runtime" => Scalar(reference)
                ?? SpanReinterpretation.Translate(reference, profile.Architecture)
                ?? MemoryTransfers.Marshal(reference, profile.Architecture)
                ?? ValueBitCasts.Translate(reference, profile.Architecture)
                ?? UnsafeModels.Translate(reference, profile.Architecture)
                ?? ElementSpan(reference, profile.Architecture) ?? Runtime(reference.FullName),
            "System.Memory" => Scalar(reference) ?? BinaryTransfers.Translate(reference) ??
                ElementSpan(reference, profile.Architecture) ?? Span(reference.FullName),
            "System.Runtime.Intrinsics" => Intrinsic(reference.FullName, profile),
            _ => null
        };
        if (op is not null) ValidateSignature(reference, profile.Architecture);
        if (op == DivRem) ValueTuples.RequireWordPair(reference.ReturnType, reference.Module, profile.Architecture);
        return op;
    }

    const string DivRem = ".intrinsic (.x86Base .divRem64) 3";

    private static readonly (string Type, int Width, bool Signed)[] MathIntegers =
    [
        ("System.SByte", 8, true), ("System.Byte", 8, false),
        ("System.Int16", 16, true), ("System.UInt16", 16, false),
        ("System.Int32", 32, true), ("System.UInt32", 32, false),
        ("System.Int64", 64, true), ("System.UInt64", 64, false),
        ("System.IntPtr", 64, true), ("System.UIntPtr", 64, false)
    ];
    private static readonly (string Name, string Operation, int Arity)[] MathOperations =
    [
        ("Min", "min", 2), ("Max", "max", 2), ("Clamp", "clamp", 3),
        ("Abs", "abs", 1), ("Sign", "sign", 1)
    ];
    private static readonly (string Type, int Width)[] RotatableWords =
        [("System.UInt32", 32), ("System.UInt64", 64), ("System.UIntPtr", 64)];
    private static readonly (string Name, string Operation)[] Rotations =
        [("RotateLeft", "rotateLeft"), ("RotateRight", "rotateRight")];
    private static readonly (string Name, string Operation)[] BitCounts =
    [
        ("PopCount", "popCount"), ("LeadingZeroCount", "leadingZeroCount"),
        ("TrailingZeroCount", "trailingZeroCount"), ("Log2", "log2")
    ];
    private static readonly (string Type, int Width, bool Signed)[] Pow2Integers =
    [
        ("System.Int32", 32, true), ("System.UInt32", 32, false),
        ("System.Int64", 64, true), ("System.UInt64", 64, false),
        ("System.IntPtr", 64, true), ("System.UIntPtr", 64, false)
    ];
    private static readonly (string Type, int Width, bool Signed)[] ByteAndNativeIntegers =
    [
        ("System.SByte", 8, true), ("System.Byte", 8, false),
        ("System.IntPtr", 64, true), ("System.UIntPtr", 64, false)
    ];

    // Match exact non-generic static signatures, including the defining assembly.
    private static string? Scalar(MethodReference reference)
    {
        if (reference.HasThis || reference.HasGenericParameters || reference is GenericInstanceMethod ||
            reference.CallingConvention != MethodCallingConvention.Default) return null;
        return reference.DeclaringType.Scope.Name switch
        {
            "System.Runtime" => RuntimeScalar(reference.FullName),
            "System.Memory" => ReverseEndianness(reference.FullName),
            _ => null
        };
    }

    // System.Math and System.Numerics.BitOperations, both defined in System.Runtime.
    private static string? RuntimeScalar(string signature)
    {
        if (signature == "System.UInt64 System.Math::BigMul(System.UInt64,System.UInt64,System.UInt64&)")
            return ".memory .bigMul64";
        foreach (var (type, width, signed) in MathIntegers)
        foreach (var (name, operation, arity) in MathOperations)
        {
            if (!signed && arity == 1) continue;
            var result = name == "Sign" ? "System.Int32" : type;
            var parameters = string.Join(",", Enumerable.Repeat(type, arity));
            if (signature == $"{result} System.Math::{name}({parameters})")
                return $".intrinsic (.scalar (.math .{operation} {width} {LeanBool(signed)})) {arity}";
        }
        foreach (var (type, width) in RotatableWords)
        {
            foreach (var (name, operation) in Rotations)
                if (signature == $"{type} System.Numerics.BitOperations::{name}({type},System.Int32)")
                    return $".intrinsic (.scalar (.{operation} {width})) 2";
            foreach (var (name, operation) in BitCounts)
                if (signature == $"System.Int32 System.Numerics.BitOperations::{name}({type})")
                    return $".intrinsic (.scalar (.{operation} {width})) 1";
            if (signature == $"{type} System.Numerics.BitOperations::RoundUpToPowerOf2({type})")
                return $".intrinsic (.scalar (.roundUpToPowerOf2 {width})) 1";
        }
        foreach (var (type, width, signed) in Pow2Integers)
            if (signature == $"System.Boolean System.Numerics.BitOperations::IsPow2({type})")
                return $".intrinsic (.scalar (.isPow2 {width} {LeanBool(signed)})) 1";
        return null;
    }

    // System.Buffers.Binary.BinaryPrimitives, defined in System.Memory.
    private static string? ReverseEndianness(string signature)
    {
        foreach (var (type, width, signed) in ByteAndNativeIntegers)
            if (signature == $"{type} System.Buffers.Binary.BinaryPrimitives::ReverseEndianness({type})")
                return $".intrinsic (.scalar (.reverseEndianness {width} {LeanBool(signed)})) 1";
        foreach (var width in new[] { 16, 32, 64 })
        foreach (var signed in new[] { false, true })
        {
            var type = $"System.{(signed ? "Int" : "UInt")}{width}";
            if (signature == $"{type} System.Buffers.Binary.BinaryPrimitives::ReverseEndianness({type})")
                return $".intrinsic (.scalar (.reverseEndianness {width} {LeanBool(signed)})) 1";
        }
        return null;
    }

    private static string LeanBool(bool value) => value.ToString().ToLowerInvariant();

    private static string? Runtime(string signature) => signature switch
    {
        $"System.Void {Unsafe}::CopyBlock(System.Byte&,System.Byte&,System.UInt32)" => ".memory (.copyBlock 8)",
        $"System.Void {Unsafe}::CopyBlockUnaligned(System.Byte&,System.Byte&,System.UInt32)" =>
            ".memory (.copyBlock 1)",
        $"System.Void {Unsafe}::InitBlock(System.Byte&,System.Byte,System.UInt32)" => ".memory (.initBlock 8)",
        $"System.Void {Unsafe}::InitBlockUnaligned(System.Byte&,System.Byte,System.UInt32)" => ".memory (.initBlock 1)",
        $"!!1 {Unsafe}::BitCast<System.Byte,System.Boolean>(!!0)" => ".memory .bitcastByteBool",
        "System.Void System.ReadOnlySpan`1<System.Byte>::.ctor(System.Void*,System.Int32)" => ".memory .spanCreate",
        _ => Span(signature)
    };

    private static readonly Dictionary<string, string> SpanOperations = BuildSpanOperations();

    // Signatures are immutable: runtime lookup performs no interpolation or per-element scan.
    private static string? Span(string signature) => SpanOperations.GetValueOrDefault(signature);

    private sealed class ElementSpanOperations
    {
        internal readonly Dictionary<string, Dictionary<string, string>> Architectures = new(StringComparer.Ordinal);
    }

    private static string? ElementSpan(MethodReference method, string architecture)
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

    private static Dictionary<string, string> BuildSpanOperations(
        TypeReference? elementType = null, string architecture = "scalar")
    {
        var operations = new Dictionary<string, string>(StringComparer.Ordinal);
        var primitives = new[]
        {
            ("System.Byte", 1), ("System.SByte", 1), ("System.Int16", 2), ("System.UInt16", 2),
            ("System.Int32", 4), ("System.UInt32", 4), ("System.Int64", 8), ("System.UInt64", 8),
            ("System.IntPtr", 8), ("System.UIntPtr", 8), ("System.Char", 2), ("System.Boolean", 1)
        };
        foreach (var (element, width) in elementType is null ? primitives :
            [(elementType.FullName, Spans.ElementWidth(elementType, architecture)!.Value)])
        {
            var arrayElement = (elementType is null ? Arrays.Primitive(element) :
                Arrays.Storage(elementType, architecture))?.Expression;
            var span = $"System.ReadOnlySpan`1<{element}>";
            if (arrayElement is not null) operations.Add("System.ReadOnlySpan`1<!!0> System.Runtime.CompilerServices.RuntimeHelpers::" +
                $"CreateSpan<{element}>(System.RuntimeFieldHandle)", $".memory (.createSpan {width})");
            operations.Add($"!0& modreq(System.Runtime.InteropServices.InAttribute) {span}::get_Item(System.Int32)",
                $".memory (.spanItem {width})");
            operations.Add("!!0& System.Runtime.InteropServices.MemoryMarshal::" +
                $"GetReference<{element}>(System.ReadOnlySpan`1<!!0>)", ".memory .spanReference");
            foreach (var name in new[] { "System.Span`1", "System.ReadOnlySpan`1" })
            {
                var owner = $"{name}<{element}>";
                var writable = name == "System.Span`1";
                var capability = writable ? "true" : "false";
                var arrayWhole = $".memory (.arraySpan {arrayElement} {capability} .whole)";
                if (arrayElement is not null) operations.Add($"System.Void {owner}::.ctor(!0[])", arrayWhole);
                if (arrayElement is not null) operations.Add($"{name}<!0> {owner}::op_Implicit(!0[])", arrayWhole);
                if (arrayElement is not null) operations.Add($"System.Void {owner}::.ctor(!0[],System.Int32,System.Int32)",
                    $".memory (.arraySpan {arrayElement} {capability} .counted)");
                operations.Add($"System.Void {owner}::.ctor(System.Void*,System.Int32)",
                    $".memory (.spanFromReference {width} {capability})");
                operations.Add($"System.Void {owner}::.ctor(!0&)",
                    $".memory (.spanSingleReference {width} {capability})");
                operations.Add($"System.Int32 {owner}::get_Length()", ".memory .spanLength");
                operations.Add($"System.Boolean {owner}::get_IsEmpty()", ".memory (.observeView .spanEmpty)");
                var pinnableResult = writable ? "!0&" :
                    "!0& modreq(System.Runtime.InteropServices.InAttribute)";
                operations.Add($"{pinnableResult} {owner}::GetPinnableReference()",
                    ".memory (.observeView .spanPinnable)");
                operations.Add($"System.Void {owner}::CopyTo(System.Span`1<!0>)",
                    $".memory (.spanCopy {width} false)");
                operations.Add($"System.Boolean {owner}::TryCopyTo(System.Span`1<!0>)",
                    $".memory (.spanCopy {width} true)");
                if (writable)
                {
                    operations.Add($"!0& {owner}::get_Item(System.Int32)", $".memory (.spanItem {width})");
                    operations.Add($"System.Void {owner}::Clear()", $".memory (.spanFill {width} true)");
                    operations.Add($"System.Void {owner}::Fill(!0)", $".memory (.spanFill {width} false)");
                }
                operations.Add($"{name}<!0> {owner}::Slice(System.Int32)", ".memory (.spanSlice false)");
                operations.Add($"{name}<!0> {owner}::Slice(System.Int32,System.Int32)", ".memory (.spanSlice true)");
                var factory = writable ? "CreateSpan" : "CreateReadOnlySpan";
                operations.Add($"{name}<!!0> System.Runtime.InteropServices.MemoryMarshal::" +
                    $"{factory}<{element}>(!!0&,System.Int32)",
                    $".memory (.spanFromReference {width} {capability})");
            }
            operations.Add($"System.ReadOnlySpan`1<!0> System.Span`1<{element}>::" +
                "op_Implicit(System.Span`1<!0>)", ".memory .spanReadOnly");
            operations.Add("!!0& System.Runtime.InteropServices.MemoryMarshal::" +
                $"GetArrayDataReference<{element}>(!!0[])", ".memory (.observeView .arrayData)");
            foreach (var (parameters, range) in new[]
            {
                ("!!0[]", "whole"), ("!!0[],System.Int32", "fromStart"),
                ("!!0[],System.Int32,System.Int32", "counted")
            })
                if (arrayElement is not null) operations.Add("System.Span`1<!!0> System.MemoryExtensions::" +
                    $"AsSpan<{element}>({parameters})", $".memory (.arraySpan {arrayElement} true .{range})");
        }
        return operations;
    }

    private static string? Intrinsic(string signature, FeatureProfile profile)
    {
        string? Finish(string intrinsic, int argc, Feature? required = null)
        {
            if (required is Feature feature && !profile.Get(feature))
                throw new InvalidDataException($"Reachable intrinsic lacks {feature}: {signature}");
            return $".intrinsic ({intrinsic}) {argc}";
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
        if (signature == $"{V512UInt64} {Intrinsics}.Vector512::Create({V256UInt64},{V256UInt64})")
            return Finish(".vector .combine256", 2);
        if (signature == $"{V128UInt64} {Intrinsics}.Vector128::CreateScalarUnsafe(System.UInt64)")
            return Finish(".vector .createScalarUnsafe64", 1);
        foreach (int width in new[] { 128, 256 })
        {
            string ulongVector = Vector(width, "System.UInt64");
            string genericVector = Vector(width, "!!0");
            string memberVector = Vector(width, "!0");
            string owner = $"System.Runtime.Intrinsics.Vector{width}";
            string genericOwner = Vector(width, "System.UInt64");
            foreach ((string name, string op) in new[] { ("op_Addition", "add64"), ("op_Subtraction", "sub64"),
                ("op_BitwiseAnd", "band"), ("op_BitwiseOr", "bor"), ("op_ExclusiveOr", "bxor") })
                if (signature == $"{memberVector} {genericOwner}::{name}({memberVector},{memberVector})")
                    return Finish($".vector (.{op} {width})", 2);
            foreach (string element in new[] { "System.UInt64", "System.UInt32", "System.Int32" })
            {
                string vectorOwner = Vector(width, element);
                foreach ((string name, string op) in new[]
                    { ("op_BitwiseAnd", "band"), ("op_BitwiseOr", "bor"), ("op_ExclusiveOr", "bxor") })
                    if (signature == $"{memberVector} {vectorOwner}::{name}({memberVector},{memberVector})")
                        return Finish($".vector (.{op} {width})", 2);
                if (signature == $"System.Boolean {vectorOwner}::op_Equality({memberVector},{memberVector})")
                    return Finish($".vector (.equalsAll {width})", 2);
                if (signature == $"{memberVector} {vectorOwner}::op_OnesComplement({memberVector})")
                    return Finish($".vector (.bnot {width})", 1);
            }
            foreach ((string name, string op) in new[] { ("LessThan", "ltu64"), ("Equals", "eq64") })
                if (signature == $"{genericVector} {owner}::{name}<System.UInt64>({genericVector},{genericVector})")
                    return Finish($".vector (.{op} {width})", 2);
            if (signature == $"System.Boolean {owner}::EqualsAll<System.UInt64>({genericVector},{genericVector})")
                return Finish($".vector (.equalsAll {width})", 2);
            if (signature == $"!!0 {owner}::GetElement<System.UInt64>({genericVector},System.Int32)")
                return Finish($".vector (.extract64 {width})", 2);
            foreach (string element in new[] { "System.UInt64", "System.UInt32" })
                if (signature == $"{memberVector} {Vector(width, element)}::get_Zero()")
                    return Finish($".vector (.zero {width})", 0);
            if (signature == $"{memberVector} {genericOwner}::get_AllBitsSet()")
                return Finish($".vector (.ones {width})", 0);
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
            string elementwise = string.Join(",", Enumerable.Repeat("System.UInt64", width / 64));
            if (signature == $"{ulongVector} {owner}::Create({elementwise})")
                return Finish($".vector (.create64 {width})", width / 64);
            if (signature == $"{ulongVector} {owner}::Create(System.UInt64)")
                return Finish($".vector (.create64 {width})", 1);
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
            $"{V128UInt64} {X86}.Sse2::ShiftLeftLogical128BitLane({V128UInt64},System.Byte)" =>
                Finish(".sse .shiftLeftBytes", 2, Feature.Sse2),
            $"{V128Byte} {X86}.Ssse3::AlignRight({V128Byte},{V128Byte},System.Byte)" =>
                Finish(".sse .alignBytes", 3, Feature.Ssse3),
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
                Finish(".x86Base .divRem64", 3, Feature.X86Base64),
            _ => null
        };
    }
}
