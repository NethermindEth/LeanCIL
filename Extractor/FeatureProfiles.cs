using Mono.Cecil;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace Nethermind.LeanCIL;

internal enum Feature
{
    AdvSimd, Sse2, Ssse3, Sse42, Avx, Avx2, Avx512F, Avx512FVL, Bmi1,
    Sse41, Avx512DQ, Avx512DQVL, Bmi2, ArmBase64, Vector256Accelerated,
    X86Base64, Vector128Accelerated
}

// Runtime-visible capabilities for .NET 10 CoreCLR, including runtime disabling.
// Group constraints and measured x64/arm64 evidence are recorded in docs/RUNTIME-PROFILES.md.
internal sealed record FeatureProfile(string Name, string Architecture, int NativeWidth,
    bool LittleEndian, bool AdvSimd = false, bool Sse2 = false, bool Ssse3 = false,
    bool Sse42 = false, bool Avx = false, bool Avx2 = false,
    bool Avx512F = false, bool Avx512FVL = false, bool Bmi1 = false,
    bool Sse41 = false, bool Avx512DQ = false, bool Avx512DQVL = false,
    bool Bmi2 = false, bool ArmBase64 = false, bool Vector256Accelerated = false,
    bool X86Base64 = false, bool Vector128Accelerated = false)
{
    internal static FeatureProfile Scalar { get; } = new("scalar", "scalar", 64, true);

    internal bool Get(Feature feature) => feature switch
    {
        Feature.AdvSimd => AdvSimd, Feature.Sse2 => Sse2, Feature.Ssse3 => Ssse3,
        Feature.Sse42 => Sse42, Feature.Avx => Avx, Feature.Avx2 => Avx2,
        Feature.Avx512F => Avx512F, Feature.Avx512FVL => Avx512FVL,
        Feature.Bmi1 => Bmi1, Feature.Sse41 => Sse41, Feature.Avx512DQ => Avx512DQ,
        Feature.Avx512DQVL => Avx512DQVL, Feature.Bmi2 => Bmi2, Feature.ArmBase64 => ArmBase64,
        Feature.Vector256Accelerated => Vector256Accelerated,
        Feature.X86Base64 => X86Base64, Feature.Vector128Accelerated => Vector128Accelerated,
        _ => throw new InvalidDataException($"Unknown feature: {feature}")
    };

    internal void Validate()
    {
        if (string.IsNullOrWhiteSpace(Name) || NativeWidth != 64 || !LittleEndian || Architecture is not ("scalar" or "arm64" or "x64") ||
            ((AdvSimd || ArmBase64) && Architecture != "arm64") ||
            (X86Base64 && Architecture != "x64") ||
            (Ssse3 && !Sse2) || (Sse42 && (!Sse2 || !Ssse3)) ||
            (Avx2 && !Avx) || (Avx512FVL && !Avx512F) ||
            (Avx && !Sse42) || (Avx512F && !Avx2) ||
            (Sse41 && !Ssse3) || (Sse42 && !Sse41) ||
            (Avx512DQ && !Avx512F) || (Avx512DQVL && (!Avx512DQ || !Avx512FVL)) ||
            (AdvSimd && !ArmBase64))
            throw new InvalidDataException($"Invalid execution profile: {Name}");
        // Every x86 ISA class derives from X86Base.
        if ((Sse2 || Ssse3 || Sse42 || Avx || Avx2 || Avx512F || Avx512FVL || Bmi1 || Sse41 || Avx512DQ || Avx512DQVL || Bmi2) && !X86Base64)
            throw new InvalidDataException($"Invalid execution profile: {Name}: x86 ISA flags require x86Base64");
        if (Sse2 != X86Base64 || Ssse3 != Sse41 || Sse41 != Sse42 ||
            Avx2 != Bmi1 || Avx2 != Bmi2 ||
            Avx512F != Avx512FVL || Avx512F != Avx512DQ || Avx512F != Avx512DQVL ||
            AdvSimd != ArmBase64 || Vector128Accelerated != (Sse2 || AdvSimd) ||
            (Vector256Accelerated && !Avx2))
            throw new InvalidDataException($"Invalid execution profile: {Name}: capabilities split a .NET 10 CoreCLR runtime group; see docs/RUNTIME-PROFILES.md");
    }

    internal static FeatureProfile Select(string name)
    {
        if (name.StartsWith('@'))
        {
            JsonSerializerOptions options = new()
            {
                PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
                UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow
            };
            using JsonDocument document = JsonDocument.Parse(File.ReadAllText(name[1..]));
            string[] expected = JsonSerializer.SerializeToElement(Scalar, options).EnumerateObject()
                .Select(p => p.Name).Order().ToArray();
            string[] actual = document.RootElement.EnumerateObject().Select(p => p.Name).Order().ToArray();
            if (!actual.SequenceEqual(expected))
                throw new InvalidDataException("Execution profile requires every exact capability field");
            FeatureProfile selected = document.RootElement.Deserialize<FeatureProfile>(options)
                ?? throw new InvalidDataException("Missing execution profile");
            selected.Validate();
            return selected;
        }
        FeatureProfile profile = name switch
        {
            "scalar" => Scalar,
            "arm64-advsimd" => new(name, "arm64", 64, true, AdvSimd: true, ArmBase64: true, Vector128Accelerated: true),
            "x64-sse2" => new(name, "x64", 64, true, Sse2: true, X86Base64: true, Vector128Accelerated: true),
            "x64-sse42" => new(name, "x64", 64, true, Sse2: true, Ssse3: true, Sse41: true, Sse42: true, X86Base64: true, Vector128Accelerated: true),
            // .NET 10 enables x86-64-v3 (AVX2 with BMI1/BMI2) and v4 (AVX-512 F/DQ/VL) only as whole groups.
            "x64-v3" or "x64-v4" => new(name, "x64", 64, true,
                Sse2: true, Ssse3: true, Sse41: true, Sse42: true, Avx: true, Avx2: true, Bmi1: true, Bmi2: true,
                Avx512F: name == "x64-v4", Avx512FVL: name == "x64-v4", Avx512DQ: name == "x64-v4", Avx512DQVL: name == "x64-v4",
                X86Base64: true, Vector128Accelerated: true, Vector256Accelerated: true),
            "x64-avx2" or "x64-avx2-bmi1" or "x64-bmi2" or "x64-vector256" =>
                throw new ArgumentException($"Retired execution profile: {name}; migrate to x64-v3 and reverify (docs/RUNTIME-PROFILES.md)"),
            "x64-avx512" or "x64-avx512-bmi1" =>
                throw new ArgumentException($"Retired execution profile: {name}; migrate to x64-v4 and reverify (docs/RUNTIME-PROFILES.md)"),
            "x64-sse41" => throw new ArgumentException($"Retired execution profile: {name}; migrate to x64-sse42 and reverify (docs/RUNTIME-PROFILES.md)"),
            "arm64-armbase" => throw new ArgumentException($"Retired execution profile: {name}; migrate to arm64-advsimd and reverify (docs/RUNTIME-PROFILES.md)"),
            _ => throw new ArgumentException($"Unknown execution profile: {name}")
        };
        profile.Validate();
        return profile;
    }

    internal string Lean => $"{{ architecture := .{Architecture}, nativeWidth := {NativeWidth}, littleEndian := {Bool(LittleEndian)}, " +
        $"advSimd := {Bool(AdvSimd)}, sse2 := {Bool(Sse2)}, ssse3 := {Bool(Ssse3)}, sse42 := {Bool(Sse42)}, " +
        $"avx := {Bool(Avx)}, avx2 := {Bool(Avx2)}, avx512F := {Bool(Avx512F)}, avx512FVL := {Bool(Avx512FVL)}, bmi1 := {Bool(Bmi1)}, " +
        $"sse41 := {Bool(Sse41)}, avx512DQ := {Bool(Avx512DQ)}, avx512DQVL := {Bool(Avx512DQVL)}, " +
        $"bmi2 := {Bool(Bmi2)}, armBase64 := {Bool(ArmBase64)}, vector256Accelerated := {Bool(Vector256Accelerated)}, " +
        $"x86Base64 := {Bool(X86Base64)}, vector128Accelerated := {Bool(Vector128Accelerated)} }}";

    internal static string LeanFeature(Feature feature) =>
        "." + char.ToLowerInvariant(feature.ToString()[0]) + feature.ToString()[1..];

    private static string Bool(bool value) => value ? "true" : "false";

    internal static int? PlatformConstant(MethodReference reference)
    {
        var pointerSize = reference.Name == "get_Size" &&
            reference.DeclaringType.FullName is "System.IntPtr" or "System.UIntPtr";
        var processWidth = reference.Name == "get_Is64BitProcess" &&
            reference.DeclaringType.FullName == "System.Environment";
        if (!pointerSize && !processWidth) return null;
        var result = pointerSize ? "System.Int32" : "System.Boolean";
        if (!RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") ||
            reference.HasThis || reference.ExplicitThis || reference.CallingConvention != MethodCallingConvention.Default ||
            reference.HasGenericParameters || reference is GenericInstanceMethod || reference.Parameters.Count != 0 ||
            reference.FullName != $"{result} {reference.DeclaringType.FullName}::{reference.Name}()")
            throw new InvalidDataException($"Unsupported platform getter: {reference.FullName}");
        RuntimeModels.ValidateSignature(reference);
        return pointerSize ? 8 : 1;
    }

    /// <summary>Whether a field load is named <c>BitConverter.IsLittleEndian</c>, before identity checks.</summary>
    internal static bool PlatformFieldQuery(FieldReference reference) =>
        reference.Name == "IsLittleEndian" && reference.DeclaringType.FullName == "System.BitConverter";

    /// <summary>
    /// The value of the exact System.Runtime <c>BitConverter.IsLittleEndian</c> field;
    /// <see cref="Validate"/> admits only little-endian profiles. Lookalike identities throw.
    /// </summary>
    internal static int? PlatformField(FieldReference reference)
    {
        if (!PlatformFieldQuery(reference)) return null;
        const string identity = "System.Boolean System.BitConverter::IsLittleEndian";
        var exactReference = reference.DeclaringType is not TypeSpecification &&
            RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") &&
            RuntimeModels.ExactScope(reference.FieldType.Scope, "System.Runtime") && reference.FullName == identity;
        // Resolve only exact references: a forged assembly scope must not reach the resolver.
        var field = exactReference ? reference.Resolve() : null;
        if (field is null || field.FullName != identity ||
            !field.IsStatic || !field.IsInitOnly || !field.IsPublic || field.HasConstant ||
            (field.Attributes & FieldAttributes.HasFieldRVA) != 0)
            throw new InvalidDataException($"Unsupported static field load: {reference.FullName} " +
                $"[{reference.DeclaringType.Scope.Name}]\n  Only System.Runtime's static readonly " +
                "BitConverter.IsLittleEndian is a platform constant.");
        return 1;
    }

    internal static Feature? Getter(MethodReference reference)
    {
        if (reference.Name is not ("get_IsSupported" or "get_IsHardwareAccelerated") ||
            !reference.DeclaringType.FullName.StartsWith("System.Runtime.Intrinsics.", StringComparison.Ordinal)) return null;
        // Never reinterpret an unrecognised getter as a disabled capability.
        if (!RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime.Intrinsics") ||
            reference.HasThis || reference.ExplicitThis || reference.CallingConvention != MethodCallingConvention.Default ||
            reference.HasGenericParameters || reference.Parameters.Count != 0 ||
            reference.ReturnType.FullName != "System.Boolean" ||
            reference.FullName != $"System.Boolean {reference.DeclaringType.FullName}::{reference.Name}()")
            throw new InvalidDataException($"Unsupported feature getter: {reference.FullName} [{reference.DeclaringType.Scope.Name}]");
        RuntimeModels.ValidateSignature(reference);
        return reference.DeclaringType.FullName switch
        {
            "System.Runtime.Intrinsics.Vector128" when reference.Name == "get_IsHardwareAccelerated" => Feature.Vector128Accelerated,
            "System.Runtime.Intrinsics.Vector256" when reference.Name == "get_IsHardwareAccelerated" => Feature.Vector256Accelerated,
            _ when reference.Name != "get_IsSupported" => throw new InvalidDataException($"Unclassified feature getter: {reference.FullName}"),
            // .NET 10 sets AdvSimd_Arm64 exactly when AdvSimd is set on ARM64; see docs/RUNTIME-PROFILES.md.
            "System.Runtime.Intrinsics.Arm.AdvSimd" or "System.Runtime.Intrinsics.Arm.AdvSimd/Arm64" => Feature.AdvSimd,
            "System.Runtime.Intrinsics.Arm.ArmBase/Arm64" => Feature.ArmBase64,
            "System.Runtime.Intrinsics.X86.Sse2" => Feature.Sse2,
            "System.Runtime.Intrinsics.X86.Ssse3" => Feature.Ssse3,
            "System.Runtime.Intrinsics.X86.Sse42" => Feature.Sse42,
            "System.Runtime.Intrinsics.X86.Sse41" => Feature.Sse41,
            "System.Runtime.Intrinsics.X86.Avx" => Feature.Avx,
            "System.Runtime.Intrinsics.X86.Avx2" => Feature.Avx2,
            "System.Runtime.Intrinsics.X86.Avx512F" => Feature.Avx512F,
            "System.Runtime.Intrinsics.X86.Avx512F/VL" => Feature.Avx512FVL,
            "System.Runtime.Intrinsics.X86.Bmi1" => Feature.Bmi1,
            "System.Runtime.Intrinsics.X86.Bmi2/X64" => Feature.Bmi2,
            "System.Runtime.Intrinsics.X86.X86Base/X64" => Feature.X86Base64,
            "System.Runtime.Intrinsics.X86.Avx512DQ" => Feature.Avx512DQ,
            "System.Runtime.Intrinsics.X86.Avx512DQ/VL" => Feature.Avx512DQVL,
            _ => throw new InvalidDataException($"Unclassified feature getter: {reference.FullName}")
        };
    }
}
