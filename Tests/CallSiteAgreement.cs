#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Text;

var output = At("artifacts/CallSiteAgreement");
var assembly = At("Examples/Assembly/bin/Examples.dll");
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.Extraction.DecodedDefinition");
CallWitness[] witnesses =
[
    new("integerModel", "IntegerMath::AbsInt32(System.Int32)",
        0, 1, ".model"),
    new("binary", "BinarySpans::ReadBig(System.ReadOnlySpan`1<System.Byte>)",
        0, 1, ".model"),
    new("arrayDataModel", "ViewAccessors::ArrayData(System.Int32[])",
        0, 1, ".model"),
    new("marshal", "MarshaledMemory::Read(System.ReadOnlySpan`1<System.Byte>)",
        0, 1, ".model"),
    new("pointerOffset", "UnsafeReferences::AddPointer(System.Byte*,System.Int32)",
        0, 2, ".model"),
    new("unsafeTransfer", "UnalignedMemory::ReadWord(System.Byte&)",
        0, 1, ".model"),
    new("bitCast", "ValueBitCasts::From128Byte(System.Runtime.Intrinsics.Vector128`1<System.Byte>)",
        0, 1, ".model"),
    new("asReference", "UnsafeReferences::Word(Examples.FourLimbs&)",
        0, 1, ".model"),
    new("sizeOf", "UnsafeLayouts::Size0()",
        0, 0, ".model"),
    new("bigMul", "WideProduct::UnsignedBigMul32(System.UInt32,System.UInt32)",
        0, 2, ".model"),
    new("divRem", "TupleDivision::MathQuotient(System.Int32,System.Int32)",
        0, 2, ".model"),
    new("spanReference", "StaticSpans::First()",
        0, 1, ".model"),
    new("skipInit", "SkipInitialization::Skip(Examples.FourLimbs&)",
        0, 1, ".model"),
    new("spanItem", "MemorySpans::Read(System.ReadOnlySpan`1<System.Int32>,System.Int32)", 0, 2, ".model"),
    new("spanSlice",
        "MemorySpans::SliceRead(System.ReadOnlySpan`1<System.Int32>,System.Int32,System.Int32,System.Int32)",
        0, 3, ".model"),
    new("spanLength", "SpanReferences::Length(System.ReadOnlySpan`1<System.Int32>&)", 0, 1, ".model"),
    new("spanIsEmpty", "ViewAccessors::Empty(System.Span`1<System.Int32>)", 0, 1, ".model"),
    new("spanPinnable", "ViewAccessors::PinnableNull(System.Span`1<System.Int32>)", 0, 1, ".model"),
    new("spanReadOnly",
        "EnumBuffers::SpanRoundtrip(Examples.EnumBuffers/Small[],System.Int32,Examples.EnumBuffers/Small)",
        0, 10, ".model"),
    new("spanEmpty", "SpanConstructors::ReadOnlyEmpty()", 0, 0, ".model"),
    new("arrayConversion", "MemorySpans::ArrayReadOnly(System.Int32[])", 0, 1, ".model"),
    new("asSpan", "MemorySpans::ArrayAsSpan(System.Boolean[])", 0, 1, ".model"),
    new("objectModel", "VirtualCalls::DogLegs()",
        4, 1, ".model"),
    new("throwConstructor", "Throws::Inner(System.UInt32)",
        0, 4, ".refused"),
    new("typeTest", "TypeTests::Marker(System.Int32)",
        1, 4, ".refused"),
    new("feature", "Capabilities::AesFlags()",
        0, 0, ".model"),
    new("aesX64", "Capabilities::AesFlags()", 0, 3, ".model"),
    new("armAes", "Capabilities::AesFlags()", 0, 9, ".model"),
    new("armAes64", "Capabilities::AesFlags()", 0, 15, ".model"),
    new("armSimd64", "Capabilities::ArmFlags()", 0, 0, ".model"),
    new("armSimd", "Capabilities::ArmFlags()", 0, 3, ".model"),
    new("vbmiVl", "Capabilities::VbmiFlags()", 0, 0, ".model"),
    new("vbmi", "Capabilities::VbmiFlags()", 0, 3, ".model"),
    new("x86Base64", "Capabilities::Flags()", 0, 0, ".model"),
    new("vector128", "Capabilities::Flags()", 0, 3, ".model"),
    new("avx2", "Loops::FeatureCountdown(uint)", 0, 3, ".model"),
    new("unsignedSize", "Capabilities::Platform()", 0, 3, ".model"),
    new("processWidth", "Capabilities::Platform()", 0, 6, ".model"),
    new("guard", "Guards::Required(System.String)",
        0, 2, ".model"),
    new("positiveGuard", "ItemPool::.ctor(System.Int32)", 0, 4, ".model"),
    new("negativeGuard", "Guards::Count(System.Int32)", 0, 2, ".model"),
    new("comparisonGuard", "Guards::Index(System.UInt32,System.UInt32)", 0, 3, ".model"),
    new("bitModel", "Bits::Population64(System.UInt64)",
        0, 1, ".model"),
    new("byteOrderModel", "Bits::ReverseI16(System.Int16)",
        0, 1, ".model"),
    new("hardware", "DivisionIntrinsics::And(ulong,ulong)",
        0, 4, ".model", "x64-v3"),
    new("vectorConstruction", "DivisionIntrinsics::And(ulong,ulong)",
        0, 1, ".model", "x64-v3"),
    new("spanConstruction",
        "DivisionIntrinsics::Shuffle128(System.ReadOnlySpan`1<System.Byte>,System.ReadOnlySpan`1<System.Byte>)",
        0, 1, ".model", "x64-v3"),
    new("vectorModel", "DivisionIntrinsics::UnsafeCall(ulong)",
        0, 1, ".model", "x64-v3"),
    new("byteTransfer",
        "DivisionIntrinsics::SwapHalves(System.ReadOnlySpan`1<System.Byte>,System.Span`1<System.Byte>)",
        0, 6, ".model", "arm64-advsimd"),
    new("areSame", "UnsafeReferences::AreSame(System.Byte&,System.Byte&)",
        0, 2, ".model"),
    new("byteOffset", "UnsafeReferences::ByteOffset(System.Byte&,System.Byte&)",
        0, 2, ".model"),
    new("byteAddition", "UnsafeReferences::AddSigned(System.Byte&,System.IntPtr)",
        0, 2, ".model"),
    new("asRefByref", "UnsafeReferences::Mutable(Examples.FourLimbs&)",
        0, 1, ".model"),
    new("asRefPointer", "UnsafeReferences::Pointer(System.Byte*)",
        0, 1, ".model"),
    new("nullRef", "NullReferences::IsNull()",
        0, 0, ".model"),
    new("isNullRef", "NullReferences::IsNull()",
        0, 1, ".model"),
    new("platform", "Capabilities::Platform()",
        0, 0, ".model"),
    new("referenceContent", "Capabilities::ReferenceFree()",
        0, 0, ".model"),
    new("staticSpan", "SpanTables::First()",
        1, 1, ".model"),
    new("initBlockUnaligned", "Blocks::Fill(System.Byte&,System.Byte,System.UInt32)", 0, 3, ".model"),
    new("initBlock", "Blocks::FillPointerAligned(System.Byte*,System.Byte,System.UInt32)", 0, 3, ".model"),
    new("copyBlockUnaligned", "Blocks::CopyPointer(System.Byte*,System.Byte*,System.UInt32)", 0, 3, ".model"),
    new("copyBlock", "Blocks::CopyPointerAligned(System.Byte*,System.Byte*,System.UInt32)", 0, 3, ".model"),
];
string[] extraOwners = [
    "Arm.ArmBase.Arm64", "X86.Sse2", "X86.Ssse3", "X86.Sse41", "X86.Sse42", "X86.Avx",
    "X86.Avx512F", "X86.Avx512F.VL", "X86.Avx512DQ", "X86.Avx512DQ.VL", "X86.Bmi1", "X86.Bmi2.X64", "Vector256"
];
var fixture = Path.Combine(output, "Fixture");
Directory.CreateDirectory(fixture);
File.WriteAllText(Path.Combine(fixture, "Queries.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk">
      <PropertyGroup><TargetFramework>net11.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
    </Project>
    """);
var extraMethods = new List<string>();
var extraSites = new List<CallWitness>();
foreach (var owner in extraOwners)
{
    var method = owner.Replace(".", "", StringComparison.Ordinal);
    var getter = owner == "Vector256" ? "IsHardwareAccelerated" : "IsSupported";
    extraMethods.Add($"public static bool {method}() => System.Runtime.Intrinsics.{owner}.{getter};");
    extraSites.Add(new(method, $"Queries::{method}()", 0, 0, ".model"));
}
foreach (var name in new[] { "ThrowIfZero", "ThrowIfEqual", "ThrowIfNotEqual", "ThrowIfGreaterThan",
    "ThrowIfLessThan", "ThrowIfLessThanOrEqual" })
{
    var unary = name == "ThrowIfZero";
    var parameters = unary ? "int value" : "int value, int bound";
    var arguments = unary ? "value, null" : "value, bound, null";
    var signature = unary ? "int" : "int,int";
    extraMethods.Add($"""
        public static void {name}({parameters}) => System.ArgumentOutOfRangeException.{name}({arguments});
        """);
    extraSites.Add(new(name, $"Queries::{name}({signature})", 0, unary ? 2 : 3, ".model"));
}
File.WriteAllText(Path.Combine(fixture, "Queries.cs"), $$"""
    public static class Queries
    {
        {{string.Join(Environment.NewLine, extraMethods)}}
    }
    """);
Run(["dotnet", "build", Path.Combine(fixture, "Queries.csproj"), "-c", "Release"]);
var evidence = new GeneratedEvidence(output);
Check(assembly, "Examples", witnesses);
Check(Path.Combine(fixture, "bin", "Queries.dll"), "Queries", extraSites);
evidence.Check(replay: false);

void Check(string dll, string identity, IEnumerable<CallWitness> sites)
{
    var methods = sites.GroupBy(site => (site.Entry, site.Profile)).ToArray();
    string Folder(CallWitness site) => Path.Combine(output, site.Name);
    ExtractBatch("extract", identity, methods.Select(group =>
        new GeneratedExtraction(dll, group.Key.Entry, Folder(group.First()), group.Key.Profile)));
    foreach (var group in methods)
    {
        var directory = Folder(group.First());
        var source = new StringBuilder(File.ReadAllText(Path.Combine(directory, "Extracted.lean")));
        foreach (var site in group) source.AppendLine(site.Proof());
        var proof = Path.Combine(directory, "Agreement.lean");
        File.WriteAllText(proof, source.ToString());
        evidence.Add(proof, $"PASS exact call-site agreement for {group.Key.Entry}");
    }
}

sealed record CallWitness(string Name, string Entry, int Method, int Pc, string Claim, string Profile = "scalar")
{
    // Every different instruction, including every instruction with the same stack effect, is refused.
    public string Proof()
    {
        var method = $"method{Method}";
        var change = Name switch
        {
            "typeTest" => "method.owner := .atom runtimeScope \"MyType\"",
            "throwConstructor" => "method.owner := .atom runtimeScope \"System.Object\"",
            "areSame" => "method.owner := .atom \"Fixture\" \"System.Runtime.CompilerServices.Unsafe\"",
            _ when Claim == ".model" => "declared.convention := site.declared.convention + 1",
            _ => "target := .external \"Another overload\""
        };
        var agreement = Claim == ".refused" ? """
                And (foldOwnsSite role = true)
                  (role.bind (fun part => Instruction.ofRole? part none raw) = some expected)) := by
              constructor
              case left => cil_kernel_rfl
              case right => constructor <;> cil_kernel_rfl
            """ : """
                forall emitted, runtimeCatalog.siteAgrees environment profile raw emitted link true =
                  decide (emitted = expected)) := by
              constructor
              case left => cil_kernel_rfl
              case right =>
                intro emitted
                have token : methodTokenCall raw.opcode = true := by cil_kernel_rfl
                have resolved : runtimeCatalog.callRequirement environment.callLayouts profile link raw =
                    .instruction expected := by cil_kernel_rfl
                simp [ModelCatalog.siteAgrees, ModelCatalog.agreesAt, token, resolved,
                  CallRequirement.accepts]
            """;
        return $$"""
            namespace Extracted.{{Name}}
            open CIL CIL.Extraction
            /-- The call operand from the closed metadata body. -/
            private def raw := {{method}}Closed.code[{{Pc}}]'(by decide +kernel)
            /-- The operation emitted at this pc. -/
            private def expected := {{method}}.code[{{Pc}}]'(by decide +kernel)
            /-- The fold role computed from the complete raw body. -/
            private def role := (foldRoles {{method}}Closed.code)[{{Pc}}]?.join
            /-- The managed link at this pc, if present. -/
            private def link := {{method}}.linkAt {{Pc}}
            /-- The resolving member accepts exactly its emitted instruction. -/
            theorem exactEmission :
                And (siteClaim environment link raw = {{Claim}})
                ({{agreement}}
            #print axioms exactEmission
            /-- Changing one part of the resolving operand refuses the live call. -/
            theorem unresolvedOverload :
                let changed := match raw.operand with
                  | .call site => { raw with operand := .call { site with {{change}} } }
                  | _ => raw
                let code := {{method}}Closed.code.set {{Pc}} changed
                let source := { {{method}}Closed with code }
                let decoded := Method.ofRaw? profile environment {{method}}Links {{method}}Reachable source []
                And (runtimeCatalog.callRequirement environment.callLayouts profile link changed =
                  .hole raw.opcode) (decoded = none) := by
              constructor <;> cil_kernel_rfl
            #print axioms unresolvedOverload
            end Extracted.{{Name}}
            """;
    }
}
