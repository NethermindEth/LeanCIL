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
        0, 1, ".lowered .binary"),
    new("view", "ViewAccessors::ArrayData(System.Int32[])",
        0, 1, ".lowered .view"),
    new("marshal", "MarshaledMemory::Read(System.ReadOnlySpan`1<System.Byte>)",
        0, 1, ".lowered .marshal"),
    new("unsafeOffset", "UnsafeReferences::AddPointer(System.Byte*,System.Int32)",
        0, 2, ".lowered .unsafeOffset"),
    new("unsafeTransfer", "UnalignedMemory::ReadWord(System.Byte&)",
        0, 1, ".lowered .unsafeTransfer"),
    new("bitCast", "ValueBitCasts::From128Byte(System.Runtime.Intrinsics.Vector128`1<System.Byte>)",
        0, 1, ".lowered .bitCast"),
    new("sizeOf", "UnsafeLayouts::Size0()",
        0, 0, ".lowered .sizeOf"),
    new("integerMath", "WideProduct::UnsignedBigMul32(System.UInt32,System.UInt32)",
        0, 2, ".lowered .integerMath"),
    new("spanReference", "StaticSpans::First()",
        0, 1, ".lowered .spanReference"),
    new("skipInit", "SkipInitialization::Skip(Examples.FourLimbs&)",
        0, 1, ".lowered (.unsafeHelper .skipInit)"),
    new("span", "MemorySpans::ArrayAsSpan(System.Boolean[])",
        0, 1, ".lowered .span"),
    new("objectModel", "VirtualCalls::DogLegs()",
        4, 1, ".model"),
    new("throwConstructor", "Throws::Inner(System.UInt32)",
        0, 4, ".lowered .throwConstructor"),
    new("typeTest", "TypeTests::Marker(System.Int32)",
        1, 4, ".lowered .typeTest"),
    new("feature", "Capabilities::AesFlags()",
        0, 0, ".lowered .feature"),
    new("guard", "Guards::Required(System.String)",
        0, 2, ".lowered .guard"),
    new("bitModel", "Bits::Population64(System.UInt64)",
        0, 1, ".model"),
    new("byteOrderModel", "Bits::ReverseI16(System.Int16)",
        0, 1, ".model"),
    new("hardware", "DivisionIntrinsics::And(ulong,ulong)",
        0, 4, ".lowered .hardware", "x64-v3"),
    new("vectorCreate", "DivisionIntrinsics::And(ulong,ulong)",
        0, 1, ".lowered .vectorCreate", "x64-v3"),
    new("byteSpanCreate",
        "DivisionIntrinsics::Shuffle128(System.ReadOnlySpan`1<System.Byte>,System.ReadOnlySpan`1<System.Byte>)",
        0, 1, ".lowered .vectorCreate", "x64-v3"),
    new("vectorModel", "DivisionIntrinsics::UnsafeCall(ulong)",
        0, 1, ".model", "x64-v3"),
    new("vectorTransfer",
        "DivisionIntrinsics::SwapHalves(System.ReadOnlySpan`1<System.Byte>,System.Span`1<System.Byte>)",
        0, 6, ".lowered .vectorTransfer", "arm64-advsimd"),
    new("unsafeReference", "UnsafeReferences::AreSame(System.Byte&,System.Byte&)",
        0, 2, ".lowered .unsafeReference"),
    new("nullRef", "NullReferences::IsNull()",
        0, 0, ".lowered (.unsafeHelper .nullRef)"),
    new("isNullRef", "NullReferences::IsNull()",
        0, 1, ".lowered (.unsafeHelper .isNullRef)"),
    new("platform", "Capabilities::Platform()",
        0, 0, ".lowered .platform"),
    new("referenceContent", "Capabilities::ReferenceFree()",
        0, 0, ".lowered .referenceContent"),
    new("staticSpan", "SpanTables::First()",
        1, 1, ".lowered .staticSpan"),
    new("unsafeBlock", "Blocks::Fill(System.Byte&,System.Byte,System.UInt32)",
        0, 3, ".lowered .unsafeBlock"),
];
var methods = witnesses.GroupBy(site => (site.Entry, site.Profile)).ToArray();
string Folder(CallWitness site) => Path.Combine(output, site.Name);
ExtractBatch("extract", "Examples", methods.Select(group =>
    new GeneratedExtraction(assembly, group.Key.Entry, Folder(group.First()), group.Key.Profile)));
var evidence = new GeneratedEvidence(output);
foreach (var group in methods)
{
    var directory = Folder(group.First());
    var source = new StringBuilder(File.ReadAllText(Path.Combine(directory, "Extracted.lean")));
    foreach (var site in group) source.AppendLine(site.Proof());
    var proof = Path.Combine(directory, "Agreement.lean");
    File.WriteAllText(proof, source.ToString());
    evidence.Add(proof, $"PASS exact call-site agreement for {group.Key.Entry}");
}
evidence.Check(replay: false);

sealed record CallWitness(string Name, string Entry, int Method, int Pc, string Claim, string Profile = "scalar")
{
    // Every different instruction, including every instruction with the same stack effect, is refused.
    public string Proof()
    {
        var method = $"method{Method}";
        var change = Claim == ".model" ? "declared.convention := site.declared.convention + 1" :
            "target := .external \"Another overload\"";
        return $$"""
            namespace Extracted.{{Name}}
            open CIL CIL.Extraction
            private def raw := {{method}}Closed.code[{{Pc}}]'(by decide +kernel)
            private def expected := {{method}}.code[{{Pc}}]'(by decide +kernel)
            private def role := (foldRoles {{method}}Closed.locals {{method}}Closed.code)[{{Pc}}]?.join
            private def link := {{method}}.linkAt {{Pc}}
            theorem exactEmission :
                siteClaim loweredCallFamily environment link raw = {{Claim}} ∧
                ∀ emitted, runtimeCatalog.siteAgrees environment profile raw emitted link role true =
                  decide (emitted = expected) := by
              constructor
              · cil_kernel_rfl
              · intro emitted
                have token : methodTokenCall raw.opcode = true := by cil_kernel_rfl
                have resolved : runtimeCatalog.callRequirement environment.callLayouts profile link role raw =
                    .instruction expected := by cil_kernel_rfl
                simp [ModelCatalog.siteAgrees, ModelCatalog.agreesAt, token, resolved,
                  CallRequirement.accepts]
            #print axioms exactEmission
            /-- Changing one part of the resolving operand leaves an opcode-tagged hole. -/
            theorem unresolvedOverload :
                let changed := match raw.operand with
                  | .call site => { raw with operand := .call { site with {{change}} } }
                  | _ => raw
                let code := {{method}}Closed.code.set {{Pc}} changed
                let changedRole := (foldRoles {{method}}Closed.locals code)[{{Pc}}]?.join
                runtimeCatalog.callRequirement environment.callLayouts profile link changedRole changed =
                  .hole raw.opcode := by cil_kernel_rfl
            #print axioms unresolvedOverload
            end Extracted.{{Name}}
            """;
    }
}
