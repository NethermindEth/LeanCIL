using Nethermind.LeanCIL;

partial class Program
{
    const string ProfileReferenceModule = "LeanCILProfileReference";
    const string ProfileReferenceNamespace = ProfileReferenceModule + ".Extracted";

    // The reference is checked against the same DLL and compiled separately from author syntax extensions.
    static Dictionary<string, string>? ProfileFamilySources(PreparedContractExport export)
    {
        if (export.Request.ReferenceArtifact is not { } artifact) return null;
        var sourcePath = Path.Combine(artifact, "Extracted.lean");
        var identityPath = Path.Combine(artifact, "identity.json");
        var sourceBytes = File.ReadAllBytes(sourcePath);
        var identityBytes = File.ReadAllBytes(identityPath);
        Run(["dotnet", ExtractorPath, "check", artifact]);
        if (Sha(sourcePath) != ContractInterface.Hash(sourceBytes) ||
            Sha(identityPath) != ContractInterface.Hash(identityBytes))
            throw new InvalidDataException("Profile family reference changed during its extraction check.");
        var identity = System.Text.Json.JsonSerializer.Deserialize<System.Text.Json.JsonElement>(identityBytes);
        var current = ExtractionIdentity.Read(export.Request.Artifact).Root;
        foreach (var property in new[] { "assemblySha256", "assemblyIdentity", "entry" })
            if (identity.GetProperty(property).GetString() != current.GetProperty(property).GetString())
                throw new InvalidDataException("Profile family reference artifact differs on " + property);
        if (System.Text.Json.JsonSerializer.Deserialize<FeatureProfile>(identity.GetProperty("profile")) !=
            FeatureProfile.Select(export.Request.ReferenceProfile!))
            throw new InvalidDataException("Profile family reference artifact has the wrong profile.");
        var source = System.Text.Encoding.UTF8.GetString(sourceBytes).Replace("\r\n", "\n");
        if (source.Split("\nnamespace Extracted\n").Length != 2 || source.Split("\nend Extracted\n").Length != 2 ||
            source.Contains("_root_.Extracted", StringComparison.Ordinal))
            throw new InvalidDataException("Unsupported reference extraction namespace form.");
        var bodyStart = source.IndexOf("\nnamespace Extracted\n", StringComparison.Ordinal) + 1;
        return new(StringComparer.Ordinal)
        {
            [ProfileReferenceModule] = source[..bodyStart] + "namespace " + ProfileReferenceModule + "\n" +
                source[bodyStart..] + "\nend " + ProfileReferenceModule + "\n"
        };
    }

    // These exact statements prevent proof-module macros from replacing the transport checks.
    static AuditRequest[] ProfileFamilyAudits(PreparedContractExport export)
    {
        if (export.Request.Program is not { } program) return [];
        var source = AuditConstant(program);
        var target = AuditConstant("Extracted.profile");
        var reference = ProfileExpression(FeatureProfile.Select(export.Request.ReferenceProfile!));
        return
        [
            ExtractionCertificate(ProfileReferenceNamespace + ".translation_valid", ProfileReferenceModule + "."),
            new("LeanCILExportAudit.referenceIdentity", new { app = new object[]
            {
                new { @const = "Eq", levels = new[] { 1 } }, AuditConstant("CIL.Program"), source,
                AuditConstant(ProfileReferenceNamespace + ".program")
            } }, ApprovedAxioms),
            new("LeanCILExportAudit.referenceUniform", new { app = new object[]
            {
                new { @const = "Eq", levels = new[] { 1 } }, AuditConstant("CIL.Program"),
                new { app = new[] { AuditConstant("CIL.reprofile"), source, reference } }, source
            } }, ApprovedAxioms),
            new("LeanCILExportAudit.profileAgreement", new { app = new[]
                { AuditConstant("CIL.Program.ProfileAgreement"), source, reference, target } }, ApprovedAxioms),
            new("LeanCILExportAudit.exactProgram", new { app = new object[]
            {
                new { @const = "Eq", levels = new[] { 1 } }, AuditConstant("CIL.Program"),
                AuditConstant("Extracted.program"),
                new { app = new[] { AuditConstant("CIL.reprofile"), source, target } }
            } }, ApprovedAxioms)
        ];
    }

    // The constructor order is the public CIL.FeatureProfile structure order, also used by FeatureProfile.Lean.
    static object ProfileExpression(FeatureProfile profile) => new
    {
        app = new object[]
        {
            AuditConstant("CIL.FeatureProfile.mk"), AuditConstant("CIL.Architecture." + profile.Architecture),
            new { nat = profile.NativeWidth }
        }.Concat(new[]
        {
            profile.LittleEndian, profile.AdvSimd, profile.Sse2, profile.Ssse3, profile.Sse42,
            profile.Avx, profile.Avx2, profile.Avx512F, profile.Avx512FVL, profile.Bmi1,
            profile.Sse41, profile.Avx512DQ, profile.Avx512DQVL, profile.Bmi2, profile.ArmBase64,
            profile.Vector256Accelerated, profile.X86Base64, profile.Vector128Accelerated
        }.Select(value => AuditConstant(value ? "Bool.true" : "Bool.false"))).ToArray()
    };

    static string ProfileFamilySource(PreparedContractExport export, string statement)
    {
        var program = "_root_." + export.Request.Program;
        var reference = FeatureProfile.Select(export.Request.ReferenceProfile!).Lean;
        return $$"""
import LeanCILProfileReference
theorem LeanCILExportAudit.referenceIdentity :
    {{program}} = LeanCILProfileReference.Extracted.program := by
  first | rfl | fail "Profile family reference differs from its fixed extraction artifact"
#print axioms LeanCILExportAudit.referenceIdentity
-- The diagnostic is advisory; the following theorem independently proves agreement in the kernel.
#eval show IO Unit from do
  let reference : CIL.FeatureProfile := {{reference}}
  for feature in ({{program}}).profileReads do
    if reference.evaluate feature != Extracted.profile.evaluate feature then
      throw (IO.userError ("Profile family disagrees on read flag: " ++ reprStr feature))
theorem LeanCILExportAudit.profileAgreement :
    CIL.Program.ProfileAgreement {{program}} {{reference}} Extracted.profile :=
  CIL.Program.ProfileAgreement.of_flags _ _ _ (by decide +kernel)
#print axioms LeanCILExportAudit.profileAgreement
theorem LeanCILExportAudit.referenceUniform :
    CIL.reprofile {{program}} {{reference}} = {{program}} := by
  first | rfl | fail "Profile family reference program is not uniform in referenceProfile"
#print axioms LeanCILExportAudit.referenceUniform
theorem LeanCILExportAudit.exactProgram :
    Extracted.program = CIL.reprofile {{program}} Extracted.profile := by
  first | rfl | fail "Profile family extraction differs from the reprofiled reference program"
#print axioms LeanCILExportAudit.exactProgram
theorem LeanCILExportAudit.certified : {{statement}} := by
  rw [LeanCILExportAudit.exactProgram]
  exact _root_.{{export.Request.Theorem}} Extracted.profile (by decide +kernel)
""";
    }
}
