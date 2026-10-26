#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include CheckedExtractionPrefix.cs

using System.Text.RegularExpressions;

using var verification = new Program();
verification.Library(Inputs(At("CIL.lean")));
var output = At("artifacts/TranslationAudit");
Directory.CreateDirectory(output);
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution");
Run(Extract("extract", At("Examples/Assembly/bin/Examples.dll"), "Examples", "Arithmetic::Add(ulong,ulong)", output));
var baseline = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
var declaration = new Regex(@"theorem translation_valid\s*:[\s\S]*?(?=@\[cil_code\] theorem lookup0)");
if (declaration.Matches(baseline).Count != 1)
    throw new InvalidOperationException("Expected exactly one complete extraction certificate");
var prefix = new CheckedExtractionPrefix(baseline, "theorem translation_valid :", output);
var checker = Path.Combine(Run(["lean", "--print-prefix"]).Trim(), "bin",
    OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
Run([checker, prefix.Module], leanPath: prefix.LeanPath);
try
{
    prefix.RemainingSource(baseline.Replace("namespace Extracted", "namespace Changed", StringComparison.Ordinal));
    throw new InvalidOperationException("Changed prefix was accepted.");
}
catch (InvalidOperationException error) when (error.Message == "Mutation changes the checked extraction prefix.") { }

// The emitted certificate itself must also state the validator application exactly, as batches audit it directly.
void Audit(string name, string source, bool accepted, bool emitted = true)
{
    var folder = Path.Combine(output, name);
    Directory.CreateDirectory(folder);
    File.WriteAllText(Path.Combine(folder, "Extracted.lean"), prefix.RemainingSource(source));
    File.WriteAllText(Path.Combine(folder, "ExtractionAudit.lean"), ExtractionAuditSource);
    var leanPath = folder + Path.PathSeparator + prefix.LeanPath;
    Run(["lean", "--root=" + folder, "-o", Path.Combine(folder, "Extracted.olean"), Path.Combine(folder, "Extracted.lean")], leanPath: leanPath);
    var result = Execute(["lean", "--root=" + folder, "-o", Path.Combine(folder, "ExtractionAudit.olean"), Path.Combine(folder, "ExtractionAudit.lean")], leanPath: leanPath);
    if ((result.Code == 0) != accepted)
        throw new InvalidOperationException("Unexpected certificate audit result " + name + ": " + result.Output);
    if (accepted)
    {
        Run([checker, "Extracted", "ExtractionAudit"], leanPath: leanPath);
        var audited = verification.AuditOleans(leanPath, ["ExtractionAudit"],
            [ExtractionCertificate("ExtractionAudit.valid"), ExtractionCertificate("Extracted.translation_valid")]);
        AuditedAxioms(audited.theorems[0]);
        if ((audited.theorems[1].error is null) != emitted)
            throw new InvalidOperationException("Unexpected emitted certificate audit result " + name + ": " + audited.theorems[1].error);
    }
    Console.WriteLine("PASS mandatory extraction audit " + name);
}

Audit("valid", baseline, true);
// Definitionally equal, so elaboration accepts it, but not the statement the extractor emits.
Audit("wrapped-statement", baseline.Replace("theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts methodEvidence imports program := by",
    "theorem translation_valid : id (Extraction.TranslationValid rawLayouts computedLayouts methodEvidence imports program) := by"), true, emitted: false);
Audit("missing-certificate", declaration.Replace(baseline, ""), false);
Audit("unrelated-true", declaration.Replace(baseline, "theorem translation_valid : True := True.intro"), false);
Audit("definition-instead-of-theorem", baseline.Replace("theorem translation_valid", "def translation_valid"), false);
// A certificate over another import table does not certify the emitted `Extracted.imports`.
Audit("other-import-table", declaration.Replace(baseline,
    "theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts methodEvidence [{ identity := \"forged\", closureDigest := \"\", parameterCount := 0, hasThis := false, returnsValue := false }] program := " +
    "by decide +kernel\n"), false);
