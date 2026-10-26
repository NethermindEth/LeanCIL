#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include CheckedExtractionPrefix.cs
#:include RejectedEvidence.cs

using System.Text;
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
try
{
    prefix.RemainingSource(baseline.Replace("namespace Extracted", "namespace Changed", StringComparison.Ordinal));
    throw new InvalidOperationException("Changed prefix was accepted.");
}
catch (InvalidOperationException error) when (error.Message == "Mutation changes the checked extraction prefix.") { }

var cases = new List<(string Name, string Source, bool Accepted, bool Emitted)>();
// Every extraction must elaborate before checking whether its wrapper or exact statement is accepted.
void Audit(string name, string source, bool accepted, bool emitted = true)
{
    cases.Add((name, prefix.RemainingSource(source), accepted, accepted && emitted));
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

string Wrapper(int index) => ExtractionAuditSource.Replace("import Extracted\n", "", StringComparison.Ordinal)
    .Replace("Extracted.translation_valid", $"AuditCase{index}.Extracted.translation_valid", StringComparison.Ordinal)
    .Replace("ExtractionAudit.valid", $"AuditCase{index}.ExtractionAudit.valid", StringComparison.Ordinal);

var batch = new StringBuilder($"import {prefix.Module}\n");
var requests = new List<AuditRequest>();
for (var index = 0; index < cases.Count; index++)
{
    batch.AppendLine($"namespace AuditCase{index}\nopen _root_.Extracted");
    batch.AppendLine(Regex.Replace(cases[index].Source, @"(?m)^import [^\r\n]+\r?\n", ""));
    batch.AppendLine($"end AuditCase{index}");
    requests.Add(ExtractionCertificate($"AuditCase{index}.Extracted.translation_valid"));
    if (cases[index].Accepted) batch.AppendLine(Wrapper(index));
}
var sourcePath = Path.Combine(output, "AuditCases.lean");
File.WriteAllText(sourcePath, batch.ToString());
var checkedSource = Run(["lean", "--root=" + output, "-o", Path.ChangeExtension(sourcePath, ".olean"), sourcePath],
    leanPath: prefix.LeanPath);
if (checkedSource.Contains("sorryAx", StringComparison.Ordinal))
    throw new InvalidOperationException("Untrusted extraction audit fixture");
verification.ReplayCheckedModules([prefix.Module, "AuditCases"], prefix.LeanPath,
    "Kernel replay of extraction audit fixtures");
for (var index = 0; index < cases.Count; index++)
    if (cases[index].Accepted) requests.Add(ExtractionCertificate($"AuditCase{index}.ExtractionAudit.valid"));
var audited = verification.AuditOleans(prefix.LeanPath, ["AuditCases"], requests.ToArray());
for (var index = 0; index < cases.Count; index++)
{
    if ((audited.theorems[index].error is null) != cases[index].Emitted)
        throw new InvalidOperationException("Unexpected emitted certificate audit result " + cases[index].Name +
            ": " + audited.theorems[index].error);
    if (cases[index].Emitted) AuditedAxioms(audited.theorems[index]);
}
foreach (var wrapper in audited.theorems.Skip(cases.Count)) AuditedAxioms(wrapper);

var rejected = new RejectedEvidence(Path.Combine(output, "RejectedWrappers"));
for (var index = 0; index < cases.Count; index++)
{
    if (cases[index].Accepted)
    {
        Console.WriteLine("PASS mandatory extraction audit " + cases[index].Name);
        continue;
    }
    var path = Path.Combine(output, cases[index].Name + ".lean");
    File.WriteAllText(path, "import AuditCases\nnamespace Extracted\nend Extracted\n" + Wrapper(index));
    rejected.Add(path, "PASS mandatory extraction audit " + cases[index].Name,
        diagnostic => diagnostic.Contains("Expected extraction certificate theorem", StringComparison.Ordinal) ||
            diagnostic.Contains("Type mismatch", StringComparison.Ordinal));
}
rejected.Check(prefix.LeanPath);
