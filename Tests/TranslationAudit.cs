#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;

var output = At("artifacts/TranslationAudit");
Directory.CreateDirectory(output);
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution"]);
Run(Extract("extract", At("Examples/Assembly/bin/Examples.dll"), "Examples", "Arithmetic::Add(ulong,ulong)", output));
var baseline = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
var declaration = new Regex(@"theorem translation_valid\s*:[\s\S]*?(?=@\[cil_code\] theorem lookup0)");
if (declaration.Matches(baseline).Count != 1)
    throw new InvalidOperationException("Expected exactly one complete extraction certificate");

void Audit(string name, string source, bool accepted)
{
    var folder = Path.Combine(output, name);
    Directory.CreateDirectory(folder);
    File.WriteAllText(Path.Combine(folder, "Extracted.lean"), source);
    File.WriteAllText(Path.Combine(folder, "ExtractionAudit.lean"), ExtractionAuditSource);
    var leanPath = folder + Path.PathSeparator + At(".lake/build/lib/lean");
    Run(["lean", "--root=" + folder, "-o", Path.Combine(folder, "Extracted.olean"), Path.Combine(folder, "Extracted.lean")], leanPath: leanPath);
    var result = Execute(["lean", "--root=" + folder, "-o", Path.Combine(folder, "ExtractionAudit.olean"), Path.Combine(folder, "ExtractionAudit.lean")], leanPath: leanPath);
    if ((result.Code == 0) != accepted)
        throw new InvalidOperationException("Unexpected certificate audit result " + name + ": " + result.Output);
    if (accepted)
    {
        AuditedAxioms(result.Output, "ExtractionAudit.valid");
        var checker = Path.Combine(Run(["lean", "--print-prefix"]).Trim(), "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
        Run([checker, "Extracted", "ExtractionAudit"], leanPath: leanPath);
    }
    Console.WriteLine("PASS mandatory extraction audit " + name);
}

Audit("valid", baseline, true);
Audit("missing-certificate", declaration.Replace(baseline, ""), false);
Audit("unrelated-true", declaration.Replace(baseline, "theorem translation_valid : True := True.intro"), false);
Audit("definition-instead-of-theorem", baseline.Replace("theorem translation_valid", "def translation_valid"), false);
