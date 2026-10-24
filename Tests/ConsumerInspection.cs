#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/LibraryAudit.cs

using System.Text.Json;

using var verification = new Program();
Run(["lake", "build", "leancil-audit"]);
verification.auditExecutable = At(".lake/build/bin/leancil-audit" + (OperatingSystem.IsWindows() ? ".exe" : ""));
verification.auditExecutableSha = Sha(verification.auditExecutable);
var root = Path.Combine(Path.GetTempPath(), "leancil-inspection-test-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
try
{
    var marker = Path.Combine(root, "initializer-ran");
    var source = Path.Combine(root, "Inspection.lean");
    var compiled = Path.Combine(root, "Inspection.olean");
    var modules = new Dictionary<string, string> { ["Inspection"] = compiled };
    void Compile(int value)
    {
        File.WriteAllText(source, "import Lean\ninitialize IO.FS.writeFile " +
            JsonSerializer.Serialize(marker) + " \"executed\"\n" +
            $"def inspectedValue : Nat := {value}\n" +
            $"theorem inspectedValue_eq : inspectedValue = {value} := rfl\n#print axioms inspectedValue_eq\n");
        Run(["lean", "--root=" + root, "-o", compiled, source]);
        File.Delete(marker);
    }
    Compile(1);
    var imports = verification.ConsumerModuleImports(root, modules);
    if (!imports["Inspection"].Contains("Lean")) throw new InvalidOperationException("Missing Lean import.");
    var first = verification.PortableConsumerModuleParts(root, modules)["Inspection"];
    var again = verification.PortableConsumerModuleParts(root, modules)["Inspection"];
    if (!Same(first, again) || first.Count == 0)
        throw new InvalidOperationException("Portable fingerprints are not stable.");
    verification.AuditOleans(root, ["Inspection"], [ProofTheorem("inspectedValue_eq")]);
    if (File.Exists(marker)) throw new InvalidOperationException("Inspection executed a module initializer.");

    Compile(2);
    if (Same(first, verification.PortableConsumerModuleParts(root, modules)["Inspection"]))
        throw new InvalidOperationException("Portable fingerprint omitted a changed declaration.");
    if (File.Exists(marker)) throw new InvalidOperationException("Fingerprinting executed a module initializer.");

    var trustedHash = verification.auditExecutableSha;
    verification.auditExecutableSha = "incorrect";
    foreach (Action inspect in new Action[]
    {
        () => verification.ConsumerModuleImports(root, modules),
        () => verification.PortableConsumerModuleParts(root, modules)
    })
    {
        try { inspect(); throw new Exception("Changed inspection executable was accepted."); }
        catch (InvalidOperationException error) when (error.Message.Contains("executable is missing or changed")) { }
    }
    verification.auditExecutableSha = trustedHash;
    File.WriteAllText(compiled, "corrupt olean");
    try
    {
        verification.ConsumerModuleImports(root, modules);
        throw new Exception("Corrupt module header was accepted.");
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Command failed")) { }
    Console.WriteLine("PASS native consumer imports, fingerprints, initializer isolation and executable binding");
}
finally { Directory.Delete(root, recursive: true); }
