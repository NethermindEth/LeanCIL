#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/LibraryAudit.cs

using System.Text.Json;

using var verification = new Program();
verification.Library(Inputs(At("CIL.lean")));
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

    var interfaceSource = Path.Combine(root, "InterfaceAudit.lean");
    void CompileInterface(string declarations)
    {
        File.WriteAllText(interfaceSource, declarations);
        Run(["lean", "--root=" + root, "-o", Path.ChangeExtension(interfaceSource, ".olean"), interfaceSource]);
    }
    CompileInterface("def interfaceValue : Nat := 1\n");
    var cleanInterface = verification.AuditOleans(root, ["InterfaceAudit"], [], interfaces: ["InterfaceAudit"]);
    if (cleanInterface.interfaces?.error is not null)
        throw new InvalidOperationException("A selected clean interface was rejected.");
    CompileInterface(
        "axiom interfaceAxiom : False\ntheorem interfaceTheorem : False := interfaceAxiom\n" +
        "#print axioms interfaceTheorem\n");
    var noInterfaces = verification.AuditOleans(root, ["InterfaceAudit"], []);
    if (noInterfaces.interfaces?.error is not null)
        throw new InvalidOperationException("An empty interface selection inspected unrelated declarations.");
    var selectedInterface = verification.AuditOleans(root, ["InterfaceAudit"], [], interfaces: ["InterfaceAudit"]);
    if (selectedInterface.interfaces?.error is not { } interfaceError ||
        !interfaceError.Contains("axiom", StringComparison.OrdinalIgnoreCase))
        throw new InvalidOperationException("A selected interface accepted an unapproved axiom.");
    var selectedTheorem = verification.AuditOleans(root, ["InterfaceAudit"], [ProofTheorem("interfaceTheorem")]);
    if (selectedTheorem.theorems[0].error is not { } theoremError ||
        !theoremError.Contains("Unapproved proof axioms", StringComparison.Ordinal))
        throw new InvalidOperationException("An empty interface selection bypassed the requested theorem audit.");
    CompileInterface("unsafe def interfaceUnsafe : Nat := 1\n");
    var unsafeInterface = verification.AuditOleans(root, ["InterfaceAudit"], [], interfaces: ["InterfaceAudit"]);
    if (unsafeInterface.interfaces?.error is not { } unsafeError ||
        !unsafeError.Contains("Unsafe or partial declaration", StringComparison.Ordinal))
        throw new InvalidOperationException("A selected interface accepted an unused unsafe definition.");

    Compile(2);
    if (Same(first, verification.PortableConsumerModuleParts(root, modules)["Inspection"]))
        throw new InvalidOperationException("Portable fingerprint omitted a changed declaration.");
    if (File.Exists(marker)) throw new InvalidOperationException("Fingerprinting executed a module initializer.");

    File.WriteAllText(compiled, "corrupt olean");
    try
    {
        verification.ConsumerModuleImports(root, modules);
        throw new Exception("Corrupt module header was accepted.");
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Command failed")) { }
    Console.WriteLine("PASS native consumer imports, fingerprints and initializer isolation");
}
finally { Directory.Delete(root, recursive: true); }
