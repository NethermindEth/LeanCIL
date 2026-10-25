#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

using System.Text.Json;

using var verification = new Program();
var output = At("artifacts/AllocationImports");
Directory.CreateDirectory(output);
var build = Run(["lake", "build", "CIL", "leancil-audit",
    "Tests.AllocationRenaming", "Tests.AllocationExecutionRenaming"]);
if (build.Contains("sorryAx", StringComparison.Ordinal))
    throw new InvalidOperationException("Allocation build contains sorryAx");
verification.auditExecutable = At(".lake/build/bin/leancil-audit" +
    (OperatingSystem.IsWindows() ? ".exe" : ""));
verification.auditExecutableSha = Sha(verification.auditExecutable);
var leanPath = At(".lake/build/lib/lean");

HashSet<string> Imports(string name, string[] modules)
{
    var source = string.Join('\n', modules.Select(module => "import " + module)) + "\n" + """
        run_cmd do
          let modules := (← Lean.getEnv).allImportedModuleNames.map Lean.Name.toString
          IO.println ("MODULES " ++ (Lean.toJson modules).compress)
        """;
    var path = Path.Combine(output, name + ".lean");
    File.WriteAllText(path, source);
    var result = Execute([verification.LeanExecutable, path], leanPath: leanPath);
    var line = result.Stdout.Split('\n').SingleOrDefault(line => line.StartsWith("MODULES ", StringComparison.Ordinal));
    if (result.Code != 0 || line is null)
        throw new InvalidOperationException("Import inspection failed: " + result.Output);
    return JsonSerializer.Deserialize<string[]>(line[8..])!.ToHashSet(StringComparer.Ordinal);
}

var baseline = Imports("Root", ["CIL"]);
var selected = Imports("Selected", ["Tests.AllocationRenaming", "Tests.AllocationExecutionRenaming"]);
const string entry = "CIL.Safety.AllocationRefinement";
if (baseline.Contains(entry) || !selected.Contains(entry))
    throw new InvalidOperationException("Allocation refinement must require its explicit import");
var targets = selected.Except(baseline).Order(StringComparer.Ordinal).ToArray();
var parts = targets.ToDictionary(module => module, module =>
    ConsumerModuleParts(Path.Combine(leanPath, module.Replace('.', '/') + ".olean")));
if (!verification.ReplayModulesJointly(At("."), targets, leanPath, "Kernel replay of allocation refinement"))
    throw new InvalidOperationException("Allocation refinement dependencies failed joint kernel replay");
Console.WriteLine($"PASS root import excludes allocation refinement; explicit imports replay {targets.Length} modules");
var audited = verification.AuditOleans(leanPath, targets, [],
    namespaces: new(["CIL", "Tests"], ApprovedAxioms));
if (audited.namespaces is not { error: null, count: > 0, rejected.Length: 0 } namespaces ||
    namespaces.axioms.Except(ApprovedAxioms).Any())
    throw new InvalidOperationException("Allocation theorem axiom audit failed: " +
        JsonSerializer.Serialize(audited.namespaces));
foreach (var module in targets)
{
    var path = Path.Combine(leanPath, module.Replace('.', '/') + ".olean");
    RequireAuditedModule(audited, module, path);
    if (!Same(parts[module], ConsumerModuleParts(path)))
        throw new InvalidOperationException("Allocation module changed during replay or audit: " + module);
}
Console.WriteLine($"PASS explicit imports replay {targets.Length} modules and audit {namespaces.count} theorems");

const string negativeModule = "AllocationAuditNegative";
var negativeSource = Path.Combine(output, negativeModule + ".lean");
File.WriteAllText(negativeSource, """
    namespace Tests.AllocationAuditNegative
    theorem claimed : True := by sorry
    #print axioms claimed
    end Tests.AllocationAuditNegative
    """);
Run([verification.LeanExecutable, "--root=" + output, "-o",
    Path.ChangeExtension(negativeSource, ".olean"), negativeSource], leanPath: leanPath);
if (!verification.ReplayModulesJointly(output, [negativeModule], output, "Replay of axiom negative control"))
    throw new InvalidOperationException("The axiom negative control must pass kernel replay");
var rejected = verification.AuditOleans(output, [negativeModule], [],
    namespaces: new(["Tests.AllocationAuditNegative"], ApprovedAxioms)).namespaces;
if (rejected?.error is null || !rejected.axioms.Contains("sorryAx") ||
    !rejected.rejected.Any(theorem => theorem.name == "Tests.AllocationAuditNegative.claimed"))
    throw new InvalidOperationException("Compiled namespace audit accepted the sorryAx negative control");
Console.WriteLine("PASS compiled namespace audit rejects sorryAx after successful kernel replay");
