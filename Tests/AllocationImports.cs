#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

using System.Text.Json;

using var verification = new Program();
var output = At("artifacts/AllocationImports");
Directory.CreateDirectory(output);
Run(["lake", "build", "CIL", "Tests.AllocationRenaming", "Tests.AllocationExecutionRenaming"]);
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
if (!verification.ReplayModulesJointly(At("."), targets, leanPath, "Kernel replay of allocation refinement"))
    throw new InvalidOperationException("Allocation refinement dependencies failed joint kernel replay");
Console.WriteLine($"PASS root import excludes allocation refinement; explicit imports replay {targets.Length} modules");
