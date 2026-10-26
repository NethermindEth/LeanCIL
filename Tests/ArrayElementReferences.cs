#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs

using System.Reflection;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ArrayElementReferences");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.ArrayElementReferences")!;
RequireLeanFixtures("CIL.Extraction.Translation", "Tests.ArrayElementReferences");
foreach (var name in new[] { "Element", "Read", "Write" })
{
    var values = new[] { 3, 5 };
    var write = name == "Write";
    var runtimeResult = runtime.GetMethod(name)!.Invoke(null, write ? [values, 1, 7] : [values, 1]);
    if (!Equals(runtimeResult, write ? 7 : 5) || values[0] != 3 || values[1] != (write ? 7 : 5))
        throw new Exception("Incorrect runtime array reference behavior: " + name);
    var signature = "System.Int32[],System.Int32" + (write ? ",System.Int32" : "");
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"ArrayElementReferences::{name}({signature})", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    var extra = write ? ", .scalar (.i32 7)" : "";
    var result = name == "Element" ? ".reference (.address ⟨0, 4⟩)" :
        $".scalar (.i32 {(write ? 7 : 5)})";
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.managedHeap, ⟨8, 4, []⟩, true, [8]⟩ else none
          cells := fun _ offset => ⟨if offset == 0 then 3 else if offset == 4 then 5 else 0, true⟩
          views := [⟨0, 0, 8, true, true⟩]
          nextIdentity := 1 }
        theorem checked_element_reference :
            (match CIL.Safety.invoke Extracted.program 128 0
              [.array ⟨.address ⟨0, 0⟩, 2, .signed32⟩, .scalar (.i32 1){{extra}}] inputMemory with
             | .ok outcome => outcome.2 == [{{result}}] &&
                 (outcome.1.cells 0 0).bits == 3 && (outcome.1.cells 0 4).bits == {{(write ? 7 : 5)}}
             | .error _ => false) = true := by decide +kernel
        #print axioms checked_element_reference
        """);
    evidence.Add(proof, "PASS runtime and certified array reference: " + name);
    if (name != "Element") continue;
    const string target = ".arrayAddress .signed32";
    if (!source.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing address mutation target");
    var forged = Path.Combine(root, "ForgedElement.lean");
    File.WriteAllText(forged, source.Replace(target, ".arrayAddress .unsigned32", StringComparison.Ordinal));
    var rejection = Execute(["lake", "env", "lean", forged], cwd: FixturePackage());
    if (rejection.Code == 0 || !rejection.Output.Contains("ScalarFlowValid", StringComparison.Ordinal))
        throw new Exception("Forged element address was not rejected by scalar evidence: " + rejection.Output);
}

evidence.Check(replay: false);
