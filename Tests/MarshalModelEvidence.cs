partial class Program
{
    // The compiler keeps the call at its original pc. Check its model and both alternative emissions there.
    static void CheckMarshalModels(string root, (string Name, int Pc, string Model, string Other)[] cases)
    {
        var evidence = new GeneratedEvidence(Path.Combine(root, "ModelEvidence"));
        foreach (var (name, pc, model, other) in cases)
        {
            var directory = Path.Combine(root, name);
            var path = Path.Combine(directory, "ModelEvidence.lean");
            File.Copy(Path.Combine(directory, "Extracted.lean"), path, overwrite: true);
            File.AppendAllText(path, $$"""

                namespace Extracted
                open CIL CIL.Extraction
                /-- The retained call binds its exact operation, closed operand and open signature. -/
                theorem marshalEvidence :
                    (match method0Closed.code[{{pc}}]?, method0.code[{{pc}}]? with
                     | some raw, some (Instruction.call method _) => match raw.operand with
                       | .call site =>
                         let agrees := fun operand op =>
                           runtimeCatalog.siteAgrees environment profile operand op none none true
                         let forged := { site with declared.convention := 0 }
                         let changed := { raw with operand := .call forged }
                         runtimeModel environment .call method == some (.memory ({{model}})) &&
                           runtimeModel environment .call method != some (.memory ({{other}})) &&
                           agrees raw (.call method {}) && !agrees changed (.call method {}) &&
                           !agrees raw (.memory ({{model}})) && !agrees raw (.memory ({{other}}))
                       | _ => false
                     | _, _ => false) = true := by decide +kernel
                #print axioms marshalEvidence
                end Extracted
                """);
            evidence.Add(path, $"PASS exact MemoryMarshal model for {name}", "marshalEvidence");
        }
        evidence.Check(replay: false);
    }
}
