partial class Program
{
    // Each retained call binds its closed reference, including the width of a generic transfer.
    static void CheckMarshalModels(string root, (string Name, int Pc, string Model, string? UInt16Model)[] cases)
    {
        var evidence = new GeneratedEvidence(Path.Combine(root, "ModelEvidence"));
        foreach (var (name, pc, model, uint16Model) in cases)
        {
            var directory = Path.Combine(root, name);
            var path = Path.Combine(directory, "ModelEvidence.lean");
            File.Copy(Path.Combine(directory, "Extracted.lean"), path, overwrite: true);
            var alternate = uint16Model is null ? "none" : $"some ({uint16Model})";
            File.AppendAllText(path, $$"""

                namespace Extracted
                open CIL CIL.Extraction
                /-- Closing the same declaration with UInt16 selects its own transfer width.
                    The original site refuses a call to that instantiation. -/
                private def changedElement (raw : RawInstruction) (site : CallSite)
                    (expected : MemoryOp) : Bool := Id.run do
                  let arguments := site.typeArguments.set 0 (.atom runtimeScope "System.UInt16")
                  let close := substituteType arguments
                  let some result := close site.declared.returnType | return false
                  let some parameters := site.declared.parameters.mapM close | return false
                  let method := { site.method with
                    methodArguments := arguments, returnType := result, parameters }
                  return runtimeModel environment .call method == some (.memory expected) &&
                    !runtimeCatalog.siteAgrees environment profile raw (.call method {}) none true

                /-- The retained call binds its exact operation, closed operand and open signature. -/
                theorem marshalEvidence :
                    (match method0Closed.code[{{pc}}]?, method0.code[{{pc}}]? with
                     | some raw, some (Instruction.call method _) => match raw.operand with
                       | .call site =>
                         let agrees := fun operand op =>
                           runtimeCatalog.siteAgrees environment profile operand op none true
                         let forged := { site with declared.convention := 0 }
                         let changed := { raw with operand := .call forged }
                         runtimeModel environment .call method == some (.memory ({{model}})) &&
                           agrees raw (.call method {}) && !agrees changed (.call method {}) &&
                           !agrees raw (.memory ({{model}})) &&
                           ({{alternate}} : Option MemoryOp).all (changedElement raw site)
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
