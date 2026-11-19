using Mono.Cecil;

// Each witness starts from the caller's real MemberRef and changes one field per refusal.
internal static class ModelOperandChecks
{
    internal static void Append(string proof, MethodDefinition method, Func<MethodReference, string?> expectedModel)
    {
        File.AppendAllText(proof, """

            namespace Extracted
            open CIL
            /-- The raw operands of the example, indexed by instruction position. -/
            private def fixtureOperandCode : Array Extraction.RawInstruction := method0Closed.code.toArray
            end Extracted

            """);
        bool witnessed = false;
        foreach (var (pc, instruction) in method.Body.Instructions.Index())
        {
            if (instruction.Operand is not MethodReference reference || expectedModel(reference) is not { } model)
                continue;
            witnessed = true;
            File.AppendAllText(proof, $$"""

                namespace Extracted.Site{{pc}}
                open CIL CIL.Extraction
                /-- The decoder keeps this live call and rejects each altered operand at the same opcode. -/
                theorem operand_checked :
                    (match (fixtureOperandCode[{{pc}}]? : Option RawInstruction) with
                    | some { operand := .call site, .. } =>
                      let decode := fun (operand : CallSite) =>
                        let raw := RawInstruction.mk 0 40 (.call operand)
                        let source := { method0Closed with code := [raw] }
                        (Method.ofRaw? profile environment [] [true] source []).map Method.code
                      let foreign := match site.method.owner with
                        | .atom _ name => TypeExpr.atom "Foreign" name
                        | .apply (.constructor _ name) element =>
                          .apply (.constructor "Foreign" name) element
                        | owner => owner
                      let floating := TypeExpr.atom runtimeScope "System.Double"
                      let floatingSite : Option CallSite := do
                        let result <- substituteType [floating] site.declared.returnType
                        let parameters <- site.declared.parameters.mapM (substituteType [floating])
                        return { site with
                          method.returnType := result, method.parameters := parameters,
                          method.methodArguments := [floating], typeArguments := [floating] }
                      let refused := fun changed => decide (decode changed = none)
                      let bad : List CallSite := [
                        { site with method.owner := foreign },
                        { site with name := "Unknown" },
                        { site with method.genericArity := site.method.genericArity + 1 },
                        { site with method.parameters := site.parameterTypes.set 0 (.pointer .void) },
                        { site with method.returnType := .pointer .void },
                        { site with declared.convention := 32 },
                        { site with typeArguments := [.atom runtimeScope "System.Double"] },
                        { site with target := .external "Other overload" }]
                      decide (decode site = some [.call site.method {}]) &&
                        bad.all refused && (site.method.genericArity == 0 || floatingSite.any refused)
                    | _ => false) = true := by cil_kernel_rfl
                #print axioms operand_checked
                /-- The generated model fact names the expected checked operation and all its operands. -/
                theorem checked_model :
                    (match (fixtureOperandCode[{{pc}}]? : Option RawInstruction) with
                    | some { operand := .call site, .. } => runtimeModel environment .call site.method
                    | _ => none) = some ({{model}}) := by
                  -- The elaborator would index the literal code list to its end, so the kernel compares the sides.
                  have _fact : runtimeModel environment .call _ = some ({{model}}) := method0_model{{pc}}
                  cil_kernel_rfl
                #print axioms checked_model
                end Extracted.Site{{pc}}

                """);
        }
        if (!witnessed) throw new InvalidDataException($"No model operands in {method.FullName}");
    }
}
