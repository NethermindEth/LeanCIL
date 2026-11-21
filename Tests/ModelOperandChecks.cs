using Mono.Cecil;

// Each witness starts from the caller's real MemberRef and changes one field per refusal.
internal static class ModelOperandChecks
{
    internal static void Append(string proof, MethodDefinition method, Func<MethodReference, string?> expectedModel,
        bool needsFeature = false)
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
            var availability = needsFeature ? "refusedUnder .scalar site &&" : "";
            File.AppendAllText(proof, $$"""

                namespace Extracted.Site{{pc}}
                open CIL CIL.Extraction
                /-- The decoder keeps this live call and refuses each altered operand as a live hole at pc 0. -/
                theorem operand_checked :
                    (match (fixtureOperandCode[{{pc}}]? : Option RawInstruction) with
                    | some { operand := .call site, .. } =>
                      let source := fun (operand : CallSite) =>
                        { method0Closed with code := [RawInstruction.mk 0 40 (.call operand)] }
                      let decode := fun features operand =>
                        (Method.ofRaw? features environment [] [true] (source operand) []).map Method.code
                      let refusal := fun features operand =>
                        match Method.ofClosed? features environment [] [true] (source operand)
                          method0RawArguments with
                        | .error error => some error
                        | .ok _ => none
                      let refusedUnder := fun features operand =>
                        decide (decode features operand = none) &&
                          decide (refusal features operand = some (.liveHole 0 40)) &&
                          decide (methodCode features environment [] [true] (source operand) = [.unadmitted 40])
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
                      let ownerElement : Option CallSite := do
                        let .apply head (.atom _ original) := site.method.owner | none
                        let .external identity := site.target | none
                        let changed := TypeExpr.apply head floating
                        let close := fun type => if type == site.method.owner then changed else type
                        return { site with
                          method.owner := changed,
                          method.returnType := close site.method.returnType,
                          method.parameters := site.parameterTypes.map close,
                          target := .external (identity.replace original "System.Double") }
                      let refused := refusedUnder profile
                      let bad : List CallSite := [
                        { site with method.owner := foreign },
                        { site with name := "Unknown" }, { site with method.name := name!"Unknown" },
                        { site with method.genericArity := site.method.genericArity + 1 },
                        { site with method.parameters := (.pointer .void) :: site.parameterTypes.drop 1 },
                        { site with method.returnType := .pointer .void },
                        { site with declared.convention := 32 },
                        { site with declared.parameters := .void :: site.declared.parameters },
                        { site with typeArguments := [.atom runtimeScope "System.Double"] },
                        { site with target := .external "Other overload" }]
                      decide (decode profile site = some [.call site.method {}]) && {{availability}}
                        bad.all refused && ownerElement.all refused &&
                        (site.method.genericArity == 0 || floatingSite.any refused)
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
