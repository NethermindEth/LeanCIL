partial class Program
{
    const string ProjectedReturn = """
        /-- Projecting the result values of a successful computation retains a final memory witness. -/
        private theorem fromEmpty {outcome : Except LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value)}
            {values : List CIL.Safety.Value} (observed : outcome.map Prod.snd = .ok values) :
            ∃ final, outcome = .ok (final, values) ∧ Confined [] Memory.empty final := by
          cases outcome with
          | error fault => cases observed
          | ok pair =>
            obtain ⟨final, actual⟩ := pair
            cases Except.ok.inj observed
            exact ⟨final, rfl, by constructor <;> simp [Memory.empty]⟩
        #print axioms fromEmpty
        """;

    /// <summary>A universal result from empty memory and one input where a variant returns another value.</summary>
    sealed record EmptyReturn(string Input, string Arguments, string Expected, int Fuel, string FromExample,
        string Witness, string Requires = "True");

    void VerifyEmptyReturn(string assembly, string selector, string example, string wrongAssembly,
        string wrongSelector, string wrongOutput, EmptyReturn spec)
    {
        var contract = $$"""
            /-- The arguments, permitted inputs and result of the universal invocation equation. -/
            def contract : MethodContract ({{spec.Input}}) where
              args input := {{spec.Arguments}}
              pre input memory := memory = Memory.empty ∧ {{spec.Requires}}
              footprint _ := []
              post input _ _ values := values = [{{spec.Expected}}]
            """;
        var positive = $$"""
            {{ProjectedReturn}}
            /-- The example's fixed-fuel equation supplies the return required by the contract. -/
            theorem correctness : contract.Holds Extracted.program 0 := by
              rintro input _ ⟨rfl, permitted⟩
              have answer : (invoke Extracted.program {{spec.Fuel}} 0 (contract.args input)
                  Memory.empty).map Prod.snd = .ok [{{spec.Expected}}] := by
                {{spec.FromExample.ReplaceLineEndings("\n").Replace("\n", "\n    ")}}
              obtain ⟨final, ran, framed⟩ := fromEmpty answer
              exact ⟨{{spec.Fuel}}, (final, [{{spec.Expected}}]), ran, framed, _, rfl, rfl⟩
            """;
        var counterexample = $$"""
            /-- The extracted variant returns a different value at the witness. -/
            theorem correctness : contract.Refuted Extracted.program 0 :=
              .of_return (input := {{spec.Witness}}) (initial := Memory.empty) ⟨rfl, by decide⟩
                (rfl : invoke Extracted.program 64 0 (contract.args {{spec.Witness}}) Memory.empty = .ok _)
                (by rintro ⟨-, _, rfl, wrong⟩
                    dsimp only [contract] at wrong
                    revert wrong
                    decide)
            """;
        VerifyContractVariant(assembly, "Examples", selector, Path.Combine(wrongOutput, "Positive"), wrongAssembly,
            wrongSelector, wrongOutput, contract, positive, counterexample, example: example);
    }
}
