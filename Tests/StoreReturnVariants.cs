partial class Program
{
    /// <summary>Checks a store and load through the fixture's reference for every word.</summary>
    void VerifyStoreReturn(string assembly, string selector, string example, string wrongAssembly,
        string wrongSelector, string wrongOutput, int width)
    {
        var bytes = width / 8;
        var contract = $$"""
            /-- A store followed by a load returns the word supplied by the caller. -/
            def contract : MethodContract W{{width}} where
              args input := [Tests.reference, .scalar (.i{{width}} input)]
              pre _ memory := memory = Tests.caller
              footprint _ := [(⟨0, 0⟩, {{bytes}})]
              post input _ _ values := values = [.scalar (.i{{width}} input)]
            """;
        var positive = $$"""
            /-- Only the bytes at the supplied reference change. -/
            theorem correctness : contract.Holds Extracted.program 0 := by
              rintro input _ rfl
              refine ⟨8, _, rfl, ?_, _, rfl, ?_⟩
              · exact Confined.write
                  (rfl : write Tests.caller ⟨0, 0⟩ (numberBytes input.toNat {{bytes}}) 1 = .ok _)
                  (by simp [contract, numberBytes])
              · exact Except.ok.inj (ExampleProof.correctness input)
            """;
        const string counterexample = """
            /-- Storing another value changes the value read back at input one. -/
            theorem correctness : contract.Refuted Extracted.program 0 :=
              .of_return (input := 1) (initial := Tests.caller) rfl
                (rfl : invoke Extracted.program 16 0 (contract.args 1) Tests.caller = .ok _)
                (by rintro ⟨-, _, rfl, wrong⟩
                    dsimp only [contract] at wrong
                    revert wrong
                    decide)
            """;
        VerifyContractVariant(assembly, "Examples", selector, Path.Combine(wrongOutput, "Positive"), wrongAssembly,
            wrongSelector, wrongOutput, contract, positive, counterexample, example: example,
            imports: "import Tests.Support");
    }
}
