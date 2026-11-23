using System.Text.Json;

partial class Program
{
    /// <summary>Checks one contract against the positive entry and a witness against the wrong entry.</summary>
    void VerifyContractVariant(string assembly, string identity, string selector, string positiveOutput,
        string wrongAssembly, string wrongSelector, string wrongOutput, string contract, string positive,
        string counterexample, string profile = "scalar", string? example = null, string imports = "")
    {
        string Proof(string output, string theorem, string source)
        {
            Directory.CreateDirectory(output);
            var path = Path.Combine(output, "ContractVariant.lean");
            File.WriteAllText(path, $$"""
                import CIL.Safety.MethodContract
                {{imports}}
                {{source}}

                /-! The extracted entry's contract and its verification at this implementation. -/

                open CIL (W32 W64)
                open CIL.Safety
                namespace VariantProof

                {{contract}}

                {{theorem}}
                #print axioms correctness
                end VariantProof

                """);
            return path;
        }

        const string theorem = "VariantProof.correctness";
        var source = example is null ? "import Extracted" : File.ReadAllText(example);
        if (source.StartsWith("import Extracted.", StringComparison.Ordinal))
            source = $"import Extracted{source[source.IndexOf('\n')..]}";
        var original = Verify(assembly, identity, selector, Proof(positiveOutput, positive, source), positiveOutput,
            profile, theorem: theorem, statement: new(Term: true));
        var expected = original.statementIdentity!.term!.Value.GetRawText();
        var wrongProof = Proof(wrongOutput, counterexample, "import Extracted");
        VerifyRefutation(wrongAssembly, identity, wrongSelector, wrongProof, wrongOutput, profile, theorem, expected);
    }

    /// <summary>The counterexample refutes the verified contract and names the entry in this extraction.</summary>
    void VerifyRefutation(string assembly, string identity, string selector, string proof, string output,
        string profile, string theorem, string expected)
    {
        var result = Verify(assembly, identity, selector, proof, output, profile, theorem: theorem,
            statement: new(Term: false, Expected: expected, Refuted: true));
        using var manifest = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "identity.json")));
        var entry = manifest.RootElement.GetProperty("entry").GetString()
            ?? throw new InvalidDataException("The extraction has no entry signature.");
        if (result.refutation is not { } refutation || refutation.method.signature != entry)
            throw new InvalidOperationException($"Expected a verified refutation of {entry}.");
    }
}
