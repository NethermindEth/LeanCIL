using System.Text.Json;

partial class Program
{
    sealed record ContractCounterexample(string Assembly, string Selector, string Output, string Proof);

    /// <summary>Checks one contract against the positive entry and a witness against the wrong entry.</summary>
    void VerifyContractVariant(string assembly, string identity, string selector, string positiveOutput,
        string wrongAssembly, string wrongSelector, string wrongOutput, string contract, string positive,
        string counterexample, string profile = "scalar", string? example = null, string imports = "") =>
        VerifyContractVariants(assembly, identity, selector, positiveOutput, contract, positive,
            [new(wrongAssembly, wrongSelector, wrongOutput, counterexample)], profile, example, imports);

    /// <summary>Every witness is checked against the same kernel-audited positive statement.</summary>
    void VerifyContractVariants(string assembly, string identity, string selector, string positiveOutput,
        string contract, string positive, ContractCounterexample[] counterexamples, string profile = "scalar",
        string? example = null, string imports = "")
    {
        var source = example is null ? "import Extracted" : File.ReadAllText(example);
        if (source.StartsWith("import Extracted.", StringComparison.Ordinal))
            source = $"import Extracted{source[source.IndexOf('\n')..]}";
        var original = Verify(assembly, identity, selector,
            VariantProof(positiveOutput, imports, source, contract, positive), positiveOutput, profile,
            theorem: VariantTheorem, statement: new(Term: true));
        var expected = original.statementIdentity!.term!.Value.GetRawText();
        foreach (var variant in counterexamples)
        {
            var proof = VariantProof(variant.Output, imports, "import Extracted", contract, variant.Proof);
            VerifyRefutation(variant.Assembly, identity, variant.Selector, proof, variant.Output, profile,
                VariantTheorem, expected);
        }
    }

    /// <summary>The theorem each generated variant proof states.</summary>
    const string VariantTheorem = "VariantProof.correctness";

    /// <summary>
    /// Writes a proof of `theorem`, which names `VariantTheorem`, after `contract` and the imports and source it
    /// needs, and returns its path.
    /// </summary>
    static string VariantProof(string output, string imports, string source, string contract, string theorem)
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

    /// <summary>
    /// Verifies `ExampleProof.holds` of `example`, the `Holds` of its contract `contractName`, and checks that each
    /// counterexample, stated against that definition as the example writes it, refutes that statement.
    /// </summary>
    void VerifyExampleRefutations(string assembly, string identity, string selector, string example,
        string contractName, string positiveOutput, ContractCounterexample[] counterexamples, string imports = "")
    {
        var expected = ExampleStatement(assembly, identity, selector, example, positiveOutput);
        foreach (var variant in counterexamples)
            VerifyExampleRefutation(example, contractName, variant, identity, expected, imports);
    }

    /// <summary>The kernel-audited statement of `ExampleProof.holds` in `example`, which refutations match.</summary>
    string ExampleStatement(string assembly, string identity, string selector, string example, string output) =>
        Verify(assembly, identity, selector, example, output, theorem: "ExampleProof.holds",
            statement: new(Term: true)).statementIdentity!.term!.Value.GetRawText();

    /// <summary>
    /// Checks that `variant`, stated against the definition `contractName` of `example` and the example's imports,
    /// refutes `expected`.
    /// </summary>
    void VerifyExampleRefutation(string example, string contractName, ContractCounterexample variant,
        string identity, string expected, string imports = "")
    {
        var exampleImports = string.Join('\n', File.ReadLines(example).Where(line =>
            line.StartsWith("import ", StringComparison.Ordinal)));
        var proof = VariantProof(variant.Output, imports, exampleImports, ContractDefinition(example, contractName),
            variant.Proof);
        VerifyRefutation(variant.Assembly, identity, variant.Selector, proof, variant.Output, "scalar",
            VariantTheorem, expected);
    }

    /// <summary>
    /// The definition `name` in `proof` with the docstring directly above it, through the line before the next
    /// blank line.
    /// </summary>
    static string ContractDefinition(string proof, string name)
    {
        var lines = File.ReadAllLines(proof);
        var declared = lines.Index().Where(line => line.Item.StartsWith($"def {name} ", StringComparison.Ordinal))
            .Select(line => line.Index).ToArray();
        if (declared.Length != 1)
            throw new InvalidDataException($"{proof} does not define {name} exactly once.");
        var start = declared[0];
        while (start > 0 && lines[start - 1].Length != 0) start--;
        var end = Array.FindIndex(lines, declared[0], line => line.Length == 0);
        return string.Join('\n', lines[start..(end < 0 ? lines.Length : end)]);
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
