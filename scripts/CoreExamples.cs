partial class Program
{
    // These repository fixtures use relative namespaces and share immutable framework inputs.
    static readonly Dictionary<string, string> CoreExampleSignatures = new()
    {
        ["Add"] = "System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)",
        ["AddModel"] = "System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)",
        ["DecodedAdd"] = "System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)",
        ["Choose"] = "System.UInt64 Examples.Arithmetic::Choose(System.Boolean,System.UInt64,System.UInt64)",
        ["Calls"] = "System.UInt64 Examples.Arithmetic::Calls(System.UInt64)",
        ["CallsSummary"] = "System.UInt64 Examples.Arithmetic::Calls(System.UInt64)",
        ["IdentitySummary"] = "System.UInt64 Examples.GenericMethods::Identity64(System.UInt64)",
        ["RepeatedSummary"] = "System.UInt64 Examples.GenericMethods::Repeated(System.UInt64)",
        ["Alias"] = "System.UInt64 Examples.Arithmetic::Alias(System.UInt64&,System.UInt64&)",
        ["Struct"] = "System.UInt64 Examples.Arithmetic::Struct(System.UInt64)",
        ["StructCopy"] = "System.UInt64 Examples.Arithmetic::StructCopy(System.UInt64)",
        ["LargeStruct"] = "System.UInt64 Examples.Arithmetic::LargeStruct(System.UInt64)",
        ["PastEnd"] = "System.UInt64 Examples.Arithmetic::PastEnd(System.UInt64&)",
        ["WrongAdd"] = "System.UInt64 Examples.Arithmetic::WrongAdd(System.UInt64,System.UInt64)",
        ["Escape"] = "System.UInt64& Examples.Arithmetic::Escape()"
    };

    // The theorem of each core example that does not prove ExampleProof.correctness.
    static readonly Dictionary<string, string> CoreExampleTheorems = new()
    {
        ["DecodedAdd"] = "ExampleProof.correctness_decoded"
    };

    // Each output retains its own checked extraction, proof identity and certificate.
    void VerifyCoreExamples(string outputRoot, Action<string> passed, bool separate = false)
    {
        var assembly = At("Examples/Assembly/bin/Examples.dll");
        var requests = CoreExampleSignatures.Select(pair => new GeneratedVerification(
            pair.Key == "Add" ? "Arithmetic::Add(ulong,ulong)" : pair.Value,
            At($"Examples/Proofs/{pair.Key}.lean"), Path.Combine(outputRoot, pair.Key),
            CoreExampleTheorems.GetValueOrDefault(pair.Key, "ExampleProof.correctness"))).ToArray();
        if (separate)
            foreach (var request in requests)
                Verify(assembly, "Examples", request.Entry, request.Proof, request.Output, theorem: request.Theorem);
        else VerifyGeneratedBatch(assembly, "Examples", requests);
        foreach (var request in requests)
        {
            var name = Path.GetFileName(request.Output);
            Verify(assembly, "Examples", CoreExampleSignatures[name], request.Proof, request.Output,
                theorem: request.Theorem, check: true);
            passed(name + " kernel proof and artifact identity");
        }
        // Add decodes in full, so its extraction defines the method from its decoder and writes no literal for it.
        var add = File.ReadAllText(Path.Combine(outputRoot, "Add", "Extracted.lean"));
        if (!add.Contains("\ncil_decoded_method method0 := ", StringComparison.Ordinal) ||
            add.Contains("\ndef method0 : Method", StringComparison.Ordinal))
            throw new InvalidOperationException("The extraction of Add writes a method literal.");
        passed("Add defined from its decoder with no method literal");
    }
}
