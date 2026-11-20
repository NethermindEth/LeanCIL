using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;

partial class Program
{
    void CheckSavedSummaries(string directory, string assembly)
    {
        const string signature = "::Add(System.UInt64,System.UInt64)";
        const string addition = "System.UInt64 Examples.Arithmetic" + signature;
        Directory.CreateDirectory(directory);
        var changed = Path.Combine(directory, "Examples.dll");
        WriteInstructionChange(assembly, changed, "Add", [0x02, 0x03, 0x58, 0x2a], 2, 0x59);
        CheckSavedSummary(Path.Combine(directory, "Addition"), assembly, addition,
            At("Tests/SummaryModules/SavedSummary.lean"),
            ("OtherToken", assembly, "System.UInt64 SelectorExamples.One.Collision" + signature, "token"),
            ("OtherBody", changed, addition, "program"));
        CheckSavedSummary(Path.Combine(directory, "Vector"), assembly,
            "System.UInt64 Examples.DivisionIntrinsics::UnsafeLow(System.UInt64)",
            At("Tests/SummaryModules/Vector/SavedSummary.lean"));
        CheckSavedSummary(Path.Combine(directory, "Memory"), assembly,
            "System.Void Examples.Arithmetic::Mutate(System.UInt64&)",
            At("Tests/SummaryModules/Memory/SavedSummary.lean"));
        CheckSavedBranches(Path.Combine(directory, "Branch"), assembly);
    }

    void CompileSummaryModule(string source, string destination, string search)
    {
        var module = Path.GetFileNameWithoutExtension(source);
        var result = Run([LeanExecutable, "--root=" + Path.GetDirectoryName(source), "-o",
            Path.Combine(destination, module + ".olean"), source], leanPath: search);
        if (result.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidDataException($"The compiled module {module} depends on sorryAx.");
    }

    // Publish only compiled modules. A consumer must discharge the target's own byte and metadata checks.
    string PublishSummary(string directory, string assembly, string entry, string summarySource)
    {
        var published = Path.Combine(directory, "Published");
        Directory.CreateDirectory(published);
        var producer = Path.Combine(directory, "Producer");
        Run(Extract("extract", assembly, "Examples", entry, producer));
        var reference = Path.Combine(producer, "Reference.lean");
        var generated = File.ReadAllText(Path.Combine(producer, "Extracted.lean"));
        File.WriteAllText(reference, generated.Replace("Extracted", "Reference", StringComparison.Ordinal));
        var search = published + Path.PathSeparator + CheckoutLeanPath();
        CompileSummaryModule(reference, published, search);
        CompileSummaryModule(summarySource, published, search);
        return published;
    }

    void CheckSavedBranches(string directory, string assembly)
    {
        const string entry = "System.UInt64 Examples.Arithmetic::Choose(System.Boolean,System.UInt64,System.UInt64)";
        var published = PublishSummary(directory, assembly, entry, At("Tests/SummaryModules/Branch/SavedArms.lean"));
        var changed = Path.Combine(directory, "Examples.dll");
        WriteInstructionChange(assembly, changed, "Choose", [0x02, 0x2d, 0x02, 0x04, 0x2a, 0x03, 0x2a], 1, 0x2c);
        var consumer = Path.Combine(directory, "Reversed");
        Run(Extract("extract", changed, "Examples", entry, consumer));
        var search = string.Join(Path.PathSeparator, consumer, published, CheckoutLeanPath());
        CompileSummaryModule(Path.Combine(consumer, "Extracted.lean"), consumer, search);
        CompileSummaryModule(At("Tests/SummaryModules/Branch/ReversedBranch.lean"), consumer, search);
        ReplayCheckedModules(["Reference", "SavedArms", "Extracted", "ReversedBranch"], search,
            "Kernel replay of both saved return regions and the reversed branch");
        Console.WriteLine("PASS reversing the branch reuses both return regions and refutes the original result");

        VerifyContractVariant(assembly, "Examples", entry, Path.Combine(directory, "OriginalContract"), changed,
            entry, Path.Combine(directory, "WrongContract"), """
            /-- Choose returns the requested argument and preserves every caller memory. -/
            def choose : MethodContract (Bool × W64 × W64) W64 where
              args := fun (flag, x, y) =>
                [.scalar (.i32 (if flag then 1 else 0)), .scalar (.i64 x), .scalar (.i64 y)]
              results word := [.scalar (.i64 word)]
              pre _ _ := True
              footprint _ := []
              post := fun (flag, x, y) initial final result =>
                final = initial ∧ result = (if flag then x else y)
            """, """
            /-- Both input choices satisfy the original compiled entry's contract. -/
            theorem correctness : choose.Holds Extracted.program 0 := by
              rintro ⟨flag, x, y⟩ memory _
              obtain ⟨fuel, ran⟩ := ExampleProof.correctness memory flag x y
              exact MethodContract.Holds.intro memory (if flag then x else y) ⟨fuel, ran⟩
                (Confined.refl [] memory) ⟨rfl, rfl⟩
            """, """
            /-- The changed condition selects 22 on an input requiring 11. -/
            theorem correctness : choose.Refuted Extracted.program 0 := by
              apply MethodContract.Refuted.of_return (input := (true, 11, 22)) (initial := Memory.empty)
                (fuel := 4) (final := Memory.empty) (values := [.scalar (.i64 22)]) trivial rfl
              rintro ⟨_, result, encoded, _, rfl⟩
              exact (by decide : ¬ ([CIL.Safety.Value.scalar (.i64 22)] = [.scalar (.i64 11)])) encoded
            """, example: At("Examples/Proofs/Choose.lean"));
    }

    void CheckSavedSummary(string directory, string assembly, string entry, string summarySource,
        params (string Name, string Image, string Entry, string Mismatch)[] variants)
    {
        var published = PublishSummary(directory, assembly, entry, summarySource);
        var consumerSource = At("Tests/SummaryModules/SummaryConsumer.lean");
        var producerPath = published + Path.PathSeparator + CheckoutLeanPath();
        var savedProof = Path.Combine(published, "SavedSummary.olean");
        var savedHash = Sha(savedProof);
        CheckConsumer("SameEntry", assembly, entry);
        foreach (var variant in variants)
            CheckConsumer(variant.Name, variant.Image, variant.Entry, variant.Mismatch);
        if (savedHash != Sha(savedProof))
            throw new InvalidDataException($"The published summary for {entry} changed during reuse.");

        void CheckConsumer(string name, string image, string entry, string? mismatch = null)
        {
            var consumer = Path.Combine(directory, name);
            Run(Extract("extract", image, "Examples", entry, consumer, "x64-v3"));
            var search = consumer + Path.PathSeparator + producerPath;
            CompileSummaryModule(Path.Combine(consumer, "Extracted.lean"), consumer, search);
            if (mismatch is null)
            {
                CompileSummaryModule(consumerSource, consumer, search);
                ReplayCheckedModules(["Reference", "SavedSummary", "Extracted", "SummaryConsumer"], search,
                    $"Joint kernel replay of the saved summary and x64-v3 consumer of {entry}");
                Console.WriteLine($"PASS the x64-v3 extraction reuses the compiled scalar summary of {entry}");
                return;
            }

            var lines = File.ReadAllLines(consumerSource);
            int Line(string fact) => Array.FindIndex(lines,
                line => line.StartsWith("  have " + fact + " :", StringComparison.Ordinal)) + 1;
            var result = Execute([LeanExecutable, "--root=" + Path.GetDirectoryName(consumerSource), consumerSource],
                leanPath: search);
            var errors = result.Output.Split('\n').Where(line => line.Contains(": error:", StringComparison.Ordinal)).ToArray();
            bool RejectedAt(string fact) => errors.Any(line =>
                line.Contains($"SummaryConsumer.lean:{Line(fact)}:", StringComparison.Ordinal) &&
                line.Contains("cil_kernel_rfl: the kernel does not accept the two sides as equal", StringComparison.Ordinal));
            if (result.Code == 0 || errors.Length != 2 || !RejectedAt(mismatch) || !RejectedAt("record"))
                throw new InvalidDataException($"Unexpected saved summary result for {name}: {result.Output}");
            Console.WriteLine($"PASS {name} rejects the saved summary at its {mismatch} and evidence checks");
        }
    }

    // Replace one opcode in a known tiny method, preserving its token, operands, metadata and image length.
    static void WriteInstructionChange(string assembly, string output, string name, byte[] expected,
        int position, byte opcode)
    {
        var bytes = File.ReadAllBytes(assembly);
        using var pe = new PEReader(new MemoryStream(bytes));
        var metadata = pe.GetMetadataReader();
        var type = metadata.TypeDefinitions.Select(metadata.GetTypeDefinition).Single(type =>
            metadata.StringComparer.Equals(type.Namespace, "Examples") && metadata.StringComparer.Equals(type.Name, "Arithmetic"));
        var method = type.GetMethods().Select(metadata.GetMethodDefinition).Single(method =>
            metadata.StringComparer.Equals(method.Name, name) &&
            pe.GetMethodBody(method.RelativeVirtualAddress).GetILBytes().AsSpan().SequenceEqual(expected));
        int rva = method.RelativeVirtualAddress;
        var section = pe.PEHeaders.SectionHeaders[pe.PEHeaders.GetContainingSectionIndex(rva)];
        int body = section.PointerToRawData + rva - section.VirtualAddress;
        if (bytes[body] != (expected.Length << 2 | 2) || !bytes.AsSpan(body + 1, expected.Length).SequenceEqual(expected))
            throw new InvalidDataException($"Unexpected tiny method body for {name}.");
        bytes[body + 1 + position] = opcode;
        File.WriteAllBytes(output, bytes);
    }
}
