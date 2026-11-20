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
        WriteSubtraction(assembly, changed);
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
    }

    void CheckSavedSummary(string directory, string assembly, string entry, string summarySource,
        params (string Name, string Image, string Entry, string Mismatch)[] variants)
    {
        var published = Path.Combine(directory, "Published");
        Directory.CreateDirectory(published);
        var libraryPath = CheckoutLeanPath();
        var producer = Path.Combine(directory, "Producer");
        Run(Extract("extract", assembly, "Examples", entry, producer));
        var reference = Path.Combine(producer, "Reference.lean");
        var generated = File.ReadAllText(Path.Combine(producer, "Extracted.lean"));
        File.WriteAllText(reference, generated.Replace("Extracted", "Reference", StringComparison.Ordinal));
        var consumerSource = At("Tests/SummaryModules/SummaryConsumer.lean");
        var producerPath = published + Path.PathSeparator + libraryPath;
        Compile(reference, published, producerPath);
        Compile(summarySource, published, producerPath);
        var savedProof = Path.Combine(published, "SavedSummary.olean");
        var savedHash = Sha(savedProof);
        CheckConsumer("SameEntry", assembly, entry);
        foreach (var variant in variants)
            CheckConsumer(variant.Name, variant.Image, variant.Entry, variant.Mismatch);
        if (savedHash != Sha(savedProof))
            throw new InvalidDataException($"The published summary for {entry} changed during reuse.");

        void Compile(string source, string destination, string search)
        {
            var module = Path.GetFileNameWithoutExtension(source);
            var result = Run([LeanExecutable, "--root=" + Path.GetDirectoryName(source), "-o",
                Path.Combine(destination, module + ".olean"), source], leanPath: search);
            if (result.Contains("sorryAx", StringComparison.Ordinal))
                throw new InvalidDataException($"The compiled module {module} depends on sorryAx.");
        }

        void CheckConsumer(string name, string image, string entry, string? mismatch = null)
        {
            var consumer = Path.Combine(directory, name);
            Run(Extract("extract", image, "Examples", entry, consumer, "x64-v3"));
            var search = consumer + Path.PathSeparator + producerPath;
            Compile(Path.Combine(consumer, "Extracted.lean"), consumer, search);
            if (mismatch is null)
            {
                Compile(consumerSource, consumer, search);
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

    // Change only the add byte. The image retains the assembly identity, MVID, MethodDef token and metadata.
    static void WriteSubtraction(string assembly, string output)
    {
        var bytes = File.ReadAllBytes(assembly);
        using var pe = new PEReader(new MemoryStream(bytes));
        var metadata = pe.GetMetadataReader();
        var type = metadata.TypeDefinitions.Select(metadata.GetTypeDefinition).Single(type =>
            metadata.StringComparer.Equals(type.Namespace, "Examples") && metadata.StringComparer.Equals(type.Name, "Arithmetic"));
        var method = type.GetMethods().Select(metadata.GetMethodDefinition).Single(method =>
            metadata.StringComparer.Equals(method.Name, "Add") &&
            pe.GetMethodBody(method.RelativeVirtualAddress).GetILBytes() is [0x02, 0x03, 0x58, 0x2a]);
        int rva = method.RelativeVirtualAddress;
        var section = pe.PEHeaders.SectionHeaders[pe.PEHeaders.GetContainingSectionIndex(rva)];
        int body = section.PointerToRawData + rva - section.VirtualAddress;
        if (bytes[body] != (4 << 2 | 2) || bytes[body + 3] != 0x58)
            throw new InvalidDataException("Expected a tiny method containing ldarg.0, ldarg.1, add, ret.");
        bytes[body + 3] = 0x59;
        File.WriteAllBytes(output, bytes);
    }
}
