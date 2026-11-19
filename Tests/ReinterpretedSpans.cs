#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include MarshalModelEvidence.cs

using System.Reflection;
using System.Runtime.InteropServices;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ReinterpretedSpans");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var methods = metadata.GetType("Examples.ReinterpretedSpans").Methods;
RuntimeChecks(Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.ReinterpretedSpans")!);
var queue = new GeneratedQueue(verification, assembly);
foreach (var method in methods.Where(method => method.IsPublic))
{
    var name = method.Name;
    var (sourceWidth, targetWidth) = name switch
    {
        "Bytes" => (4, 1), "ReadOnlyBytes" or "Expanded" => (8, 1),
        "Words" => (1, 4), "ReadOnlyWords" => (1, 2), "SameWidth" => (4, 4),
        "Aliased" => (4, 1), _ => (1, 1)
    };
    var writable = (!name.StartsWith("ReadOnly", StringComparison.Ordinal)).ToString().ToLowerInvariant();
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var claims = new List<string>();
    string View(int length, int width, bool empty = false) =>
        $".bufferSpan ⟨{(empty ? ".null" : ".address ⟨0, 1⟩")}, {length}, {width}, {writable}⟩";
    string Run(int length, bool empty = false) =>
        $"CIL.Safety.invoke Extracted.program 32 0 [{View(length, sourceWidth, empty)}] memory";
    if (name == "Aliased")
        claims.Add($"({Run(2)}).map Prod.snd = .ok [.scalar (.i32 255)]");
    else
    {
        foreach (var length in new[] { 0, 1, 7 })
            claims.Add($"({Run(length, length == 0)}).map Prod.snd = " +
                $".ok [{View(length * sourceWidth / targetWidth, targetWidth, length == 0)}]");
        if (sourceWidth > targetWidth)
            claims.Add($"({Run(int.MaxValue)}).map Prod.snd = .error ⟨0, 1, .thrown .overflow⟩");
        var uninitialized = Run(7).Replace("] memory", "] { memory with cells := fun _ _ => ⟨0, false⟩ }",
            StringComparison.Ordinal);
        claims.Add($"({uninitialized}).map Prod.snd = .ok [{View(7 * sourceWidth / targetWidth, targetWidth)}]");
        var noAuthority = Run(7).Replace("] memory", "] { memory with views := [] }", StringComparison.Ordinal);
        claims.Add($"({noAuthority}).map Prod.snd = .ok [{View(7 * sourceWidth / targetWidth, targetWidth)}]");
    }
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nnamespace ExampleProof\n" + """
        /-- Sparse caller storage permits boundary lengths without allocating their byte contents. -/
        def memory : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨2^35, 1, []⟩, true, [2^35]⟩ else none
          cells := fun _ _ => ⟨0, true⟩
          views := [⟨0, 0, 2^35, true, true⟩]
          nextIdentity := 1 }
        /-- Empty, truncated, overflow and unreadable views retain their exact runtime behavior. -/
        """ + "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := " + (claims.Count == 1 ? "by rfl" :
            $"by exact ⟨{string.Join(", ", claims.Select(_ => "by rfl"))}⟩") +
        "\n#print axioms correctness\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS reinterpreted span: " + name));
}
queue.Flush();
CheckMarshalModels(root,
[
    ("Bytes", 1, ".spanReinterpret 4 1 true", ".spanReinterpret 8 1 true"),
    ("Words", 1, ".spanReinterpret 1 4 true", ".spanReinterpret 1 8 true"),
    ("ReadOnlyWords", 1, ".spanReinterpret 1 2 false", ".spanReinterpret 1 2 true"),
    ("SameWidth", 1, ".spanReinterpret 4 4 true", ".spanReadOnly")
]);

partial class Program
{
    delegate Span<byte> Bytes(Span<uint> source);
    delegate Span<uint> Words(Span<byte> source);
    delegate ReadOnlySpan<ushort> ReadOnlyWords(ReadOnlySpan<byte> source);
    delegate uint Aliased(Span<uint> source);

    static void RuntimeChecks(Type runtime)
    {
        var bytes = runtime.GetMethod("Bytes")!.CreateDelegate<Bytes>();
        var words = runtime.GetMethod("Words")!.CreateDelegate<Words>();
        var readOnlyWords = runtime.GetMethod("ReadOnlyWords")!.CreateDelegate<ReadOnlyWords>();
        var aliased = runtime.GetMethod("Aliased")!.CreateDelegate<Aliased>();
        uint[] source = [0, 0];
        if (bytes(source).Length != 8 || bytes(Span<uint>.Empty).Length != 0 || aliased(source) != 255 ||
            source[0] != 255 || source[1] != 0) throw new Exception("Aliased byte view differs");
        var storage = new byte[8];
        if (words(storage.AsSpan(1, 7)).Length != 1 || readOnlyWords(storage.AsSpan(1, 7)).Length != 3 ||
            words(Span<byte>.Empty).Length != 0) throw new Exception("Truncated or unaligned view differs");
        try
        {
            bytes(MemoryMarshal.CreateSpan(ref source[0], int.MaxValue));
            throw new Exception("Overflowing byte view accepted");
        }
        catch (OverflowException) { }
    }
}

