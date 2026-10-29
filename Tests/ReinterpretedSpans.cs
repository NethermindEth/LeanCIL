#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

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
            claims.Add($"({Run(int.MaxValue)}).map Prod.snd = .error ⟨0, 1, .thrown \"System.OverflowException\"⟩");
        var uninitialized = Run(7).Replace("] memory", "] { memory with cells := fun _ _ => ⟨0, false⟩ }",
            StringComparison.Ordinal);
        claims.Add($"({uninitialized}).map Prod.snd = .ok [{View(7 * sourceWidth / targetWidth, targetWidth)}]");
        var noAuthority = Run(7).Replace("] memory", "] { memory with views := [] }", StringComparison.Ordinal);
        claims.Add($"({noAuthority}).map Prod.snd = .ok [{View(7 * sourceWidth / targetWidth, targetWidth)}]");
    }
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + """
        /-- Sparse caller storage permits boundary lengths without allocating their byte contents. -/
        def memory : CIL.Safety.Memory := { Examples.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨2^35, 1, []⟩, true, [2^35]⟩ else none
          cells := fun _ _ => ⟨0, true⟩
          views := [⟨0, 0, 2^35, true, true⟩]
          nextIdentity := 1 }
        /-- Empty, truncated, overflow and unreadable views retain their exact runtime behavior. -/
        """ + "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := " + (claims.Count == 1 ? "by rfl" :
            "by exact ⟨" + string.Join(", ", claims.Select(_ => "by rfl")) + "⟩") +
        "\n#print axioms correctness\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS reinterpreted span: " + name));
}
queue.Flush();
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
var index = 0;
foreach (var (name, before, after) in new[]
{
    ("Bytes", ".spanReinterpret 4 1 true", ".spanReinterpret 8 1 true"),
    ("Words", ".spanReinterpret 1 4 true", ".spanReinterpret 1 8 true"),
    ("ReadOnlyWords", ".spanReinterpret 1 2 false", ".spanReinterpret 1 2 true"),
    ("SameWidth", ".spanReinterpret 4 4 true", ".spanReadOnly")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")),
        "method0_scalars_validated");
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing reinterpret mutation");
    var path = Path.Combine(root, $"Rejected{index++}.lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS exact reinterpret evidence rejection: " + name, "ScalarFlowValid");
}
rejected.Check();

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



