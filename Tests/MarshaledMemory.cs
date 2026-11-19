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

using System.Numerics;
using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/MarshaledMemory");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var methods = metadata.GetType("Examples.MarshaledMemory").Methods;
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.MarshaledMemory")!;
RuntimeChecks(runtime);
var queue = new GeneratedQueue(verification, assembly);
foreach (var method in methods.Where(method => method.IsPublic))
{
    var name = method.Name;
    var read = name.Contains("Read", StringComparison.Ordinal);
    var trying = name.StartsWith("Try", StringComparison.Ordinal);
    var aggregate = name.EndsWith("Aggregate", StringComparison.Ordinal);
    var vector = name.EndsWith("Vector", StringComparison.Ordinal);
    var width = aggregate ? 32 : vector ? 16 : 8;
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var claims = new List<string>();
    var proofs = new List<string>();
    var bits = new BigInteger(Enumerable.Repeat((byte)9, width).ToArray(), isUnsigned: true);
    var value = aggregate ? ".aggregate (List.replicate 32 9)" : $".{(vector ? "v128" : "i64")} {bits}";
    string Span(int length) => $".bufferSpan ⟨.address ⟨0, 1⟩, {length}, 1, {(read ? "false" : "true")}⟩";
    string Run(int length, bool nullSource = false) =>
        $"CIL.Safety.invoke Extracted.program 32 0 [{Span(length)}" +
        (read && !trying ? "" : read ? ", .reference (.address ⟨1, 0⟩)" :
            nullSource ? ", .readOnlyReference .null" : ", .readOnlyReference (.address ⟨1, 0⟩)") + "] memory";
    string Observed(string run, int identity, int count) =>
        $"({run}).map (fun result => (result.2, " +
        $"(CIL.Safety.readSnapshot result.1 ⟨{identity}, 0⟩ {count} 1).toOption))";
    void Success(string claim) { claims.Add(claim); proofs.Add("by apply result_of_toOption; decide +kernel"); }
    if (read && !trying) Success($"({Run(width)}).map Prod.snd = .ok [.scalar ({value})]");
    else
    {
        var returned = trying ? "[.scalar (.i32 1)]" : "[]";
        var bytes = read ? $"List.replicate {width} (9, true)" :
            $"[(9, true)] ++ List.replicate {width} (255, true) ++ List.replicate {65 - width} (9, true)";
        Success($"{Observed(Run(width), read ? 1 : 0, read ? width : 66)} = .ok ({returned}, some ({bytes}))");
    }
    if (trying)
    {
        var bytes = read ? $"List.replicate {width} (0, true)" : "List.replicate 66 (9, true)";
        Success($"{Observed(Run(width - 1, nullSource: !read), read ? 1 : 0, read ? width : 66)} = " +
            $".ok ([.scalar (.i32 0)], some ({bytes}))");
    }
    else
    {
        claims.Add($"({Run(width - 1)}).map Prod.snd = " +
            $".error ⟨0, {(read ? 1 : 2)}, .thrown .argumentOutOfRange⟩");
        proofs.Add("by rfl");
    }
    if (name == "Read")
    {
        var run = Run(width).Replace("] memory", "] { memory with cells := fun _ _ => ⟨9, false⟩ }",
            StringComparison.Ordinal);
        claims.Add($"({run}).map Prod.snd = " +
            ".error ⟨0, 1, .memory .uninitialized (.address ⟨0, 1⟩) 8⟩");
        proofs.Add("by rfl");
    }
    if (name == "TryRead")
    {
        var run = Run(width - 1).Replace("] memory",
            "] { memory with views := [⟨0, 0, 66, true, false⟩, ⟨1, 0, 66, true, false⟩] }",
            StringComparison.Ordinal);
        claims.Add($"({run}).map Prod.snd = " +
            ".error ⟨0, 2, .memory .unwritable (.address ⟨1, 0⟩) 8⟩");
        proofs.Add("by rfl");
    }
    if (name == "ReadAggregate")
    {
        var run = Run(width).Replace("] memory", "] { memory with cells := fun _ _ => ⟨9, false⟩ }",
            StringComparison.Ordinal);
        Success($"({run}).map Prod.snd = " +
            ".ok [.scalar (.snapshot (.aggregate 32) (List.replicate 32 (9, false)))]");
    }
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nnamespace ExampleProof\n" + """
        /-- Successful observations identify the successful checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- Disjoint supplied storage for the byte span and an in/out value reference. -/
        def memory : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
          allocations := fun identity => if identity < 2 then
            some ⟨.callerStack, ⟨66, 1, []⟩, true, [66]⟩ else none
          cells := fun identity _ => ⟨if identity == 0 then 9 else 255, true⟩
          views := [⟨0, 0, 66, true, true⟩, ⟨1, 0, 66, true, true⟩]
          nextIdentity := 2 }
        /-- Full and short spans have the exact runtime result and caller-visible write extent. -/
        """ + "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by exact ⟨" +
        string.Join(", ", proofs) + "⟩\n#print axioms correctness\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS checked MemoryMarshal: " + name));
}
queue.Flush();
CheckMarshalModels(root,
[
    ("Read", 1, ".marshalRead (.scalar 8 false) false", ".marshalRead (.scalar 4 false) false"),
    ("TryRead", 2, ".marshalRead (.scalar 8 false) true", ".marshalRead (.scalar 8 false) false"),
    ("TryWrite", 2, ".marshalWrite (.scalar 8 false) true", ".marshalRead (.scalar 8 false) true"),
    ("Write", 2, ".marshalWrite (.scalar 8 false) false", ".marshalWrite (.scalar 8 false) true"),
    ("ReadVector", 1, ".marshalRead (.snapshot .vector128) false", ".marshalRead (.snapshot .vector256) false"),
    ("ReadAggregate", 1, ".marshalRead (.snapshot (.aggregate 32)) false",
        ".marshalRead (.snapshot (.aggregate 16)) false"),
    ("WriteAggregate", 2, ".marshalWrite (.snapshot (.aggregate 32)) false",
        ".marshalWrite (.snapshot (.aggregate 16)) false")
]);

partial class Program
{
    delegate ulong ReadBytes(ReadOnlySpan<byte> source);
    delegate bool TryReadBytes(ReadOnlySpan<byte> source, out ulong value);
    delegate void WriteBytes(Span<byte> destination, in ulong value);
    delegate bool TryWriteBytes(Span<byte> destination, in ulong value);

    static void RuntimeChecks(Type runtime)
    {
        var read = runtime.GetMethod("Read")!.CreateDelegate<ReadBytes>();
        var tryRead = runtime.GetMethod("TryRead")!.CreateDelegate<TryReadBytes>();
        var write = runtime.GetMethod("Write")!.CreateDelegate<WriteBytes>();
        var tryWrite = runtime.GetMethod("TryWrite")!.CreateDelegate<TryWriteBytes>();
        var bytes = Enumerable.Repeat((byte)9, 10).ToArray();
        var value = 0x0909090909090909UL;
        if (read(bytes.AsSpan(1, 8)) != value || !tryRead(bytes.AsSpan(1, 8), out var actual) || actual != value ||
            tryRead(bytes.AsSpan(1, 7), out actual) || actual != 0) throw new Exception("Runtime reads differ");
        value = ulong.MaxValue;
        if (tryWrite(bytes.AsSpan(1, 7), in value) || bytes.Any(item => item != 9))
            throw new Exception("Short TryWrite changed memory");
        write(bytes.AsSpan(1, 8), in value);
        if (bytes[0] != 9 || bytes[^1] != 9 || bytes.AsSpan(1, 8).ContainsAnyExcept((byte)255))
            throw new Exception("Runtime write extent differs");
        if (!tryWrite(bytes.AsSpan(1, 8), in value)) throw new Exception("Full TryWrite rejected");
        try { read(bytes.AsSpan(1, 7)); throw new Exception("Short Read accepted"); }
        catch (ArgumentOutOfRangeException) { }
        try { write(bytes.AsSpan(1, 7), in value); throw new Exception("Short Write accepted"); }
        catch (ArgumentOutOfRangeException) { }
    }
}
