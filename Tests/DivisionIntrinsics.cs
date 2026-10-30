#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using System.Text.Json;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using Mono.Cecil;

using Program verification = new();
string assembly = At("Examples/Assembly/bin/Examples.dll");
using ModuleDefinition metadata = ModuleDefinition.ReadModule(assembly);
Dictionary<string, string> selectors = metadata.GetType("Examples.DivisionIntrinsics").Methods
    .ToDictionary(method => method.Name, method => method.FullName);
Type runtime = Assembly.LoadFile(assembly).GetType("Examples.DivisionIntrinsics")!;
string root = At("artifacts/DivisionIntrinsics");
var pending = new List<(GeneratedVerification Request, string Profile, Action Passed)>();
void Flush()
{
    foreach (var group in pending.GroupBy(item => item.Profile))
    {
        verification.VerifyGeneratedBatch(assembly, "Examples", group.Select(item => item.Request).ToArray(), group.Key);
        foreach (var item in group) item.Passed();
    }
    pending.Clear();
}

foreach (var name in new[] { "DefinedLocal", "PrunedUnsafeLocal" })
{
    var method = metadata.GetType("Examples.DivisionIntrinsics").Methods.Single(method => method.Name == name);
    var local = method.Body.Variables.First(variable => variable.VariableType.FullName ==
        "System.Runtime.Intrinsics.Vector128`1<System.UInt64>").Index;
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, $$"""
import Extracted
import Examples.Support
namespace ExampleProof
theorem byte_homes : Extracted.method0.opaqueVectorLocals = [] := rfl
#print axioms byte_homes
theorem eligible_local : CIL.Extraction.opaqueLocalIndices Extracted.method0Closed = [{{local}}] := by decide +kernel
#print axioms eligible_local
theorem forged_opaque_rejected : ¬ CIL.Extraction.OpaqueLocalsValid Extracted.method0Closed
    { Extracted.method0 with opaqueVectorLocals := [{{local}}] } := by decide +kernel
#print axioms forged_opaque_rejected
theorem correctness :
    (CIL.Safety.invoke Extracted.program 256 0 [.scalar (.i64 7)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 14)] := by rfl
#print axioms correctness
end ExampleProof
""");
    pending.Add((new(selectors[name], proof, output), "x64-sse42",
        () => Console.WriteLine("PASS byte-home compatibility and forged opaque rejection: " + name)));
    if (name == "PrunedUnsafeLocal")
    {
        var reachableOutput = Path.Combine(root, name + "-reachable");
        Directory.CreateDirectory(reachableOutput);
        var reachableProof = Path.Combine(reachableOutput, "Proof.lean");
        File.WriteAllText(reachableProof, $$"""
import Extracted
namespace ExampleProof
theorem eligible_local : CIL.Extraction.opaqueLocalIndices Extracted.method0Closed = [{{local}}] := by decide +kernel
#print axioms eligible_local
theorem correctness : Extracted.method0.opaqueVectorLocals = [{{local}}] := rfl
#print axioms correctness
end ExampleProof
""");
        pending.Add((new(selectors[name], reachableProof, reachableOutput), "x64-v3",
            () => Console.WriteLine("PASS reachable unsafe intrinsic selects the eligible opaque local")));
    }
}

// Check the boundary fault on actual extracted CIL, including an otherwise valid writable destination.
foreach (var name in new[] { "UnsafeReturn", "UnsafeCall", "UnsafeStore" })
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var arguments = name == "UnsafeStore"
        ? "[.reference (.address ⟨0, 0⟩), .scalar (.i64 7)]" : "[.scalar (.i64 7)]";
    File.WriteAllText(proof, $$"""
import Extracted
namespace ExampleProof
private def memory : CIL.Safety.Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1 }
theorem correctness :
    ((CIL.Safety.invoke Extracted.program 64 0 {{arguments}} memory).mapError
      (fun fault => fault.fault)).map Prod.snd =
      .error (.unsupported "Instruction observes unspecified vector bits") := by rfl
#print axioms correctness
end ExampleProof
""");
    pending.Add((new(selectors[name], proof, output), "x64-v3",
        () => Console.WriteLine("PASS unspecified vector boundary rejection: " + name)));
}

foreach ((string name, ulong left, ulong right, ulong expected, bool wide) in new (string, ulong, ulong, ulong, bool)[]
{
    ("And", 13, 6, 4, false), ("Or", 13, 6, 15, false),
    ("Xor", 13, 6, 11, false), ("AndNot", 1, 3, 2, false),
    ("ShiftLeft", 1, 63, 1UL << 63, false), ("ShiftLeft", 1, 64, 0, false),
    ("ShiftLeft", 1, 256, 0, false), ("ShiftRight", ulong.MaxValue, 1, ulong.MaxValue >> 1, false),
    ("ShiftRight", ulong.MaxValue, ulong.MaxValue, 0, false),
    ("Less", 1, 1UL << 63, 255, true), ("Less", 1UL << 63, 1, 0, true),
    ("Greater", 1UL << 63, 1, 255, true), ("Greater", 1, 1, 0, true)
})
{
    string output = Path.Combine(root, name + "-" + right + "-" + left);
    Directory.CreateDirectory(output);
    string proof = Path.Combine(output, "Proof.lean");
    string word = wide ? "i32" : "i64";
    var executionProof = name switch
    {
        "And" => BroadcastProof("band", 0, "and"),
        "Or" => BroadcastProof("bor", 1, "or"),
        "Xor" => BroadcastProof("bxor", 2, "xor"),
        "AndNot" => BroadcastProof("andNot", 3, "andNot"),
        "ShiftLeft" => ShiftProof("shl64Count", 0, "shiftLeft"),
        "ShiftRight" => ShiftProof("shr64Count", 3, "shiftRight"),
        _ => "\n  apply ok_of_toOption\n  decide +kernel"
    };
    string BroadcastProof(string operation, int lane, string lemma) =>
        $"exact congrArg (Except.map Prod.snd) (CIL.Safety.invoke_broadcastBinary_word " +
        $"Extracted.profile .{operation} {lane} {left} {right} {expected} Examples.empty " +
        $"rfl (by decide) (CIL.Safety.checked_broadcast_{lemma} {left} {right}))";
    string ShiftProof(string operation, int lane, string lemma) =>
        $"exact congrArg (Except.map Prod.snd) (CIL.Safety.invoke_broadcastShift " +
        $"Extracted.profile .{operation} {lane} {left} {right} {expected} Examples.empty " +
        $"rfl (by decide) (CIL.Safety.checked_broadcast_{lemma} {left} {right}))";
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\n" +
        "import CIL.Safety.IntrinsicExecution\nnamespace ExampleProof\n" +
        (wide ? "private theorem ok_of_toOption {error value : Type} {result : Except error value} {expected : value}\n" +
            "    (observed : result.toOption = some expected) : result = .ok expected := by\n" +
            "  cases result <;> simp_all [Except.toOption]\n" : "") +
        "theorem correctness : (CIL.Safety.invoke Extracted.program 256 0 [.scalar (.i64 " + left +
        "), .scalar (.i64 " + right + ")] Examples.empty).map Prod.snd = .ok [.scalar (." + word + " " + expected +
        ")] := by " + executionProof + "\n#print axioms correctness\nend ExampleProof\n");
    pending.Add((new(selectors[name], proof, output), wide ? "x64-v4" : "x64-v3", () =>
    {
        RequireRuntimeGroups(output, wide);
        Console.WriteLine("PASS compiled division intrinsic: " + name);
    }));
    if (wide ? Avx512DQ.IsSupported && Avx512F.IsSupported : Avx2.IsSupported)
    {
        object result = runtime.GetMethod(name)!.Invoke(null, [left, right])!;
        ulong actual = wide ? (ulong)(int)result : (ulong)result;
        if (actual != expected) throw new InvalidOperationException("Runtime mismatch: " + name);
    }
}

Flush();

string rejectedEncoding = Path.Combine(root, "Reject-Vector512Encoding");
Directory.CreateDirectory(rejectedEncoding);
string malformedAssembly = Path.Combine(rejectedEncoding, "Examples.dll");
using (ModuleDefinition module = ModuleDefinition.ReadModule(assembly))
{
    MethodDefinition less = module.GetType("Examples.DivisionIntrinsics").Methods.Single(method => method.Name == "Less");
    MethodReference combine = less.Body.Instructions.Select(instruction => instruction.Operand).OfType<MethodReference>()
        .First(method => method.DeclaringType.FullName == "System.Runtime.Intrinsics.Vector512");
    ((GenericInstanceType)combine.ReturnType).IsValueType = false;
    module.Write(malformedAssembly);
}
File.Delete(Path.Combine(rejectedEncoding, "Extracted.lean"));
(int Code, string Output, string Stdout, string Stderr) rejected = Execute(
    Extract("extract", malformedAssembly, "Examples", selectors["Less"], rejectedEncoding, "x64-v4"));
if (rejected.Code == 0 || File.Exists(Path.Combine(rejectedEncoding, "Extracted.lean")) ||
    !rejected.Output.Contains("Unsupported vector type encoding", StringComparison.Ordinal))
    throw new InvalidOperationException("Malformed Vector512 signature was not rejected by the raw metadata check: " + rejected.Output);
Console.WriteLine("PASS malformed Vector512 signature rejection");

foreach ((string name, int width, object initial) in new (string, int, object)[]
{
    ("Init128", 16, Vector128.Create(ulong.MaxValue)),
    ("Init256", 32, Vector256.Create(ulong.MaxValue)),
    ("Init512", 64, Vector512.Create(ulong.MaxValue))
})
{
    string output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    string proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, $$"""
import Extracted
import Examples.Support
namespace ExampleProof
private def memory (size : Nat) : CIL.Safety.Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨size, 1, []⟩, true, [size]⟩ else none
  cells := fun _ _ => ⟨255, true⟩
  views := [⟨0, 0, size, true, true⟩]
  nextIdentity := 1 }
theorem correctness :
    (CIL.Safety.invoke Extracted.program 16 0 [Examples.reference] (memory {{width}})).map
      (fun result => ((List.range {{width}}).map (fun offset => result.1.cells 0 offset), result.2)) =
      .ok (List.replicate {{width}} (⟨0, true⟩ : CIL.Safety.Cell), []) ∧
    (CIL.Safety.invoke Extracted.program 16 0 [Examples.reference] (memory {{width - 1}})).map Prod.snd =
      .error ⟨0, 1, .memory .outsideAllocation (.address ⟨0, 0⟩) {{width}}⟩ := by
  exact ⟨rfl, rfl⟩
end ExampleProof
""");
    pending.Add((new(selectors[name], proof, output), "scalar",
        () => Console.WriteLine("PASS vector initialization, exact zero bytes and bounds: " + name)));
    object[] arguments = [initial];
    runtime.GetMethod(name)!.Invoke(null, arguments);
    bool zero = arguments[0] switch
    {
        Vector128<ulong> vector => vector.Equals(Vector128<ulong>.Zero),
        Vector256<ulong> vector => vector.Equals(Vector256<ulong>.Zero),
        Vector512<ulong> vector => vector.Equals(Vector512<ulong>.Zero),
        _ => false
    };
    if (!zero) throw new InvalidOperationException("Runtime vector initialization did not clear every lane: " + name);
}

Flush();

// The byte shuffles and span constructions are compared with the host CPU on seeded random spans.
if (!Avx2.IsSupported) throw new InvalidOperationException("The byte shuffle differential test needs an AVX2 host");
const int ShuffleCases = 12;
var shuffleRandom = new Random(0x5348);
foreach ((string name, int width, string profile, string unavailable, string feature) in new[]
{
    ("Shuffle256", 32, "x64-v3", "x64-sse42", "Avx2"), ("Shuffle128", 16, "x64-sse42", "x64-sse2", "Ssse3")
})
{
    var cases = new List<(byte[] Source, byte[] Control)>();
    if (width == 32)
        cases.Add((Enumerable.Range(0, 32).Select(index => (byte)index).ToArray(),
            BitConverter.GetBytes(0x18191a1b1c1d1e1ful).Concat(BitConverter.GetBytes(0x1011121314151617ul))
                .Concat(BitConverter.GetBytes(0x08090a0b0c0d0e0ful))
                .Concat(BitConverter.GetBytes(0x0001020304050607ul)).ToArray()));
    while (cases.Count < ShuffleCases)
    {
        byte[] source = new byte[width], control = new byte[width];
        shuffleRandom.NextBytes(source);
        shuffleRandom.NextBytes(control);
        cases.Add((source, control));
    }
    var method = runtime.GetMethod(name)!;
    var observed = cases.Select(item => RuntimeShuffle(method, item.Source, item.Control)).ToArray();
    // The inputs must separate the model from a shuffle that ignores bit 7 or crosses halves.
    foreach ((string mutant, Func<byte[], byte[], byte[]> model) in new (string, Func<byte[], byte[], byte[]>)[]
    {
        ("bit 7 ignored", (source, control) => control.Select((selector, index) =>
            source[(index & ~15) | (selector & 15)]).ToArray()),
        ("lane crossing", (source, control) => control.Select(selector =>
            (selector & 0x80) != 0 ? (byte)0 : source[(selector & 31) % source.Length]).ToArray())
    })
    {
        var agrees = cases.Select((item, index) => model(item.Source, item.Control).SequenceEqual(observed[index]));
        if ((width == 32 || mutant == "bit 7 ignored") && agrees.All(same => same))
            throw new InvalidOperationException($"Shuffle inputs do not reject the {mutant} mutant: {name}");
    }
    foreach ((int sourceLength, int controlLength) in new[] { (width - 1, width), (width, width - 1) })
    {
        try
        {
            RuntimeShuffle(method, new byte[sourceLength], new byte[controlLength]);
            throw new InvalidOperationException($"Runtime accepted a short span: {name}");
        }
        catch (ArgumentOutOfRangeException) { }
    }
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    string Bytes(byte[] bytes) => $"[{string.Join(", ", bytes)}]";
    string Bits(byte[] bytes) => $"0x{Convert.ToHexString(bytes.Reverse().ToArray())}";
    string Claim(int sourceLength, int controlLength, string source, string control, string result) =>
        $"(run {sourceLength} {controlLength} {source} {control}).map Prod.snd =\n      {result}";
    var claims = cases.Select((item, index) => Claim(width, width, Bytes(item.Source), Bytes(item.Control),
        $".ok [.scalar (.v{width * 8} {Bits(observed[index])})]")).ToList();
    var proofs = cases.Select(_ => "by apply result_of_toOption; decide +kernel").ToList();
    foreach ((int sourceLength, int controlLength, int pc) in new[] { (width - 1, width, 1), (width, width - 1, 3) })
    {
        claims.Add(Claim(sourceLength, controlLength, "[]", "[]",
            $".error ⟨0, {pc}, .thrown \"System.ArgumentOutOfRangeException\"⟩"));
        proofs.Add("by rfl");
    }
    File.WriteAllText(proof, $$"""
        import Extracted
        import Examples.Support
        namespace ExampleProof
        /-- Successful observations identify the successful checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- Disjoint read-only storage for the source and control byte spans. -/
        private def memory (source control : List (BitVec 8)) : CIL.Safety.Memory := { Examples.empty with
          allocations := fun identity => if identity < 2 then
            some ⟨.callerStack, ⟨{{width}}, 1, []⟩, true, [{{width}}]⟩ else none
          cells := fun identity offset => ⟨(if identity == 0 then source else control).getD offset 0, true⟩
          views := [⟨0, 0, {{width}}, true, false⟩, ⟨1, 0, {{width}}, true, false⟩]
          nextIdentity := 2 }
        /-- The method on spans of the given lengths over the source and control bytes. -/
        private def run (sourceLength controlLength : Nat) (source control : List (BitVec 8)) :=
          CIL.Safety.invoke Extracted.program 32 0
            [.bufferSpan ⟨.address ⟨0, 0⟩, sourceLength, 1, false⟩,
              .bufferSpan ⟨.address ⟨1, 0⟩, controlLength, 1, false⟩] (memory source control)
        /-- The host CPU's shuffles of seeded random spans, and the short-span exceptions. -/
        theorem correctness :
            {{string.Join(" ∧\n    ", claims)}} := by
          exact ⟨{{string.Join(", ", proofs)}}⟩
        #print axioms correctness
        end ExampleProof
        """);
    pending.Add((new(selectors[name], proof, output), profile,
        () => Console.WriteLine($"PASS byte shuffle matches the host CPU on {cases.Count} spans: {name}")));
    // Without the shuffle's feature the reachable call is rejected before any evidence is written.
    var rejectedOutput = Path.Combine(root, $"{name}-{unavailable}");
    Directory.CreateDirectory(rejectedOutput);
    File.Delete(Path.Combine(rejectedOutput, "Extracted.lean"));
    var rejectedShuffle = Execute(
        Extract("extract", assembly, "Examples", selectors[name], rejectedOutput, unavailable));
    if (rejectedShuffle.Code == 0 || File.Exists(Path.Combine(rejectedOutput, "Extracted.lean")) ||
        !rejectedShuffle.Output.Contains($"Reachable intrinsic lacks {feature}", StringComparison.Ordinal))
        throw new InvalidOperationException($"{name} was admitted without {feature}: {rejectedShuffle.Output}");
    Console.WriteLine($"PASS {name} rejected under {unavailable}");
}

Flush();

// Forged evidence must not substitute another load width or another intrinsic for the shuffle.
var rejectedShuffles = new RejectedEvidence(Path.Combine(root, "RejectedShuffles"));
foreach ((string name, string theorem, string before, string after, string validator) in new[]
{
    ("Shuffle256", "method0_unsafe_validated", ".snapshot .vector256", ".snapshot .vector128", "UnsafeCallsValid"),
    ("Shuffle256", "method0_division_validated", ".avx2 .shuffleBytes", ".avx2 .add64", "DivisionIntrinsicsValid"),
    ("Shuffle128", "method0_division_validated", ".sse .shuffleBytes", ".sse .shiftLeftBytes",
        "DivisionIntrinsicsValid")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")), theorem);
    if (!source.Contains(before, StringComparison.Ordinal))
        throw new InvalidOperationException($"Missing shuffle mutation: {before}");
    var path = Path.Combine(root, "RejectedShuffles", $"{name}-{validator}.lean");
    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejectedShuffles.Add(path, $"PASS forged {name} evidence rejected by {validator}", validator);
}
rejectedShuffles.Check();

// Runs the compiled example on the host CPU and returns the vector's bytes, lane zero first.
static byte[] RuntimeShuffle(MethodInfo method, byte[] source, byte[] control)
{
    var bytes = new byte[method.ReturnType == typeof(Vector256<byte>) ? 32 : 16];
    if (bytes.Length == 32) method.CreateDelegate<WideShuffle>()(source, control).CopyTo(bytes);
    else method.CreateDelegate<NarrowShuffle>()(source, control).CopyTo(bytes);
    return bytes;
}

// .NET 10 reports AVX2 only with BMI1/BMI2 and AVX-512 F/DQ/VL only together; any other profile certifies no runtime.
static void RequireRuntimeGroups(string output, bool wide)
{
    using JsonDocument identity = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "identity.json")));
    JsonElement profile = identity.RootElement.GetProperty("profile");
    bool Flag(string name) => profile.GetProperty(name).GetBoolean();
    bool v3 = Flag("Avx2") && Flag("Bmi1") && Flag("Bmi2");
    bool v4 = Flag("Avx512F") && Flag("Avx512FVL") && Flag("Avx512DQ") && Flag("Avx512DQVL");
    if (!v3 || v4 != wide)
        throw new InvalidOperationException("Division profile matches no .NET 10 x64 ISA level: " + profile);
}

partial class Program
{
    delegate Vector256<byte> WideShuffle(ReadOnlySpan<byte> source, ReadOnlySpan<byte> control);
    delegate Vector128<byte> NarrowShuffle(ReadOnlySpan<byte> source, ReadOnlySpan<byte> control);
}
