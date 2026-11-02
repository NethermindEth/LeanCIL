#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Buffers.Binary;
using System.Reflection;
using System.Text.Json;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using Mono.Cecil;
using X86Aes = System.Runtime.Intrinsics.X86.Aes;

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
import Tests.Support
namespace ExampleProof
theorem byte_homes : Extracted.method0.opaqueVectorLocals = [] := rfl
#print axioms byte_homes
theorem eligible_local : CIL.Extraction.opaqueLocalIndices Extracted.method0Closed = [{{local}}] := by decide +kernel
#print axioms eligible_local
theorem forged_opaque_rejected : ¬ CIL.Extraction.OpaqueLocalsValid Extracted.method0Closed
    { Extracted.method0 with opaqueVectorLocals := [{{local}}] } := by decide +kernel
#print axioms forged_opaque_rejected
theorem correctness :
    (CIL.Safety.invoke Extracted.program 256 0 [.scalar (.i64 7)] CIL.Safety.Memory.empty).map Prod.snd =
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
        $"Extracted.profile .{operation} {lane} {left} {right} {expected} CIL.Safety.Memory.empty " +
        $"rfl (by decide) (CIL.Safety.checked_broadcast_{lemma} {left} {right}))";
    string ShiftProof(string operation, int lane, string lemma) =>
        $"exact congrArg (Except.map Prod.snd) (CIL.Safety.invoke_broadcastShift " +
        $"Extracted.profile .{operation} {lane} {left} {right} {expected} CIL.Safety.Memory.empty " +
        $"rfl (by decide) (CIL.Safety.checked_broadcast_{lemma} {left} {right}))";
    File.WriteAllText(proof, "import Extracted\nimport Tests.Support\n" +
        "import CIL.Safety.IntrinsicExecution\nnamespace ExampleProof\n" +
        (wide ? "private theorem ok_of_toOption {error value : Type} {result : Except error value} {expected : value}\n" +
            "    (observed : result.toOption = some expected) : result = .ok expected := by\n" +
            "  cases result <;> simp_all [Except.toOption]\n" : "") +
        "theorem correctness : (CIL.Safety.invoke Extracted.program 256 0 [.scalar (.i64 " + left +
        "), .scalar (.i64 " + right + ")] CIL.Safety.Memory.empty).map Prod.snd = .ok [.scalar (." + word + " " + expected +
        ")] := by " + executionProof + "\n#print axioms correctness\nend ExampleProof\n");
    pending.Add((new(selectors[name], proof, output), wide ? "x64-v4" : "x64-v3", () =>
    {
        RequireRuntimeGroups(output, wide);
        Console.WriteLine("PASS compiled exact intrinsic: " + name);
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
import Tests.Support
namespace ExampleProof
private def memory (size : Nat) : CIL.Safety.Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨size, 1, []⟩, true, [size]⟩ else none
  cells := fun _ _ => ⟨255, true⟩
  views := [⟨0, 0, size, true, true⟩]
  nextIdentity := 1 }
theorem correctness :
    (CIL.Safety.invoke Extracted.program 16 0 [Tests.reference] (memory {{width}})).map
      (fun result => ((List.range {{width}}).map (fun offset => result.1.cells 0 offset), result.2)) =
      .ok (List.replicate {{width}} (⟨0, true⟩ : CIL.Safety.Cell), []) ∧
    (CIL.Safety.invoke Extracted.program 16 0 [Tests.reference] (memory {{width - 1}})).map Prod.snd =
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
        import Tests.Support
        namespace ExampleProof
        /-- Successful observations identify the successful checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- Disjoint read-only storage for the source and control byte spans. -/
        private def memory (source control : List (BitVec 8)) : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
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
    ("Shuffle256", "method0_intrinsics_validated", ".avx2 .shuffleBytes", ".avx2 .add64", "ExactIntrinsicsValid"),
    ("Shuffle128", "method0_intrinsics_validated", ".sse .shuffleBytes", ".sse .shiftLeftBytes",
        "ExactIntrinsicsValid")
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

// The hash round is compared with the host CPU's AESENC under a custom x64 and a custom ARM64 AES
// profile; the ARM64 extraction must agree, since AESE with a zero key, AESMC and the key are AESENC.
if (!X86Aes.IsSupported) throw new InvalidOperationException("The AES differential test needs an x86 AES host");
verification.EnsureExtractorBuilt();
var profileType = Assembly.Load(File.ReadAllBytes(ExtractorPath))
    .GetType("Nethermind.LeanCIL.FeatureProfile", throwOnError: true)!;
var selectProfile = profileType.GetMethod("Select", BindingFlags.Static | BindingFlags.NonPublic)!;
string DeclareAes(string name, string flag)
{
    var profile = JsonSerializer.SerializeToNode(selectProfile.Invoke(null, [name]),
        new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.CamelCase })!;
    profile["name"] = $"{name}-{flag}";
    profile[flag] = true;
    var path = Path.Combine(root, $"{name}-{flag}.json");
    File.WriteAllText(path, profile.ToJsonString());
    return "@" + path;
}
const int AesCases = 8;
var aesRandom = new Random(20261102);
ulong RandomWord()
{
    var bytes = new byte[sizeof(ulong)];
    aesRandom.NextBytes(bytes);
    return BitConverter.ToUInt64(bytes);
}
var aesInputs = Enumerable.Range(0, AesCases)
    .Select(_ => new[] { RandomWord(), RandomWord(), RandomWord(), RandomWord() }).ToArray();
var aesRound = runtime.GetMethod("AesRound")!;
var aesObserved = aesInputs.Select(input =>
{
    var bytes = new byte[16];
    ((Vector128<byte>)aesRound.Invoke(null, input.Cast<object>().ToArray())!).CopyTo(bytes);
    return $"0x{Convert.ToHexString(bytes.Reverse().ToArray())}";
}).ToArray();
foreach (var (label, profile) in new[]
{
    ("AesRound-x64", DeclareAes("x64-v4", "aes")), ("AesRound-arm64", DeclareAes("arm64-advsimd", "armAes"))
})
{
    var output = Path.Combine(root, label);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var claims = aesInputs.Select((input, index) =>
    {
        var arguments = string.Join(", ", input.Select(word => $".scalar (.i64 {word})"));
        return $"(CIL.Safety.invoke Extracted.program 64 0 [{arguments}] CIL.Safety.Memory.empty).map Prod.snd =\n" +
            $"      .ok [.scalar (.v128 {aesObserved[index]})]";
    }).ToList();
    File.WriteAllText(proof, $$"""
        import Extracted
        import CIL.Safety.Execution
        namespace ExampleProof
        /-- Successful observations identify the successful checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- The host CPU's AESENC rounds of seeded random states and keys. -/
        theorem correctness :
            {{string.Join(" ∧\n    ", claims)}} := by
          exact ⟨{{string.Join(", ", claims.Select(_ => "by apply result_of_toOption; decide +kernel"))}}⟩
        #print axioms correctness
        end ExampleProof
        """);
    pending.Add((new(selectors["AesRound"], proof, output), profile,
        () => Console.WriteLine($"PASS hash round matches the host CPU's AESENC on {AesCases} blocks: {label}")));
}
Flush();
// Without AES the x86 getter folds false, so the reachable ARM64 calls are rejected on every built-in.
foreach (var profile in new[] { "x64-v4", "arm64-advsimd" })
{
    var rejectedOutput = Path.Combine(root, $"AesRound-{profile}");
    Directory.CreateDirectory(rejectedOutput);
    File.Delete(Path.Combine(rejectedOutput, "Extracted.lean"));
    var rejectedRound = Execute(
        Extract("extract", assembly, "Examples", selectors["AesRound"], rejectedOutput, profile));
    if (rejectedRound.Code == 0 || File.Exists(Path.Combine(rejectedOutput, "Extracted.lean")) ||
        !rejectedRound.Output.Contains("Reachable intrinsic lacks ArmAes", StringComparison.Ordinal))
        throw new InvalidOperationException($"AesRound admitted without AES under {profile}: {rejectedRound.Output}");
    Console.WriteLine($"PASS AesRound rejected under {profile}");
}
// Forged evidence must not substitute another AES step for the one the raw call names.
var rejectedRounds = new RejectedEvidence(Path.Combine(root, "RejectedAes"));
foreach ((string name, string before, string after) in new[]
{
    ("AesRound-x64", ".aes .encrypt", ".armAes .encrypt"),
    ("AesRound-arm64", ".armAes .mixColumns", ".armAes .encrypt")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")),
        "method0_intrinsics_validated");
    if (!source.Contains(before, StringComparison.Ordinal))
        throw new InvalidOperationException($"Missing AES mutation: {before}");
    var path = Path.Combine(root, "RejectedAes", $"{name}.lean");
    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejectedRounds.Add(path, $"PASS forged {name} evidence rejected by ExactIntrinsicsValid", "ExactIntrinsicsValid");
}
rejectedRounds.Check();
Run(["dotnet", "run", "--file", At("Tests/AesHardware.cs")], cwd: Root);
Console.WriteLine("PASS host AES instructions match the Lean AES model");

// The int256 sign window and eight-lane creation run on the host CPU; their x64-v4 extractions must return the
// same vectors. The windows Int256.Rsh loads come first, then indices with random high bits.
if (!Avx512F.VL.IsSupported)
    throw new InvalidOperationException("The permutation differential test needs an AVX-512 host");
const int WindowCases = 12;
var windowRandom = new Random(0x5257);
ulong WindowWord()
{
    var bytes = new byte[sizeof(ulong)];
    windowRandom.NextBytes(bytes);
    return BitConverter.ToUInt64(bytes);
}
var windowInputs = new List<ulong[]>();
for (var shift = 0UL; shift <= 4; shift++)
    windowInputs.Add([WindowWord(), WindowWord(), WindowWord(), WindowWord() | (1UL << 63),
        shift, shift + 1, shift + 2, shift + 3]);
while (windowInputs.Count < WindowCases)
    windowInputs.Add(Enumerable.Range(0, 8).Select(_ => WindowWord()).ToArray());
string VectorBits(byte[] bytes) => $"0x{Convert.ToHexString(bytes.Reverse().ToArray())}";
var signWindow = runtime.GetMethod("SignWindow")!;
var windowObserved = windowInputs.Select(input =>
{
    var bytes = new byte[32];
    ((Vector256<ulong>)signWindow.Invoke(null, input.Cast<object>().ToArray())!).AsByte().CopyTo(bytes);
    return bytes;
}).ToArray();
// The cases must separate the model from a table chosen by index bit 3 or a swapped pair of tables.
foreach ((string mutant, int tableBit, bool swapTables) in new[]
{
    ("bit 3 table", 3, false), ("swapped tables", 2, true)
})
{
    var agrees = windowInputs.Select((input, index) =>
    {
        ulong fill = (long)input[3] < 0 ? ulong.MaxValue : 0;
        var lanes = input[4..].Select(selector =>
            (((selector >> tableBit) & 1) == 1) != swapTables ? fill : input[(int)(selector & 3)]);
        return lanes.SelectMany(BitConverter.GetBytes).SequenceEqual(windowObserved[index]);
    });
    if (agrees.All(same => same))
        throw new InvalidOperationException($"Permutation inputs do not reject the {mutant} mutant");
}
uint[] words = Enumerable.Range(0, 8).Select(_ => (uint)WindowWord()).ToArray();
var wordBytes = new byte[32];
((Vector256<uint>)runtime.GetMethod("CreateWords")!.Invoke(null, words.Cast<object>().ToArray())!)
    .AsByte().CopyTo(wordBytes);
string Invocation(IEnumerable<string> arguments, string result) =>
    $"(CIL.Safety.invoke Extracted.program 64 0 [{string.Join(", ", arguments)}] CIL.Safety.Memory.empty)" +
    $".map Prod.snd =\n      .ok [.scalar ({result})]";
// A single proof is not an anonymous-constructor conjunction, so it stays unwrapped.
string Conjunction(IEnumerable<string> proofs) =>
    proofs.Count() == 1 ? $"({proofs.Single()})" : $"⟨{string.Join(", ", proofs)}⟩";
foreach ((string name, string[] claims) in new[]
{
    ("SignWindow", windowInputs.Select((input, index) => Invocation(input.Select(word => $".scalar (.i64 {word})"),
        $".v256 {VectorBits(windowObserved[index])}")).ToArray()),
    ("CreateWords",
        [Invocation(words.Select(word => $".scalar (.i32 {word})"), $".v256 {VectorBits(wordBytes)}")])
})
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, $$"""
        import Extracted
        import CIL.Safety.Execution
        namespace ExampleProof
        /-- Successful observations identify the successful checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- The host CPU's results on the same arguments. -/
        theorem correctness :
            {{string.Join(" ∧\n    ", claims)}} := by
          exact {{Conjunction(claims.Select(_ => "by apply result_of_toOption; decide +kernel"))}}
        #print axioms correctness
        end ExampleProof
        """);
    pending.Add((new(selectors[name], proof, output), "x64-v4",
        () => Console.WriteLine($"PASS {name} matches the host CPU on {claims.Length} inputs")));
}

// No host here runs AdvSimd, so REV64 is checked against BinaryPrimitives.ReverseEndianness of each lane. The
// halves are checked against the host's own Load/StoreUnsafe; a destination one byte short faults on the second store.
var reverseClaims = new[] { (0x0706050403020100UL, 0x0f0e0d0c0b0a0908UL), (WindowWord(), WindowWord()) }
    .Select(input =>
    {
        var bytes = new byte[16];
        Vector128.Create(BinaryPrimitives.ReverseEndianness(input.Item1),
            BinaryPrimitives.ReverseEndianness(input.Item2)).AsByte().CopyTo(bytes);
        return Invocation([$".scalar (.i64 {input.Item1})", $".scalar (.i64 {input.Item2})"],
            $".v128 {VectorBits(bytes)}");
    }).ToArray();
var reverseOutput = Path.Combine(root, "ReverseLimbs");
Directory.CreateDirectory(reverseOutput);
var reverseProof = Path.Combine(reverseOutput, "Proof.lean");
File.WriteAllText(reverseProof, $$"""
    import Extracted
    import CIL.Safety.Execution
    namespace ExampleProof
    /-- Each 64-bit lane byte-reversed in place, as BinaryPrimitives.ReverseEndianness reverses it. -/
    theorem correctness :
        {{string.Join(" ∧\n    ", reverseClaims)}} := by
      exact ⟨{{string.Join(", ", reverseClaims.Select(_ => "by rfl"))}}⟩
    #print axioms correctness
    end ExampleProof
    """);
pending.Add((new(selectors["ReverseLimbs"], reverseProof, reverseOutput), "arm64-advsimd",
    () => Console.WriteLine("PASS ReverseLimbs reverses the bytes of each lane under arm64-advsimd")));
var halves = new byte[32];
windowRandom.NextBytes(halves);
var swappedHalves = new byte[32];
runtime.GetMethod("SwapHalves")!.CreateDelegate<HalfSwap>()(halves, swappedHalves);
if (!swappedHalves.SequenceEqual(halves[16..].Concat(halves[..16])))
    throw new InvalidOperationException("Runtime SwapHalves did not swap the 16-byte halves");
var halvesOutput = Path.Combine(root, "SwapHalves");
Directory.CreateDirectory(halvesOutput);
var halvesProof = Path.Combine(halvesOutput, "Proof.lean");
File.WriteAllText(halvesProof, $$"""
    import Extracted
    import CIL.Safety.Execution
    namespace ExampleProof
    /-- The source bytes. -/
    private def source : List (BitVec 8) := [{{string.Join(", ", halves)}}]
    /-- A read-only 32-byte source and a zeroed writable destination of `length` bytes. -/
    private def memory (length : Nat) : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
      allocations := fun identity => if identity == 0 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩
        else if identity == 1 then some ⟨.callerStack, ⟨length, 1, []⟩, true, [length]⟩ else none
      cells := fun identity offset => ⟨if identity == 0 then source.getD offset 0 else 0, true⟩
      views := [⟨0, 0, 32, true, false⟩, ⟨1, 0, length, true, true⟩]
      nextIdentity := 2 }
    /-- The method over the source and a destination span of `length` bytes. -/
    private def run (length : Nat) :=
      CIL.Safety.invoke Extracted.program 64 0
        [.bufferSpan ⟨.address ⟨0, 0⟩, 32, 1, false⟩, .bufferSpan ⟨.address ⟨1, 0⟩, length, 1, true⟩]
        (memory length)
    /-- The destination holds the host's swapped halves and nothing is returned. -/
    theorem correctness :
        (run 32).map (fun result =>
          ((List.range 32).map fun offset => (result.1.cells 1 offset).1.toNat, result.2)) =
          .ok ([{{string.Join(", ", swappedHalves)}}], []) := by
      rfl
    #print axioms correctness
    /-- The second store into a 31-byte destination is outside the allocation. -/
    theorem short_destination_faults :
        ((run 31).mapError (fun fault => fault.fault)).map Prod.snd =
          .error (.memory .outsideAllocation (.address ⟨1, 16⟩) 16) := by
      rfl
    #print axioms short_destination_faults
    end ExampleProof
    """);
pending.Add((new(selectors["SwapHalves"], halvesProof, halvesOutput), "arm64-advsimd",
    () => Console.WriteLine("PASS SwapHalves matches the host's halves and faults past a short destination")));
Flush();
// Without AdvSimd or AVX-512 VL the reachable calls are rejected before any evidence is written.
foreach ((string name, string profile, string feature) in new[]
{
    ("ReverseLimbs", "x64-v4", "AdvSimd"), ("SignWindow", "x64-v3", "Avx512FVL")
})
{
    var rejectedOutput = Path.Combine(root, $"{name}-{profile}");
    Directory.CreateDirectory(rejectedOutput);
    File.Delete(Path.Combine(rejectedOutput, "Extracted.lean"));
    var rejectedCall = Execute(Extract("extract", assembly, "Examples", selectors[name], rejectedOutput, profile));
    if (rejectedCall.Code == 0 || File.Exists(Path.Combine(rejectedOutput, "Extracted.lean")) ||
        !rejectedCall.Output.Contains($"Reachable intrinsic lacks {feature}", StringComparison.Ordinal))
        throw new InvalidOperationException(
            $"{name} admitted without {feature} under {profile}: {rejectedCall.Output}");
    Console.WriteLine($"PASS {name} rejected under {profile}");
}
// Forged evidence must not change the table select, the lane reversal, or a transfer's offset form.
var rejectedEndian = new RejectedEvidence(Path.Combine(root, "RejectedEndian"));
foreach ((string name, string theorem, string before, string after, string validator, int index) in new[]
{
    ("SignWindow", "method0_intrinsics_validated", ".avx512 .permuteVar4x64x2", ".avx512 .ternaryLogic",
        "ExactIntrinsicsValid", 0),
    ("ReverseLimbs", "method0_intrinsics_validated", ".advSimd .reverseElement8", ".avx2 .shuffleBytes",
        "ExactIntrinsicsValid", 1),
    ("SwapHalves", "method0_unsafe_validated", ".vector128Unsafe true true", ".vector128Unsafe true false",
        "UnsafeCallsValid", 2),
    ("SwapHalves", "method0_unsafe_validated", ".memory (.vector128Unsafe false false)", ".memory .load128",
        "UnsafeCallsValid", 3)
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")), theorem);
    if (!source.Contains(before, StringComparison.Ordinal))
        throw new InvalidOperationException($"Missing {name} mutation: {before}");
    var path = Path.Combine(root, "RejectedEndian", $"{name}-{index}.lean");
    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejectedEndian.Add(path, $"PASS forged {name} evidence rejected by {validator}", validator);
}
rejectedEndian.Check();

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
        throw new InvalidOperationException("Exact intrinsic profile matches no .NET 10 x64 ISA level: " + profile);
}

partial class Program
{
    delegate Vector256<byte> WideShuffle(ReadOnlySpan<byte> source, ReadOnlySpan<byte> control);
    delegate Vector128<byte> NarrowShuffle(ReadOnlySpan<byte> source, ReadOnlySpan<byte> control);
    delegate void HalfSwap(ReadOnlySpan<byte> source, Span<byte> destination);
}
