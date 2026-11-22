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
#:include RejectedEvidence.cs
#:include ModelOperandChecks.cs
#:include HardwareExamples.cs
#:include ContractVariants.cs

using System.Buffers.Binary;
using System.Reflection;
using System.Text.Json;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using Mono.Cecil;
using Mono.Cecil.Cil;
using X86Aes = System.Runtime.Intrinsics.X86.Aes;

using Program verification = new();
Run(["lake", "build", "Tests.ExactIntrinsics", "Tests.HalfSwapContract"], verification.CheckoutPackage());
string assembly = At("Examples/Assembly/bin/Examples.dll");
using ModuleDefinition metadata = ModuleDefinition.ReadModule(assembly);
var divisionMethods = metadata.GetType("Examples.DivisionIntrinsics").Methods.ToDictionary(method => method.Name);
var selectors = divisionMethods.ToDictionary(pair => pair.Key, pair => pair.Value.FullName);
Type runtime = Assembly.LoadFile(assembly).GetType("Examples.DivisionIntrinsics")!;
string root = At("artifacts/DivisionIntrinsics");
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
    return $"@{path}";
}
var hardwareRoot = Path.Combine(root, "HardwareMembers");
Directory.CreateDirectory(hardwareRoot);
var hardwareImage = Path.Combine(hardwareRoot, "HardwareMembers.dll");
var hardwareExamples = HardwareExamples.Write(assembly, hardwareImage,
    DeclareAes("x64-v4", "aes"), DeclareAes("arm64-advsimd", "armAes"));
ExtractBatch("extract", "Examples", hardwareExamples.Select(example =>
    new GeneratedExtraction(hardwareImage, example.Selector,
        Path.Combine(hardwareRoot, example.Name), example.Profile)));
using (var hardware = ModuleDefinition.ReadModule(hardwareImage))
{
    var members = hardware.GetType("Examples.HardwareMembers").Methods.ToDictionary(method => method.Name);
    // Each evidence batch keeps the kernel's memory bounded across the independent wrappers.
    foreach (var group in hardwareExamples.Chunk(8))
    {
        var evidence = new GeneratedEvidence(Path.Combine(hardwareRoot, $"Batch-{group[0].Name}"));
        foreach (var example in group)
        {
            var folder = Path.Combine(hardwareRoot, example.Name);
            var proof = Path.Combine(folder, "Operand.lean");
            File.Copy(Path.Combine(folder, "Extracted.lean"), proof, true);
            ModelOperandChecks.Append(proof, members[example.Name], _ => example.Model, example.NeedsFeature);
            evidence.Add(proof, $"PASS checked hardware MemberRef in {example.Selector}");
        }
        evidence.Check(replay: false);
    }
}


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
    var method = divisionMethods[name];
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
    string BroadcastProof(string operation, int lane, string lemma) => $$"""
        exact congrArg (Except.map Prod.snd) (CIL.Safety.invoke_broadcastBinary_word
          Extracted.profile .{{operation}} {{lane}} {{left}} {{right}} {{expected}} CIL.Safety.Memory.empty
          rfl rfl rfl Extracted.method0_model4 rfl (by decide)
          (CIL.Safety.checked_broadcast_{{lemma}} {{left}} {{right}}))
        """;
    string ShiftProof(string operation, int lane, string lemma) => $$"""
        exact congrArg (Except.map Prod.snd) (CIL.Safety.invoke_broadcastShift
          Extracted.profile .{{operation}} {{lane}} {{left}} {{right}} {{expected}} CIL.Safety.Memory.empty
          rfl rfl rfl Extracted.method0_model6 rfl (by decide)
          (CIL.Safety.checked_broadcast_{{lemma}} {{left}} {{right}}))
        """;
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

// Change only the AVX2 member reference in the compiled AND entry, keeping its broadcast and lane.
var wrongAnd = Path.Combine(root, "OrInsteadOfAnd");
Directory.CreateDirectory(wrongAnd);
var wrongAndAssembly = Path.Combine(wrongAnd, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var methods = variant.GetType("Examples.DivisionIntrinsics").Methods;
    var andMethod = methods.Single(method => method.Name == "And");
    var orMethod = methods.Single(method => method.Name == "Or");
    static bool IsAvx2Member(object? operand) => operand is MethodReference target &&
        target.DeclaringType.FullName == "System.Runtime.Intrinsics.X86.Avx2";
    andMethod.Body.Instructions.Single(site => IsAvx2Member(site.Operand)).Operand =
        orMethod.Body.Instructions.Single(site => IsAvx2Member(site.Operand)).Operand;
    variant.Write(wrongAndAssembly);
}
verification.VerifyContractVariant(assembly, "Examples", selectors["And"], Path.Combine(root, "AndContract"),
    wrongAndAssembly, selectors["And"], wrongAnd, """
    /-- Every pair of words returns its bitwise intersection and preserves caller memory. -/
    def intersection : MethodContract (W64 × W64) W64 where
      args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
      results value := [.scalar (.i64 value)]
      pre _ _ := True
      footprint _ := []
      post input before after value := after = before ∧ value = (input.1 &&& input.2)
    """, """
    /-- The selected lane of the compiled AVX2 broadcast returns the intersection. -/
    theorem correctness : intersection.Holds Extracted.program 0 := by
      rintro ⟨left, right⟩ memory -
      apply MethodContract.Holds.intro (c := intersection) (input := (left, right))
        memory (left &&& right) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
      exact ⟨256, invoke_broadcastBinary_word Extracted.profile .band 0 left right _ memory
        rfl rfl rfl Extracted.method0_model4 rfl (by decide) (checked_broadcast_and left right)⟩
    """, """
    /-- On disjoint words one and two the replacement returns three. The intersection is zero. -/
    theorem correctness : intersection.Refuted Extracted.program 0 :=
      .of_return (input := (1, 2)) (initial := Memory.empty) trivial
        (invoke_broadcastBinary_word Extracted.profile .bor 0 1 2 3 Memory.empty
          rfl rfl rfl Extracted.method0_model4 rfl (by decide) (checked_broadcast_or 1 2))
        (by rintro ⟨-, value, encoded, -, rfl⟩; revert encoded; decide)
    """, profile: "x64-v3", imports: "import CIL.Safety.IntrinsicExecution");
Console.WriteLine("PASS AVX2 AND contract and certified OR replacement at (1, 2)");

foreach (var (name, width, zero, highBit) in new (string, int, object, object)[]
{
    ("EqualBytes256", 256, Vector256<byte>.Zero, Vector256<byte>.Zero.WithElement(31, (byte)0x80)),
    ("EqualSigned512", 512, Vector512<long>.Zero, Vector512<long>.Zero.WithElement(7, long.MinValue))
})
{
    var folder = Path.Combine(root, name + "LeftTwice");
    Directory.CreateDirectory(folder);
    var image = Path.Combine(folder, "Examples.dll");
    using (var variant = ModuleDefinition.ReadModule(assembly))
    {
        var method = variant.GetType("Examples.DivisionIntrinsics").Methods.Single(method => method.Name == name);
        method.Body.Instructions.Single(site => site.OpCode.Code == Code.Ldarg_1).OpCode = OpCodes.Ldarg_0;
        variant.Write(image);
    }
    var original = runtime.GetMethod(name)!;
    var changed = Assembly.Load(File.ReadAllBytes(image)).GetType("Examples.DivisionIntrinsics")!.GetMethod(name)!;
    if (original.Invoke(null, [zero, zero]) is not true || original.Invoke(null, [zero, highBit]) is not false ||
        changed.Invoke(null, [zero, highBit]) is not true)
        throw new InvalidOperationException($"Unexpected CLR equality result for {name}");
    verification.VerifyContractVariant(assembly, "Examples", selectors[name], Path.Combine(root, name + "Contract"),
        image, selectors[name], folder, $$"""
        /-- Equality compares every bit of the two vectors and preserves caller memory. -/
        def equalVectors : MethodContract (BitVec {{width}} × BitVec {{width}}) Bool where
          args pair := [.scalar (.v{{width}} pair.1), .scalar (.v{{width}} pair.2)]
          results equal := [.scalar (.i32 (if equal then 1 else 0))]
          pre _ _ := True
          footprint _ := []
          post pair before after equal := after = before ∧ equal = (pair.1 == pair.2)
        """, """
        set_option maxRecDepth 8192 in
        theorem correctness : equalVectors.Holds Extracted.program 0 := by
          rintro ⟨left, right⟩ memory -
          apply MethodContract.Holds.intro (c := equalVectors) (input := (left, right)) memory
            (left == right) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
          refine ⟨16, ?_⟩
          change Except.ok (memory, [Value.scalar (.i32
            (CIL.NarrowKind.unsigned8.extend (if left == right then 1 else 0)))]) =
            Except.ok (memory, [Value.scalar (.i32 (if left == right then 1 else 0))])
          rw [CIL.NarrowKind.extend_ite_one_zero]
        """, $$"""
        set_option maxRecDepth 8192 in
        theorem correctness : equalVectors.Refuted Extracted.program 0 := by
          apply MethodContract.Refuted.of_return (c := equalVectors) (program := Extracted.program)
            (method := 0) (input := (0, 1 <<< {{width - 1}})) (initial := Memory.empty)
            (fuel := 16) (values := [.scalar (.i32 1)]) trivial rfl
          rintro ⟨_, value, encoded, _, rfl⟩
          revert encoded
          decide
        """);
    Console.WriteLine($"PASS {name}: the top bit distinguishes the original from the repeated-operand variant");
}

// Keep the broadcasts, vector local and MoveMask while reversing the unsigned comparison.
var wrongLess = Path.Combine(root, "GreaterInsteadOfLess");
Directory.CreateDirectory(wrongLess);
var wrongLessAssembly = Path.Combine(wrongLess, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var methods = variant.GetType("Examples.DivisionIntrinsics").Methods;
    static Instruction Comparison(MethodDefinition method, string name) =>
        method.Body.Instructions.Single(site => site.Operand is MethodReference target &&
            target.DeclaringType.FullName == "System.Runtime.Intrinsics.X86.Avx512F" && target.Name == name);
    Comparison(methods.Single(method => method.Name == "Less"), "CompareLessThan").Operand =
        Comparison(methods.Single(method => method.Name == "Greater"), "CompareGreaterThan").Operand;
    variant.Write(wrongLessAssembly);
}
if (Avx512F.IsSupported && Avx512DQ.IsSupported)
{
    const ulong high = 1UL << 63;
    var changedType = Assembly.LoadFile(wrongLessAssembly).GetType("Examples.DivisionIntrinsics")!;
    var original = runtime.GetMethod("Less")!.CreateDelegate<Func<ulong, ulong, int>>();
    var changed = changedType.GetMethod("Less")!.CreateDelegate<Func<ulong, ulong, int>>();
    if (original(1, high) != 255 || changed(1, high) != 0)
        throw new InvalidOperationException("AVX-512 comparison masks differ from the unsigned high-bit witness.");
}
verification.VerifyContractVariant(assembly, "Examples", selectors["Less"], Path.Combine(root, "LessContract"),
    wrongLessAssembly, selectors["Less"], wrongLess, """
    /-- An unsigned comparison returns eight identical mask bits in well-formed caller memory. -/
    def unsignedMask : MethodContract (W64 × W64) W32 where
      args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
      results value := [.scalar (.i32 value)]
      pre _ memory := memory.WellFormed
      footprint _ := []
      post input _ _ value := value = if input.1.ult input.2 then 255 else 0
    """, """
    open CIL
    /-- The same unsigned word in all eight lanes. -/
    private abbrev splat (word : W64) := Vector.pack512 word word word word word word word word
    /-- The comparison sets every mask bit precisely when the left word is smaller. -/
    private theorem mask (left right : W64) :
        Vector.moveMask512 (Vector.zip512 (fun x y => Vector.mask64 (x.ult y))
          (splat left) (splat right)) = (if left.ult right then 255 else 0) := by
      simp only [splat, Vector.zip512, Vector.lane512_0, Vector.lane512_1,
        Vector.lane512_2, Vector.lane512_3, Vector.lane512_4, Vector.lane512_5,
        Vector.lane512_6, Vector.lane512_7]
      cases left.ult right <;> rfl

    #print axioms mask

    set_option maxRecDepth 8192
    set_option exponentiation.threshold 1024
    /-- The compiled method initializes one 512-bit vector local. -/
    private def localSpec : NumericLocalSpec := ⟨.vector512, .v512 0, 0, rfl⟩
    /-- The checked call returns the comparison mask and confines its write to the fresh local. -/
    theorem correctness : unsignedMask.Holds Extracted.program 0 := by
      rintro ⟨left, right⟩ memory formed
      let args : List CIL.Safety.Value := [.scalar (.i64 left), .scalar (.i64 right)]
      obtain ⟨frame, entered, setup, homes, _, _⟩ :=
        numeric_frame_setup Extracted.method0 [localSpec] rfl rfl rfl rfl memory args formed
      obtain ⟨home, slot, fresh, _, writable⟩ := homes.home_at 0 localSpec rfl
      obtain ⟨after, stored, written, readback⟩ := step_store_numeric_local
        (body := Extracted.method0) (pc := 10) (args := args) (rest := [.scalar (.v512 (splat left))])
        .vector512 (.v512 (splat right)) (splat right).toNat rfl slot writable
      have loaded := step_load_numeric_local (body := Extracted.method0) (pc := 11)
        (args := args) (stack := [.scalar (.v512 (splat left))]) .vector512
        (.v512 (splat right)) (splat right).toNat rfl slot readback
      have preserved := write_preserves_memory_below _ _ _ _ _ _ fresh written
      have final := Confined.frame_round_trip setup preserved (Nat.le_of_eq (write_nextIdentity written).symm)
      apply MethodContract.Holds.intro (c := unsignedMask) (input := (left, right)) (leaveFrame frame after)
        (if left.ult right then 255 else 0) ?_ final rfl
      refine ⟨64, invoke_of_run Extracted.program_method0 rfl setup ?_⟩
      cil_checked_steps []
      refine (run_next (fuel := 53) Extracted.program_method0 (by rfl) stored).trans ?_
      refine (run_next (fuel := 52) Extracted.program_method0 (by rfl) loaded).trans ?_
      rw [← mask left right]
      rfl
    """, """
    set_option maxRecDepth 8192
    set_option exponentiation.threshold 1024
    /-- Returning zero violates the postcondition regardless of the final memory. -/
    private theorem wrongMask (after : Memory) :
        ¬ unsignedMask.Returns (1, 0x8000000000000000) Memory.empty after [.scalar (.i32 0)] := by
      rintro ⟨value, encoded, rfl⟩
      exact (by decide : ¬ ([Value.scalar (.i32 0)] = [.scalar (.i32 255)])) encoded

    #print axioms wrongMask

    /-- Reversing the comparison clears every mask bit on this unsigned input. -/
    theorem correctness : unsignedMask.Refuted Extracted.program 0 := by
      let high : W64 := 0x8000000000000000
      let call := invoke Extracted.program 64 0 [.scalar (.i64 1), .scalar (.i64 high)] Memory.empty
      have observed : call.map Prod.snd = .ok [.scalar (.i32 0)] := by decide +kernel
      cases ran : call with
      | error fault => simp [ran, Except.map] at observed
      | ok result =>
        obtain ⟨after, values⟩ := result
        have actual : values = [.scalar (.i32 0)] := by simpa [ran, Except.map] using observed
        subst values
        exact MethodContract.Refuted.of_return (c := unsignedMask) (input := (1, high))
          (program := Extracted.program) (fuel := 64) (method := 0) (final := after)
          (values := [.scalar (.i32 0)]) Memory.empty_wellFormed ran (fun h => wrongMask after h.2)
    """, profile: "x64-v4", imports: "import CIL.Safety.LocalSnapshots\nimport CIL.SIMD.PackedLanes");
Console.WriteLine("PASS AVX-512 unsigned comparison contract and certified greater-than replacement");

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
    ("Shuffle256", 32, "x64-v3", "x64-sse42", "Avx2"), ("Shuffle128", 16, "x64-sse42", "scalar", "Ssse3")
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
            $".error ⟨0, {pc}, .thrown .argumentOutOfRange⟩"));
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

static string ShuffleProof(int width, string contract) => $$"""
        set_option maxRecDepth 8192 in
        /-- The compiled shuffle reads each valid span once and leaves caller memory unchanged. -/
        theorem correctness : {{contract}}.Holds Extracted.program 0 := by
          rintro ⟨s, c⟩ memory ⟨⟨sv, ss, sr⟩, cv, cs, cr⟩
          apply MethodContract.Holds.intro (c := {{contract}}) (input := (s, c)) memory
            (CIL.Vector.shuffleBytes{{width}} s.bits c.bits) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
          refine ⟨32, ?_⟩
          change invoke Extracted.program 32 0
            [.bufferSpan (byteSpan s.address s.length), .bufferSpan (byteSpan c.address c.length)] memory =
              .ok (memory, [.scalar (.v{{width}} (CIL.Vector.shuffleBytes{{width}} s.bits c.bits))])
          have first := read_span memory s.address s.length (.v{{width}} s.bits) sv ss sr []
          have second := read_span memory c.address c.length (.v{{width}} c.bits) cv cs cr [.scalar (.v{{width}} s.bits)]
          cil_checked_steps [sv, cv, first, second]
        """;

// The AVX2 source halves contain ones and twos. Bit 7 masks every low byte.
static byte[] Halves(byte low, byte high) =>
    Enumerable.Repeat(low, 16).Concat(Enumerable.Repeat(high, 16)).ToArray();
var shuffleSource = Halves(1, 2);
var shuffleMask = Halves(0x80, 0);
if (!RuntimeShuffle(runtime.GetMethod("Shuffle256")!, shuffleSource, shuffleMask).SequenceEqual(Halves(0, 2)))
    throw new InvalidOperationException("AVX2 did not mask the low half or select byte two in the high half.");
foreach ((string name, byte low, byte high) in new (string, byte, byte)[]
{
    ("ShuffleCrossHalf", 0, 1), ("ShuffleIgnoreHighBit", 1, 2)
})
{
    if (!RuntimeShuffle(runtime.GetMethod(name)!, shuffleSource, shuffleMask).SequenceEqual(Halves(low, high)))
        throw new InvalidOperationException($"The compiled {name} differs from its counterexample.");
    verification.VerifyContractVariant(assembly, "Examples", selectors["Shuffle256"],
        Path.Combine(root, "ShuffleContract"), assembly, selectors[name], Path.Combine(root, name),
        "open Tests.ShuffleContract", ShuffleProof(256, "shuffle"), $$"""
        set_option maxRecDepth 16384 in
        /-- The extracted mutant returns the wrong bytes for the two readable spans. -/
        theorem correctness : shuffle.Refuted Extracted.program 0 := by
          apply refuted_of_shuffle (fuel := 64) (actual := halves {{low}} {{high}}) (by decide)
          rfl
        """, profile: "x64-v3", imports: "import Tests.ShuffleContract");
    Console.WriteLine($"PASS AVX2 byte shuffle contract and checked {name} counterexample");
}


var reversed = Path.Combine(root, "Shuffle128Reversed");
Directory.CreateDirectory(reversed);
var reversedImage = Path.Combine(reversed, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var method = variant.GetType("Examples.DivisionIntrinsics").Methods.Single(m => m.Name == "Shuffle128");
    var loads = method.Body.Instructions.Where(i => i.OpCode.Code is Code.Ldarg_0 or Code.Ldarg_1).ToArray();
    if (loads.Length != 2 || loads[0].OpCode.Code != Code.Ldarg_0 || loads[1].OpCode.Code != Code.Ldarg_1)
        throw new InvalidOperationException("Expected the shuffle to load source and then control.");
    (loads[0].OpCode, loads[1].OpCode) = (loads[1].OpCode, loads[0].OpCode);
    variant.Write(reversedImage);
}
if (Ssse3.IsSupported)
{
    var source = Enumerable.Repeat((byte)1, 16).ToArray();
    var control = Enumerable.Repeat((byte)0x80, 16).ToArray();
    var reversedMethod = Assembly.Load(File.ReadAllBytes(reversedImage))
        .GetType("Examples.DivisionIntrinsics")!.GetMethod("Shuffle128")!;
    if (!RuntimeShuffle(runtime.GetMethod("Shuffle128")!, source, control).SequenceEqual(new byte[16]) ||
        !RuntimeShuffle(reversedMethod, source, control).SequenceEqual(control))
        throw new InvalidOperationException("The SSSE3 shuffle or its reversed variant disagrees with the witness.");
}
verification.VerifyContractVariant(assembly, "Examples", selectors["Shuffle128"], Path.Combine(root, "Shuffle128Contract"),
    reversedImage, selectors["Shuffle128"], reversed, "open Tests.ShuffleContract", ShuffleProof(128, "shuffle128"), """
    set_option maxRecDepth 8192 in
    /-- Reversing the two loads returns sixteen 0x80 bytes where the masked shuffle requires zeros. -/
    theorem correctness : shuffle128.Refuted Extracted.program 0 := by
      apply refuted_of_reversed128 (fuel := 32)
      rfl
    """, profile: "x64-sse42", imports: "import Tests.ShuffleContract");
Console.WriteLine("PASS SSSE3 byte shuffle contract and checked operand reversal");

// A forged operation at the hardware call must fail the model agreement of the complete method.
var rejectedHardware = new RejectedEvidence(Path.Combine(root, "RejectedHardware"));
void RejectHardware(string folder, string example, string member, string replacement, string label)
{
    var method = divisionMethods[example];
    var pc = method.Body.Instructions.Index().Single(item =>
        item.Item.Operand is MethodReference reference &&
        reference.FullName.Contains(member, StringComparison.Ordinal)).Index;
    var source = File.ReadAllText(Path.Combine(root, folder, "Extracted.lean"));
    var changed = "import Tests.Support.IntrinsicMethods\n" +
        ForgeModelEmission(source, pc, $".call Tests.IntrinsicMethods.{replacement}");
    var output = Path.Combine(root, "RejectedHardware");
    Directory.CreateDirectory(output);
    var path = Path.Combine(output, $"{folder}-{label}.lean");
    File.WriteAllText(path, changed);
    rejectedHardware.Add(path, $"PASS {folder} rejects {replacement}", "Extraction.RuntimeModelsAgree", "is false");
}
RejectHardware("Shuffle256", "Shuffle256", "Avx2::Shuffle(", "add64", "add");
RejectHardware("Shuffle128", "Shuffle128", "Ssse3::Shuffle(", "shiftLeftBytes", "shift");

// The hash round is compared with the host CPU's AESENC under a custom x64 and a custom ARM64 AES
// profile; the ARM64 extraction must agree, since AESE with a zero key, AESMC and the key are AESENC.
if (!X86Aes.IsSupported) throw new InvalidOperationException("The AES differential test needs an x86 AES host");

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
// Both profiles must implement the same round for every input and reject a lost high key half.
var wrongAes = Path.Combine(root, "AesRoundLowKeyTwice");
Directory.CreateDirectory(wrongAes);
var wrongAesImage = Path.Combine(wrongAes, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var round = variant.GetType("Examples.DivisionIntrinsics").Methods.Single(m => m.Name == "AesRound");
    var highKey = round.Body.Instructions.Single(i => i.OpCode.Code == Code.Ldarg_3);
    if (highKey.Previous?.OpCode.Code != Code.Ldarg_2 ||
        highKey.Next?.Operand is not MethodReference { Name: "Create" })
        throw new InvalidOperationException("Expected the two key halves before Vector128.Create.");
    highKey.OpCode = OpCodes.Ldarg_2;
    variant.Write(wrongAesImage);
}
var wrongRound = Assembly.Load(File.ReadAllBytes(wrongAesImage)).GetType("Examples.DivisionIntrinsics")!.GetMethod("AesRound")!;
var keyWitness = new object[] { 0UL, 0UL, 0UL, 1UL };
var expectedZeroRound = Vector128.Create((byte)0x63).AsUInt64();
var observedRound = ((Vector128<byte>)aesRound.Invoke(null, keyWitness)!).AsUInt64();
var observedWrongRound = ((Vector128<byte>)wrongRound.Invoke(null, keyWitness)!).AsUInt64();
if (observedWrongRound != expectedZeroRound || observedRound != (expectedZeroRound ^ Vector128.Create(0UL, 1UL)))
    throw new InvalidOperationException("The CLR AES results disagree with the high-key witness.");

foreach (var (label, profile, arm) in new[]
{
    ("x64", DeclareAes("x64-v4", "aes"), false), ("arm64", DeclareAes("arm64-advsimd", "armAes"), true)
})
{
    var result = arm ? """
          change [Value.scalar (.v128 (CIL.Vector.aesMixColumns (CIL.Vector.armAesEncrypt state 0) ^^^ key))] =
            [Value.scalar (.v128 (CIL.Vector.aesEncryptRound state key))]
          rw [CIL.Vector.armAes_round_eq_aesEncryptRound]
        """ : "  rfl";
    verification.VerifyContractVariant(assembly, "Examples", selectors["AesRound"], Path.Combine(root, "AesRoundContract-" + label),
        wrongAesImage, selectors["AesRound"], Path.Combine(wrongAes, label), "open Tests.AesRoundContract", $$"""
        bind_entry entry (memory : Memory) (a b k l : W64) (wf : memory.WellFormed) :=
          Extracted.method0 with [.scalar (.i64 a), .scalar (.i64 b), .scalar (.i64 k), .scalar (.i64 l)]
          from memory allocating wf

        set_option maxRecDepth 8192 in
        /-- The compiled round uses its two fresh vector locals and preserves caller storage. -/
        theorem correctness : roundContract.Holds Extracted.program 0 := by
          rintro ⟨a, b, k, l⟩ memory wf
          obtain ⟨stateHome, keyHome, entered, enter⟩ := entry.checked memory a b k l wf
          let state := CIL.Vector.pack128 a b
          let key := CIL.Vector.pack128 k l
          obtain ⟨first, stateStore, frame1, -⟩ := (enter.frame []).store 0 (.v128 state) rfl
          obtain ⟨second, keyStore, frame2, -⟩ := frame1.store 1 (.v128 key) rfl
          apply WP.enter (by rfl) (by rfl) enter.setup
          have stateRead := frame2.snapshots.read_vector128 (index := 0) (bits := state) rfl (by rfl)
          have keyRead := frame2.snapshots.read_vector128 (index := 1) (bits := key) rfl (by rfl)
          cil_contract_steps [stateStore, keyStore, entry.frame, stateRead, keyRead, state, key]
          refine ⟨(frame2.leave enter.setup).1, CIL.Vector.aesEncryptRound state key, ?_, rfl⟩
        {{result}}
        """, """
        set_option maxRecDepth 8192 in
        /-- Reusing the low key half drops the high bit set by the witness. -/
        theorem correctness : roundContract.Refuted Extracted.program 0 := by
          apply refuted_of_dropped_key (fuel := 64)
          rfl
        """, profile: profile, imports: "import CIL\nimport CIL.Safety.LoopScaffold\nimport Tests.AesRoundContract");
    Console.WriteLine($"PASS {label} AES round contract and verified high-key counterexample");
}

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
RejectHardware("AesRound-x64", "AesRound", "X86.Aes::Encrypt(", "armEncrypt", "encrypt");
RejectHardware("AesRound-arm64", "AesRound", "Arm.Aes::MixColumns(", "armEncrypt", "mix");
Run(["dotnet", "run", "--file", At("Tests/AesHardware.cs")], cwd: Root);
Console.WriteLine("PASS host AES instructions match the Lean AES model");

// The x64-v4 sign window extraction must return VPERMT2Q's documented result, which an AVX-512 host must
// also produce. The windows a 256-bit arithmetic shift loads come first, then indices with random high bits.
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
// Index bits 0-1 pick a lane and bit 2 picks the fill table; the mutants change which bit or table it is.
byte[] Window(ulong[] input, int tableBit, bool swapTables, bool lowSign = false)
{
    ulong fill = (long)input[lowSign ? 0 : 3] < 0 ? ulong.MaxValue : 0;
    return input[4..].SelectMany(selector => BitConverter.GetBytes(
        (((selector >> tableBit) & 1) == 1) != swapTables ? fill : input[(int)(selector & 3)])).ToArray();
}
var windowObserved = windowInputs.Select(input => Window(input, 2, false)).ToArray();
if (Avx512F.VL.IsSupported)
{
    var signWindow = runtime.GetMethod("SignWindow")!;
    foreach ((ulong[] input, byte[] expected) in windowInputs.Zip(windowObserved))
    {
        var bytes = new byte[32];
        ((Vector256<ulong>)signWindow.Invoke(null, input.Cast<object>().ToArray())!).AsByte().CopyTo(bytes);
        if (!bytes.SequenceEqual(expected))
            throw new InvalidOperationException("Host VPERMT2Q differs from its documented sign window");
    }
    Console.WriteLine($"PASS host VPERMT2Q matches the sign window reference on {WindowCases} inputs");
}
else
    Console.WriteLine("SKIP host VPERMT2Q comparison: no AVX-512VL; the extraction is checked against the reference");
// The cases must separate the reference from a table chosen by index bit 3 or a swapped pair of tables.
foreach ((string mutant, int tableBit, bool swapTables) in new[]
{
    ("bit 3 table", 3, false), ("swapped tables", 2, true)
})
{
    if (windowInputs.Select((input, index) => Window(input, tableBit, swapTables).SequenceEqual(windowObserved[index]))
        .All(same => same))
        throw new InvalidOperationException($"Permutation inputs do not reject the {mutant} mutant");
}
// Change the VPERMQ immediate to broadcast limb zero's sign to all four upper-table lanes.
var lowSign = Path.Combine(root, "SignWindowLowSign");
Directory.CreateDirectory(lowSign);
var lowSignImage = Path.Combine(lowSign, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var method = variant.GetType("Examples.DivisionIntrinsics").Methods.Single(m => m.Name == "SignWindow");
    var permute = method.Body.Instructions.Single(instruction =>
        instruction.OpCode == OpCodes.Call && instruction.Operand is MethodReference
            { Name: "Permute4x64", DeclaringType.FullName: "System.Runtime.Intrinsics.X86.Avx2" });
    var control = permute.Previous;
    if (control.OpCode != OpCodes.Ldc_I4 || control.Operand is not 255)
        throw new InvalidDataException("The sign broadcast must select lane three for all four lanes.");
    control.OpCode = OpCodes.Ldc_I4_0;
    control.Operand = null;
    variant.Write(lowSignImage);
}
// Exchange the two tables passed to VPERMT2Q, keeping the index vector unchanged.
var swappedTables = Path.Combine(root, "SignWindowSwappedTables");
Directory.CreateDirectory(swappedTables);
var swappedImage = Path.Combine(swappedTables, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var method = variant.GetType("Examples.DivisionIntrinsics").Methods.Single(m => m.Name == "SignWindow");
    var tableCall = method.Body.Instructions.Single(instruction =>
        instruction.OpCode == OpCodes.Call && instruction.Operand is MethodReference { Name: "PermuteVar4x64x2" });
    var storeFill = method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Stloc_0);
    var loadFill = tableCall.Previous;
    if (loadFill.OpCode != OpCodes.Ldloc_0 || method.Body.Variables.Count != 1)
        throw new InvalidDataException("Expected the upper sign table in local zero before VPERMT2Q.");
    var sourceTable = new VariableDefinition(method.Body.Variables[0].VariableType);
    method.Body.Variables.Add(sourceTable);
    var il = method.Body.GetILProcessor();
    var saveSource = il.Create(OpCodes.Stloc, sourceTable);
    il.InsertAfter(storeFill, saveSource);
    il.InsertAfter(saveSource, il.Create(OpCodes.Ldloc_0));
    il.Replace(loadFill, il.Create(OpCodes.Ldloc, sourceTable));
    variant.Write(swappedImage);
}
// Move bit 3 of each scalar selector to bit 2 before VPERMT2Q chooses a table.
var bitThree = Path.Combine(root, "SignWindowBitThree");
Directory.CreateDirectory(bitThree);
var bitThreeImage = Path.Combine(bitThree, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var method = variant.GetType("Examples.DivisionIntrinsics").Methods.Single(m => m.Name == "SignWindow");
    var indices = method.Body.Instructions.Where(instruction => instruction.OpCode == OpCodes.Ldarg_S
        && instruction.Operand is ParameterDefinition { Index: >= 4 and <= 7 }).ToArray();
    if (!indices.Select(instruction => ((ParameterDefinition)instruction.Operand).Index).SequenceEqual([4, 5, 6, 7]))
        throw new InvalidDataException("Expected four scalar selector loads in lane order.");
    var il = method.Body.GetILProcessor();
    foreach (var load in indices)
    {
        var next = load.Next;
        // (index & 3) | ((index >> 1) & 4) preserves the lane and changes the table selector.
        il.InsertBefore(next, il.Create(OpCodes.Ldc_I4_3));
        il.InsertBefore(next, il.Create(OpCodes.Conv_I8));
        il.InsertBefore(next, il.Create(OpCodes.And));
        il.InsertBefore(next, il.Create(OpCodes.Ldarg_S, (ParameterDefinition)load.Operand));
        il.InsertBefore(next, il.Create(OpCodes.Ldc_I4_1));
        il.InsertBefore(next, il.Create(OpCodes.Shr_Un));
        il.InsertBefore(next, il.Create(OpCodes.Ldc_I4_4));
        il.InsertBefore(next, il.Create(OpCodes.Conv_I8));
        il.InsertBefore(next, il.Create(OpCodes.And));
        il.InsertBefore(next, il.Create(OpCodes.Or));
    }
    variant.Write(bitThreeImage);
}
const string windowContractProof = """
    set_option maxRecDepth 12288
    set_option exponentiation.threshold 1024

    /-- The compiled method stores a 256-bit sign-fill table in one frame-local slot. -/
    private def localSpec : NumericLocalSpec := ⟨.vector256, .v256 0, 0, rfl⟩

    /-- SignWindow implements the lane selector and preserves caller storage on x64-v4. -/
    theorem correctness : signWindow.Holds Extracted.program 0 := by
      rintro ⟨v, i⟩ memory formed
      let args := signWindow.args (v, i)
      let value := pack256 v.a v.b v.c v.d
      let indices := pack256 i.a i.b i.c i.d
      let fill := permute4x64 (zip256 (fun x y => mask64 (x.slt y)) value 0) 255
      obtain ⟨frame, entered, setup, homes, _, _⟩ :=
        numeric_frame_setup Extracted.method0 [localSpec] rfl rfl rfl rfl memory args formed
      obtain ⟨home, slot, fresh, _, writable⟩ := homes.home_at 0 localSpec rfl
      obtain ⟨after, stored, written, readback⟩ := step_store_numeric_local
        (body := Extracted.method0) (pc := 12) (args := args) (rest := [.scalar (.v256 value)])
        .vector256 (.v256 fill) fill.toNat rfl slot writable
      have loaded := step_load_numeric_local (body := Extracted.method0) (pc := 18)
        (args := args) (stack := [.scalar (.v256 indices), .scalar (.v256 value)])
        .vector256 (.v256 fill) fill.toNat rfl slot readback
      have preserved := write_preserves_memory_below _ _ _ _ _ _ fresh written
      have final := Confined.frame_round_trip setup preserved (Nat.le_of_eq (write_nextIdentity written).symm)
      apply MethodContract.Holds.intro (c := signWindow) (input := (v, i)) (leaveFrame frame after)
        (permuteVar4x64x2 value indices fill) ?_ final ?_
      · refine ⟨64, invoke_of_run Extracted.program_method0 rfl setup ?_⟩
        dsimp only [args, signWindow] at *
        cil_checked_steps []
        refine (run_next (fuel := 51) Extracted.program_method0 (by rfl) stored).trans ?_
        cil_checked_steps []
        refine (run_next (fuel := 45) Extracted.program_method0 (by rfl) loaded).trans ?_
        rfl
      · exact signWindow_result v i
    """;
string WindowCounterexample(string actual) => $$"""
    set_option maxRecDepth 12288
    /-- The sign bit is set only in limb three. Each selector requests the sign-fill table. -/
    private def witness : Limbs × Limbs := (⟨0, 1, 2, 0x8000000000000000⟩, ⟨4, 5, 6, 7⟩)

    /-- The compiled variant returns a different vector from the high-sign table at this input. -/
    theorem correctness : signWindow.Refuted Extracted.program 0 := by
      let call := invoke Extracted.program 128 0 (signWindow.args witness) Memory.empty
      have observed : call.map Prod.snd = .ok [.scalar (.v256 ({{actual}}))] := by decide +kernel
      cases ran : call with
      | error fault => simp [ran, Except.map] at observed
      | ok result =>
        obtain ⟨after, values⟩ := result
        have actual : values = [.scalar (.v256 ({{actual}}))] := by simpa [ran, Except.map] using observed
        subst values
        apply MethodContract.Refuted.of_return (c := signWindow) (input := witness)
          (program := Extracted.program) (fuel := 128) (method := 0) (final := after)
          (values := [.scalar (.v256 ({{actual}}))]) Memory.empty_wellFormed ran
        rintro ⟨_, value, encoded, rfl⟩
        exact (by decide : ¬ ([CIL.Safety.Value.scalar (.v256 ({{actual}}))] =
          [.scalar (.v256 (pack256 (selected witness.1 witness.2.a) (selected witness.1 witness.2.b)
            (selected witness.1 witness.2.c) (selected witness.1 witness.2.d)))])) encoded
    """;
foreach (var (image, output, actual, tableBit, swapTables) in new[]
{
    (lowSignImage, lowSign, "0", 2, false),
    (swappedImage, swappedTables, "pack256 0 1 2 0x8000000000000000", 2, true),
    (bitThreeImage, bitThree, "pack256 0 1 2 0x8000000000000000", 3, false)
})
{
    if (Avx512F.VL.IsSupported)
    {
        var changed = Assembly.Load(File.ReadAllBytes(image)).GetType("Examples.DivisionIntrinsics")!
            .GetMethod("SignWindow")!;
        ulong[] witness = [0, 1, 2, 1UL << 63, 4, 5, 6, 7];
        foreach (var input in windowInputs.Append(witness))
        {
            var observed = (Vector256<ulong>)changed.Invoke(null, input.Cast<object>().ToArray())!;
            var expected = Window(input, tableBit, swapTables, lowSign: output == lowSign);
            if (!Vector256.EqualsAll(observed.AsByte(), Vector256.Create<byte>(expected)))
                throw new InvalidDataException($"The compiled {Path.GetFileName(output)} disagreed with its scalar result.");
        }
    }
    verification.VerifyContractVariant(assembly, "Examples", selectors["SignWindow"], Path.Combine(root, "SignWindowContract"),
        image, selectors["SignWindow"], output, "open Tests.SignWindowContract CIL.Vector",
        windowContractProof, WindowCounterexample(actual), profile: "x64-v4",
        imports: "import Tests.SignWindowContract\nimport CIL.Safety.LocalSnapshots");
    Console.WriteLine($"PASS AVX-512 sign window and checked {Path.GetFileName(output)} counterexample");
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
        /-- The documented results on the same arguments, which an AVX-512 host reproduces. -/
        theorem correctness :
            {{string.Join(" ∧\n    ", claims)}} := by
          exact {{Conjunction(claims.Select(_ => "by apply result_of_toOption; decide +kernel"))}}
        #print axioms correctness
        end ExampleProof
        """);
    pending.Add((new(selectors[name], proof, output), "x64-v4",
        () => Console.WriteLine($"PASS {name} extraction matches its reference on {claims.Length} inputs")));
}

// The compiled REV64 result is checked against BinaryPrimitives.ReverseEndianness of each lane.
var reverseClaims = new[] { (0x0706050403020100UL, 0x0f0e0d0c0b0a0908UL), (WindowWord(), WindowWord()) }
    .Select(input =>
    {
        var bytes = new byte[16];
        Vector128.Create(BinaryPrimitives.ReverseEndianness(input.Item1),
            BinaryPrimitives.ReverseEndianness(input.Item2)).AsByte().CopyTo(bytes);
        if (System.Runtime.Intrinsics.Arm.AdvSimd.IsSupported)
        {
            var observed = (Vector128<ulong>)runtime.GetMethod("ReverseLimbs")!.Invoke(null, [input.Item1, input.Item2])!;
            if (observed.AsByte() != Vector128.Create((ReadOnlySpan<byte>)bytes))
                throw new InvalidOperationException("Host REV64 differs from byte reversal within each input lane.");
        }
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
// Exchange the two leading loads and preserve the intrinsic and the rest of the body.
(string Assembly, string Output) SwapFirstArguments(string methodName)
{
    var output = Path.Combine(root, "Swapped" + methodName);
    Directory.CreateDirectory(output);
    var image = Path.Combine(output, "Examples.dll");
    using var variant = ModuleDefinition.ReadModule(assembly);
    var method = variant.GetType("Examples.DivisionIntrinsics").Methods.Single(m => m.Name == methodName);
    var code = method.Body.Instructions;
    if (code[0].OpCode != OpCodes.Ldarg_0 || code[1].OpCode != OpCodes.Ldarg_1)
        throw new InvalidDataException($"{methodName} must load arguments zero and one first.");
    (code[0].OpCode, code[1].OpCode) = (code[1].OpCode, code[0].OpCode);
    variant.Write(image);
    return (image, output);
}

var equalityArguments = SwapFirstArguments("EqualWords128");
var equalWords = runtime.GetMethod("EqualWords128")!;
var swappedEqualWords = Assembly.Load(File.ReadAllBytes(equalityArguments.Assembly))
    .GetType("Examples.DivisionIntrinsics")!.GetMethod("EqualWords128")!;
object[] firstWordSet = [1u, 0u, 0u, 0u, Vector128.Create(1u, 0u, 0u, 0u)];
if (equalWords.Invoke(null, firstWordSet) is not true || swappedEqualWords.Invoke(null, firstWordSet) is not false)
    throw new InvalidOperationException("Swapping the two low words must change equality at the CLR witness.");
verification.VerifyContractVariant(assembly, "Examples", selectors["EqualWords128"],
    Path.Combine(root, "EqualWords128Contract"), equalityArguments.Assembly, selectors["EqualWords128"],
    equalityArguments.Output, """
    /-- Four 32-bit words and the vector to compare against. -/
    structure Comparison where
      a : W32
      b : W32
      c : W32
      d : W32
      expected : BitVec 128

    /-- The comparison packs the four words in lane order and preserves caller memory. -/
    def equalWords : MethodContract Comparison Bool where
      args w := [.scalar (.i32 w.a), .scalar (.i32 w.b), .scalar (.i32 w.c), .scalar (.i32 w.d),
        .scalar (.v128 w.expected)]
      results equal := [.scalar (.i32 (if equal then 1 else 0))]
      pre _ _ := True
      footprint _ := []
      post w before after equal := after = before ∧
        equal = (((w.d ++ w.c) ++ (w.b ++ w.a)) == w.expected)
    """, """
    set_option maxRecDepth 8192 in
    /-- The compiled comparison checks every bit of all four words. -/
    theorem correctness : equalWords.Holds Extracted.program 0 := by
      intro w memory _
      let equal := (((w.d ++ w.c) ++ (w.b ++ w.a)) == w.expected)
      apply MethodContract.Holds.intro (c := equalWords) (input := w) memory equal ?_
        (Confined.refl _ _) ⟨rfl, rfl⟩
      refine ⟨32, ?_⟩
      change Except.ok (memory, [Value.scalar (.i32
        (CIL.NarrowKind.unsigned8.extend (if equal then 1 else 0)))]) =
        Except.ok (memory, [Value.scalar (.i32 (if equal then 1 else 0))])
      rw [CIL.NarrowKind.extend_ite_one_zero]
    """, """
    /-- Moving the only set bit from lane zero to lane one changes the return to false. -/
    theorem correctness : equalWords.Refuted Extracted.program 0 := by
      apply MethodContract.Refuted.of_return (c := equalWords) (input := ⟨1, 0, 0, 0, 1⟩)
        (initial := Memory.empty) (fuel := 32) (values := [.scalar (.i32 0)]) trivial rfl
      rintro ⟨_, value, encoded, _, rfl⟩
      revert encoded
      decide
    """);
Console.WriteLine("PASS four-word vector equality preserves memory and refutes swapped low words");

var wordArguments = SwapFirstArguments("CreateWords");
verification.VerifyContractVariant(assembly, "Examples", selectors["CreateWords"], Path.Combine(root, "WordsContract"),
    wordArguments.Assembly, selectors["CreateWords"], wordArguments.Output, """
    /-- The eight input words in argument order. -/
    structure Words where
      a : W32
      b : W32
      c : W32
      d : W32
      e : W32
      f : W32
      g : W32
      h : W32

    /-- Lane zero contains the first word, and lane seven contains the last. -/
    def lanes (w : Words) : BitVec 256 :=
      ((w.h ++ w.g) ++ (w.f ++ w.e)) ++ ((w.d ++ w.c) ++ (w.b ++ w.a))

    /-- Creating the vector packs all eight words and preserves caller memory. -/
    def createWords : MethodContract Words (BitVec 256) where
      args w := [.scalar (.i32 w.a), .scalar (.i32 w.b), .scalar (.i32 w.c), .scalar (.i32 w.d),
        .scalar (.i32 w.e), .scalar (.i32 w.f), .scalar (.i32 w.g), .scalar (.i32 w.h)]
      results v := [.scalar (.v256 v)]
      pre _ _ := True
      footprint _ := []
      post w before after v := after = before ∧ v = lanes w
    """, """
    set_option maxRecDepth 8192 in
    /-- The compiled method puts every word in its declared lane. -/
    theorem correctness : createWords.Holds Extracted.program 0 := by
      intro w memory _
      apply MethodContract.Holds.intro (c := createWords) (input := w) memory (lanes w)
        ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
      exact ⟨64, rfl⟩
    """, """
    private def input : Words := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

    set_option maxRecDepth 8192 in
    /-- Swapping the leading loads puts the only nonzero word in lane one. -/
    theorem correctness : createWords.Refuted Extracted.program 0 := by
      apply MethodContract.Refuted.of_return (input := input) (initial := Memory.empty)
        (fuel := 64) (values := [.scalar (.v256 4294967296)]) trivial rfl
      rintro ⟨_, v, encoded, _, rfl⟩
      exact (by decide : ¬ ([CIL.Safety.Value.scalar (.v256 4294967296)] =
        [.scalar (.v256 (lanes input))])) encoded
    """);
Console.WriteLine("PASS vector creation packs every input lane and refutes swapped low words");

var (swappedAssembly, swapped) = SwapFirstArguments("ReverseLimbs");
verification.VerifyContractVariant(assembly, "Examples", selectors["ReverseLimbs"],
    Path.Combine(root, "ReverseContract"), swappedAssembly, selectors["ReverseLimbs"], swapped, """
    open CIL (reverseBytes)
    open CIL.Vector (pack128 map128_pack128)

    /-- Both limbs stay in their original lanes, with the bytes in each limb reversed. -/
    def reversed : MethodContract (W64 × W64) (BitVec 128) where
      args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
      results value := [.scalar (.v128 value)]
      pre _ _ := True
      footprint _ := []
      post input before after value := after = before ∧
        value = pack128 (reverseBytes input.1) (reverseBytes input.2)
    """, """
    /-- REV64 reverses each input limb and preserves the caller's memory. -/
    theorem correctness : reversed.Holds Extracted.program 0 := by
      rintro ⟨low, high⟩ memory -
      apply MethodContract.Holds.intro (c := reversed) (input := (low, high)) memory
        (pack128 (reverseBytes low) (reverseBytes high)) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
      refine ⟨64, ?_⟩
      change invoke Extracted.program 64 0 [.scalar (.i64 low), .scalar (.i64 high)] memory =
        .ok (memory, [.scalar (.v128 (pack128 (reverseBytes low) (reverseBytes high)))])
      rw [← map128_pack128]
      rfl
    """, """
    /-- Distinct limbs expose the swapped argument loads on a successful execution. -/
    theorem correctness : reversed.Refuted Extracted.program 0 := by
      have ran : invoke Extracted.program 64 0 [.scalar (.i64 1), .scalar (.i64 2)] Memory.empty =
          .ok (Memory.empty, [.scalar (.v128 (pack128 (reverseBytes 2) (reverseBytes 1)))]) := rfl
      exact .of_return (input := (1, 2)) trivial ran
        (by rintro ⟨-, value, encoded, -, rfl⟩; revert encoded; decide)
    """, profile: "arm64-advsimd", imports: "import CIL.SIMD.PackedLanes");
Console.WriteLine("PASS ARM64 REV64 contract and certified swapped lanes at (1, 2)");

var halves = new byte[32];
windowRandom.NextBytes(halves);
var swappedHalves = new byte[32];
var originalSwap = runtime.GetMethod("SwapHalves")!.CreateDelegate<HalfSwap>();
originalSwap(halves, swappedHalves);
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
// Move only the upper LoadUnsafe to offset zero. The compiled variant still returns normally.
var repeatedHalf = Path.Combine(root, "RepeatLowerHalf");
Directory.CreateDirectory(repeatedHalf);
var repeatedImage = Path.Combine(repeatedHalf, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var method = variant.GetType("Examples.DivisionIntrinsics").Methods.Single(m => m.Name == "SwapHalves");
    var load = method.Body.Instructions.Single(i => i.Operand is MethodReference call &&
        call.Name == "LoadUnsafe" && call.Parameters.Count == 2);
    var offset = load.Previous;
    if (offset.OpCode == OpCodes.Conv_I || offset.OpCode == OpCodes.Conv_U) offset = offset.Previous;
    if (offset.OpCode != OpCodes.Ldc_I4_S || (sbyte)offset.Operand != 16)
        throw new InvalidDataException("SwapHalves must load its second vector at byte offset 16.");
    offset.Operand = (sbyte)0;
    variant.Write(repeatedImage);
}

var repeatedSwap = Assembly.Load(File.ReadAllBytes(repeatedImage)).GetType("Examples.DivisionIntrinsics")!
    .GetMethod("SwapHalves")!.CreateDelegate<HalfSwap>();
var overlapRandom = new Random(568);
foreach (var displacement in new[] { -16, -8, -1, 0, 1, 8, 16, 32 })
{
    const int source = 24;
    var destination = source + displacement;
    for (int trial = 0; trial < 12; trial++)
    {
        var initial = new byte[96];
        overlapRandom.NextBytes(initial);
        var expected = (byte[])initial.Clone();
        initial.AsSpan(source + 16, 16).CopyTo(expected.AsSpan(destination));
        initial.AsSpan(source, 16).CopyTo(expected.AsSpan(destination + 16));
        var actual = (byte[])initial.Clone();
        originalSwap(actual.AsSpan(source, 32), actual.AsSpan(destination, 32));
        var changed = (byte[])initial.Clone();
        repeatedSwap(changed.AsSpan(source, 32), changed.AsSpan(destination, 32));
        if (!actual.AsSpan().SequenceEqual(expected) || changed.AsSpan().SequenceEqual(expected))
            throw new InvalidOperationException($"SwapHalves overlap mismatch at displacement {displacement}, trial {trial}.");
    }
}

verification.VerifyContractVariant(assembly, "Examples", selectors["SwapHalves"], Path.Combine(root, "InPlaceHalfSwap"),
    repeatedImage, selectors["SwapHalves"], repeatedHalf, "open Tests.HalfSwapContract", """
    /-- The first load snapshots the low half before either caller write. -/
    private theorem firstLoad (data : Nat → BitVec 8) (fuel : Nat) :
        invoke Extracted.program (fuel + 7) 0 (swap.args data) (memory data) =
        run Extracted.program fuel 0 7 (swap.args data) saved
          [.scalar (.v128 (packed data 0)), .readOnlyReference (.address ⟨0, 0⟩)] (entered data) := by
      with_unfolding_all rfl
    #print axioms firstLoad

    /-- The low half occupies the private local while the second load reads the high half. -/
    private theorem saveAndLoad (data : Nat → BitVec 8) (fuel : Nat) :
        run Extracted.program (fuel + 4) 0 7 (swap.args data) saved
          [.scalar (.v128 (packed data 0)), .readOnlyReference (.address ⟨0, 0⟩)] (entered data) =
        run Extracted.program fuel 0 11 (swap.args data) saved
          [.scalar (.v128 (packed data 16))] (savedLow data) := by
      unfold savedLow
      rw [← unpack data 0]
      with_unfolding_all rfl
    #print axioms saveAndLoad

    /-- The first store copies the high half into the low addresses. -/
    private theorem firstStore (data : Nat → BitVec 8) (fuel : Nat) :
        run Extracted.program (fuel + 2) 0 11 (swap.args data) saved
          [.scalar (.v128 (packed data 16))] (savedLow data) =
        run Extracted.program fuel 0 13 (swap.args data) saved [] (highWritten data) := by
      unfold highWritten
      rw [← unpack data 16]
      with_unfolding_all rfl
    #print axioms firstStore

    /-- The saved vector fills the upper half and the return retires its private home. -/
    private theorem secondStore (data : Nat → BitVec 8) :
        run Extracted.program 6 0 13 (swap.args data) saved [] (highWritten data) =
        .ok (expire (lowWritten data) 1, []) := by
      unfold lowWritten
      rw [← unpack data 0]
      with_unfolding_all rfl
    #print axioms secondStore

    /-- Every in-place swap exchanges both halves inside the caller footprint. -/
    theorem correctness : swap.Holds Extracted.program 0 := by
      rintro data _ rfl
      refine ⟨19, (expire (lowWritten data) 1, []), ?_, framed data, (), rfl, swapped data⟩
      exact (firstLoad data 12).trans ((saveAndLoad data 8).trans ((firstStore data 6).trans (secondStore data)))
    """, """
    theorem correctness : swap.Refuted Extracted.program 0 := by
      apply refuted_of_first_byte
      with_unfolding_all rfl
    """, profile: "arm64-advsimd", imports: "import Tests.HalfSwapContract");
var overlapProof = Path.Combine(root, "HalfSwapOverlap.lean");
File.Copy(At("Tests/HalfSwapOverlap.lean.in"), overlapProof, overwrite: true);
verification.Verify(assembly, "Examples", selectors["SwapHalves"], overlapProof,
    Path.Combine(root, "OverlapHalfSwap"), "arm64-advsimd", theorem: "HalfSwapOverlap.correctness");
Console.WriteLine("PASS SwapHalves contracts for all eight placements, certified repeated load and 96 CLR comparisons");
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
// Exercise every portable vector declaration over pinned example metadata.
var vectorWitnesses = new (string Name, string Profile)[]
{
    ("And", "x64-v3"), ("Less", "x64-v4"), ("SignWindow", "x64-v4"),
    ("DefinedLocal", "scalar"), ("UnsafeEquals", "scalar"), ("ReverseLimbs", "arm64-advsimd"),
    ("Shuffle128", "x64-v3"), ("Shuffle256", "x64-v3"), ("CreateWords", "scalar"),
    ("SwapHalves", "arm64-advsimd"), ("EqualWords128", "scalar"),
    ("EqualBytes256", "scalar"), ("EqualSigned512", "scalar")
};
var operandRoot = Path.Combine(root, "VectorOperands");
ExtractBatch("extract", "Examples", vectorWitnesses.Select(witness =>
    new GeneratedExtraction(assembly, selectors[witness.Name], Path.Combine(operandRoot, witness.Name),
        witness.Profile)));
var operands = new GeneratedEvidence(operandRoot);
foreach (var (name, _) in vectorWitnesses)
{
    var folder = Path.Combine(operandRoot, name);
    var proof = Path.Combine(folder, "Operand.lean");
    File.Copy(Path.Combine(folder, "Extracted.lean"), proof, true);
    var method = divisionMethods[name];
    ModelOperandChecks.Append(proof, method, VectorModel);
    if (name == "Shuffle256") CheckShuffleReadWidth(proof, method);
    operands.Add(proof, $"PASS vector operands of {name}");
}
operands.Check(replay: false);

// Each of the two source spans must provide all 32 bytes of its vector.
static void CheckShuffleReadWidth(string proof, MethodDefinition method)
{
    var reads = method.Body.Instructions.Index()
        .Where(item => item.Item.Operand is MethodReference call &&
            VectorModel(call) == ".memory (.marshalRead (.snapshot .vector256) false)")
        .Select(item => item.Index).ToArray();
    if (reads.Length != 2) throw new InvalidDataException($"Expected two vector reads in {method.FullName}");
    File.AppendAllText(proof, $$"""

        namespace Extracted
        open CIL CIL.Extraction
        /-- Neither 256-bit read can emit a direct 128-bit snapshot read. -/
        theorem shuffle_rejects_narrow_read :
            [{{string.Join(", ", reads)}}].all (fun pc => (fixtureOperandCode[pc]?).any fun raw =>
              let closed := { method0Closed with code := [raw] }
              match raw.operand with
              | .call site =>
                let vector := TypeExpr.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
                  (.atom runtimeScope "System.Byte")
                let narrow := { site.method with
                  owner := .atom intrinsicsScope "System.Runtime.Intrinsics.Vector128", returnType := vector }
                let emitted := { method0 with code := [.call narrow {}], links := [] }
                runtimeModel environment .call narrow == some (.memory (.marshalRead (.snapshot .vector128) false)) &&
                  !(decide (RuntimeModelsAgree closed [true] emitted))
              | _ => false) = true := by cil_kernel_rfl
        #print axioms shuffle_rejects_narrow_read
        end Extracted

        """);
}

// The fixture's declaration fixes the expected operation independently of the extractor.
static string? VectorModel(MethodReference call)
{
    if (call.DeclaringType.Namespace != "System.Runtime.Intrinsics") return null;
    int width = call.DeclaringType.Name switch
    {
        "Vector128" or "Vector128`1" => 128, "Vector256" or "Vector256`1" => 256,
        "Vector512" or "Vector512`1" => 512, _ => 0
    };
    if (width == 0) return null;
    var count = call.Parameters.Count;
    var hasOffset = call.Parameters.LastOrDefault()?.ParameterType.MetadataType == MetadataType.UIntPtr;
    var offset = hasOffset ? "true" : "false";
    return call.Name switch
    {
        "op_Equality" => $".intrinsic (.vector (.equalsAll {width})) 2",
        "LoadUnsafe" => $".memory (.vector128Unsafe false {offset})",
        "StoreUnsafe" => $".memory (.vector128Unsafe true {offset})",
        "Create" when width == 512 => ".intrinsic (.vector .combine256) 2",
        "Create" when call is GenericInstanceMethod => $".memory (.marshalRead (.snapshot .vector{width}) false)",
        "Create" when call.Parameters[0].ParameterType.MetadataType == MetadataType.UInt32 =>
            $".intrinsic (.vector (.create32 {width})) {count}",
        "Create" => $".intrinsic (.vector (.create64 {width})) {count}",
        _ => null
    };
}

// Forged evidence cannot change the table select or the lane reversal.
RejectHardware("SignWindow", "SignWindow", "::PermuteVar4x64x2(", "ternaryLogic", "permute");
RejectHardware("ReverseLimbs", "ReverseLimbs", "::ReverseElement8(", "shuffle256", "reverse");

// PMULUDQ runs on the host CPU and its x64-sse42 extraction must return the same products.
// Lanes with set high halves and both 32-bit extremes come first, then seeded random words.
const int MultiplyCases = 12;
var multiplyRandom = new Random(0x4d55);
ulong MultiplyWord()
{
    var bytes = new byte[sizeof(ulong)];
    multiplyRandom.NextBytes(bytes);
    return BitConverter.ToUInt64(bytes);
}
var multiplyInputs = new List<ulong[]>
{
    new[] { 0xFFFFFFFF_FFFFFFFFUL, 0x00000003_00000002UL, 0x00000005_FFFFFFFFUL, 0x00000007_00000004UL },
    new[] { 0x80000000_7FFFFFFFUL, 0xFFFFFFFF_80000000UL, 0x00000001_80000000UL, 0x12345678_FFFFFFFFUL }
};
while (multiplyInputs.Count < MultiplyCases)
{
    multiplyInputs.Add(Enumerable.Range(0, 4).Select(_ => MultiplyWord()).ToArray());
}
var multiplyEven = runtime.GetMethod("MultiplyEven128")!;
var multiplyObserved = multiplyInputs.Select(input =>
{
    var bytes = new byte[16];
    ((Vector128<ulong>)multiplyEven.Invoke(null, input.Cast<object>().ToArray())!).AsByte().CopyTo(bytes);
    return bytes;
}).ToArray();
// The cases must separate the model from odd 32-bit lanes, a signed product and a full 64-bit product.
foreach ((string mutant, Func<ulong, ulong, ulong> product) in new (string, Func<ulong, ulong, ulong>)[]
{
    ("odd lanes", (left, right) => (left >> 32) * (right >> 32)),
    ("signed product", (left, right) => (ulong)((long)(int)left * (int)right)),
    ("full product", (left, right) => left * right)
})
{
    var agrees = multiplyInputs.Select((input, index) =>
        new[] { product(input[0], input[2]), product(input[1], input[3]) }
            .SelectMany(BitConverter.GetBytes).SequenceEqual(multiplyObserved[index]));
    if (agrees.All(same => same))
    {
        throw new InvalidOperationException($"Multiply inputs do not reject the {mutant} mutant");
    }
}
var multiplyClaims = multiplyInputs.Select((input, index) => Invocation(
    input.Select(word => $".scalar (.i64 {word})"), $".v128 {VectorBits(multiplyObserved[index])}")).ToArray();
var multiplyOutput = Path.Combine(root, "MultiplyEven128");
Directory.CreateDirectory(multiplyOutput);
var multiplyProof = Path.Combine(multiplyOutput, "Proof.lean");
File.WriteAllText(multiplyProof, $$"""
    import Extracted
    import CIL.Safety.Execution
    namespace ExampleProof
    /-- Successful observations identify the successful checked execution result. -/
    private theorem result_of_toOption {error value : Type} {result : Except error value}
        {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
      cases result <;> simp_all [Except.toOption]
    #print axioms result_of_toOption
    /-- The host CPU's even-lane products on the same arguments. -/
    theorem correctness :
        {{string.Join(" ∧\n    ", multiplyClaims)}} := by
      exact {{Conjunction(multiplyClaims.Select(_ => "by apply result_of_toOption; decide +kernel"))}}
    #print axioms correctness
    end ExampleProof
    """);
pending.Add((new(selectors["MultiplyEven128"], multiplyProof, multiplyOutput), "x64-sse42",
    () => Console.WriteLine($"PASS MultiplyEven128 matches the host CPU on {multiplyClaims.Length} inputs")));
Flush();
// Shift each input's odd UInt32 element into the even position before the original SSE2 multiply.
var oddProducts = Path.Combine(root, "OddProducts128");
Directory.CreateDirectory(oddProducts);
var oddProductsAssembly = Path.Combine(oddProducts, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var method = variant.GetType("Examples.DivisionIntrinsics").Methods
        .Single(method => method.Name == "MultiplyEven128");
    var loads = method.Body.Instructions.Where(site =>
        site.OpCode.Code is Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or Code.Ldarg_3).ToArray();
    Code[] expected = [Code.Ldarg_0, Code.Ldarg_1, Code.Ldarg_2, Code.Ldarg_3];
    if (!loads.Select(load => load.OpCode.Code).SequenceEqual(expected))
        throw new InvalidDataException("MultiplyEven128 must load the four words in lane order.");
    var il = method.Body.GetILProcessor();
    foreach (var load in loads)
    {
        var count = il.Create(OpCodes.Ldc_I4_S, (sbyte)32);
        il.InsertAfter(load, count);
        il.InsertAfter(count, il.Create(OpCodes.Shr_Un));
    }
    variant.Write(oddProductsAssembly);
}
if (Sse2.IsSupported)
{
    var changedType = Assembly.LoadFile(oddProductsAssembly).GetType("Examples.DivisionIntrinsics")!;
    static Vector128<ulong> Products(Type type) => type.GetMethod("MultiplyEven128")!
        .CreateDelegate<Func<ulong, ulong, ulong, ulong, Vector128<ulong>>>()
        (0x100000002, 0x300000004, 0x500000006, 0x700000008);
    if (!Products(runtime).Equals(Vector128.Create(12UL, 32UL)) ||
        !Products(changedType).Equals(Vector128.Create(5UL, 21UL)))
        throw new InvalidOperationException("SSE2 products differ from the unsigned low- and high-half witness.");
}
verification.VerifyContractVariant(assembly, "Examples", selectors["MultiplyEven128"],
    Path.Combine(root, "EvenProductsContract"), oddProductsAssembly, selectors["MultiplyEven128"], oddProducts, """
    open CIL.Vector (pack128 sseMultiplyEven32_pack128)

    /-- Each unsigned 32-bit operand comes from the low half of its 64-bit lane. -/
    private def product (left right : W64) : W64 :=
      (left.setWidth 32).zeroExtend 64 * (right.setWidth 32).zeroExtend 64

    /-- PMULUDQ returns two full-width products and preserves caller memory. -/
    def evenProducts : MethodContract ((W64 × W64) × (W64 × W64)) (BitVec 128) where
      args input := [.scalar (.i64 input.1.1), .scalar (.i64 input.1.2),
        .scalar (.i64 input.2.1), .scalar (.i64 input.2.2)]
      results value := [.scalar (.v128 value)]
      pre _ _ := True
      footprint _ := []
      post input before after value := after = before ∧
        value = pack128 (product input.1.1 input.2.1) (product input.1.2 input.2.2)
    """, """
    set_option maxRecDepth 8192 in
    /-- The compiled SSE2 method multiplies the low halves for all four arguments. -/
    theorem correctness : evenProducts.Holds Extracted.program 0 := by
      rintro ⟨⟨a, b⟩, c, d⟩ memory -
      apply MethodContract.Holds.intro (c := evenProducts) (input := ((a, b), (c, d))) memory
        (pack128 (product a c) (product b d)) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
      refine ⟨64, ?_⟩
      change invoke Extracted.program 64 0 _ memory =
        .ok (memory, [.scalar (.v128 (pack128 (product a c) (product b d)))])
      unfold product
      rw [← sseMultiplyEven32_pack128]
      rfl
    """, """
    set_option maxRecDepth 8192
    /-- Each high half and its low half contribute different products at this input. -/
    private def witness : (W64 × W64) × (W64 × W64) :=
      ((0x100000002, 0x300000004), (0x500000006, 0x700000008))

    /-- The observed high-half products violate the low-half postcondition. -/
    private theorem wrongProducts :
        ¬ evenProducts.Returns witness Memory.empty Memory.empty [.scalar (.v128 (pack128 5 21))] := by
      rintro ⟨value, encoded, -, rfl⟩
      exact (by decide : ¬ ([CIL.Safety.Value.scalar (.v128 (pack128 5 21))] =
        [.scalar (.v128 (pack128 12 32))])) encoded

    #print axioms wrongProducts

    /-- Selecting the odd UInt32 elements instead returns the two high-half products. -/
    theorem correctness : evenProducts.Refuted Extracted.program 0 := by
      have ran : invoke Extracted.program 64 0 (evenProducts.args witness) Memory.empty =
          .ok (Memory.empty, [.scalar (.v128 (pack128 5 21))]) := by
        simp only [evenProducts, witness]
        cil_checked_steps [] <;> rfl
      exact MethodContract.Refuted.of_return (c := evenProducts) (input := witness)
        (program := Extracted.program) (fuel := 64) (method := 0) (final := Memory.empty)
        (values := [.scalar (.v128 (pack128 5 21))]) trivial ran (fun h => wrongProducts h.2)
    """, profile: "x64-sse42", imports: "import CIL.SIMD.PackedLanes");
Console.WriteLine("PASS SSE2 even-lane product contract and certified odd-lane replacement");
// Without SSE2 the reachable call is rejected before any evidence is written.
var multiplyRejectedOutput = Path.Combine(root, "MultiplyEven128-scalar");
Directory.CreateDirectory(multiplyRejectedOutput);
File.Delete(Path.Combine(multiplyRejectedOutput, "Extracted.lean"));
var rejectedMultiply = Execute(
    Extract("extract", assembly, "Examples", selectors["MultiplyEven128"], multiplyRejectedOutput, "scalar"));
if (rejectedMultiply.Code == 0 || File.Exists(Path.Combine(multiplyRejectedOutput, "Extracted.lean")) ||
    !rejectedMultiply.Output.Contains("Reachable intrinsic lacks Sse2", StringComparison.Ordinal))
{
    throw new InvalidOperationException($"MultiplyEven128 admitted without Sse2: {rejectedMultiply.Output}");
}
Console.WriteLine("PASS MultiplyEven128 rejected under scalar");
// Forged evidence must not substitute the 256-bit multiply or another exact SSE call for PMULUDQ.
RejectHardware("MultiplyEven128", "MultiplyEven128", "Sse2::Multiply(", "multiplyEven32", "wide");
RejectHardware("MultiplyEven128", "MultiplyEven128", "Sse2::Multiply(", "shuffle128", "shuffle");
BuildLeanTestLibraries("Checking replacement hardware method signatures", "+Tests.Support.IntrinsicMethods");
rejectedHardware.Check(FixtureLeanPath());

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
