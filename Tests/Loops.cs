#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Buffers.Binary;
using System.Reflection.PortableExecutable;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Loops");
Directory.CreateDirectory(root);
var contract = At("Examples/Proofs/Countdown.lean");
var correct = Path.Combine(root, "Countdown");
verification.Verify(assembly, "Examples", "Loops::Countdown(uint)", contract, correct);
verification.Verify(assembly, "Examples", "Loops::Countdown(uint)", contract, correct, check: true);
Console.WriteLine("PASS universal countdown termination and zero result, including 0 and UInt32.MaxValue");

// Recompile equivalent control flow without changing a character of the universal proof.
foreach (var variant in new[] { "Nops", "Reordered", "Stuttering" })
{
    var output = Path.Combine(root, variant);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Loops").Methods.Single(method => method.Name == "Countdown");
        var il = method.Body.GetILProcessor();
        var original = method.Body.Instructions.ToArray();
        if (variant == "Nops")
        {
            foreach (var instruction in original) il.InsertBefore(instruction, Instruction.Create(OpCodes.Nop));
        }
        else if (variant == "Reordered")
        {
            var entryJump = original.First(instruction => instruction.OpCode.FlowControl == FlowControl.Branch);
            var condition = original.Single(instruction => instruction.OpCode.FlowControl == FlowControl.Cond_Branch);
            var header = (Instruction)entryJump.Operand;
            var body = (Instruction)condition.Operand;
            var exit = original[Array.IndexOf(original, condition) + 1];
            var entryInstructions = original.Take(Array.IndexOf(original, entryJump) + 1).ToArray();
            var bodyInstructions = original[Array.IndexOf(original, body)..Array.IndexOf(original, header)];
            var conditionInstructions = original[Array.IndexOf(original, header)..(Array.IndexOf(original, condition) + 1)];
            var exitInstructions = original[Array.IndexOf(original, exit)..];
            method.Body.Instructions.Clear();
            foreach (var instruction in entryInstructions.Concat(exitInstructions).Concat(conditionInstructions))
                il.Append(instruction);
            il.Append(Instruction.Create(OpCodes.Br, exit));
            foreach (var instruction in bodyInstructions) il.Append(instruction);
            il.Append(Instruction.Create(OpCodes.Br, header));
        }
        else
        {
            // Still valid cyclic CIL, but a nonzero counter never decreases.
            original.Single(instruction => instruction.OpCode == OpCodes.Ldc_I4_1).OpCode = OpCodes.Ldc_I4_0;
        }
        module.Write(dll);
    }
    Run(Extract("extract", dll, "Examples", "Loops::Countdown(uint)", output));
    if (variant == "Stuttering")
    {
        var refused = false;
        try { verification.Verify(dll, "Examples", "Loops::Countdown(uint)", contract, output, existingArtifacts: true); }
        catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
        {
            refused = true;
        }
        if (!refused || File.Exists(Path.Combine(output, "verified.json")))
            throw new InvalidOperationException("Nondecreasing loop satisfied the termination contract");
        Console.WriteLine("PASS unchanged universal contract rejects nondecreasing loop");
    }
    else
    {
        var actual = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Loops")!.GetMethod("Countdown")!;
        foreach (var input in new uint[] { 0, 1, 7 })
            if ((uint)actual.Invoke(null, [input])! != 0)
                throw new InvalidOperationException("Equivalent-loop fixture changed the result: " + variant);
        verification.Verify(dll, "Examples", "Loops::Countdown(uint)", contract, output, existingArtifacts: true);
        Console.WriteLine($"PASS unchanged universal contract after {variant}");
    }
}

void Prove(string dll, string selector, string name, string source)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nimport CIL.Safety.StepComposition\n" +
        "set_option maxRecDepth 16384\nset_option maxHeartbeats 2000000\nnamespace ExampleProof\n" + source + "\nend ExampleProof\n");
    verification.Verify(dll, "Examples", selector, proof, output);
}

Prove(assembly, "Loops::Countdown(uint)", "Boundaries", """
theorem correctness :
    CIL.Safety.invoke Extracted.program 6 0 [.scalar (.i32 0)] Examples.empty =
      .error ⟨0, 10, .fuelExhausted⟩ ∧
    Extracted.method0.code[5]? = some .sub ∧
    CIL.Safety.step Extracted.method0 .sub 5 [] ⟨0, [], [], []⟩
      [.scalar (.i32 1), .scalar (.i32 4294967295)] Examples.empty =
      .ok (.next 6 [.scalar (.i32 4294967294)] ⟨0, [], [], []⟩ Examples.empty) := ⟨rfl, rfl, rfl⟩
""");
Console.WriteLine("PASS insufficient fuel and maximum unsigned decrement boundary");

// Actual .NET execution supplies independent expected values. Large counter inputs
// are covered by induction in the universal proof, not billions of runtime steps.
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Loops")!;
foreach (var name in new[] { "Countdown", "WrongCountdown" })
{
    var method = runtime.GetMethod(name)!;
    uint[] inputs = [0, 1, 2, 3, 7, 16];
    var claims = inputs.Select(value =>
        $"(CIL.Safety.invoke Extracted.program {16 + 8 * value} 0 [.scalar (.i32 {value})] Examples.empty).map Prod.snd = .ok [.scalar (.i32 {method.Invoke(null, [value])})]");
    Prove(assembly, $"Loops::{name}(uint)", name + "Runtime",
        "theorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", inputs.Select(_ => "rfl")) + "⟩");
    Console.WriteLine($"PASS {name}: {inputs.Length} runtime comparisons");
}

// A profile-fixed false feature remains false even across a backedge. The array
// operation is unreachable under scalar, and must be rejected under AVX2.
Prove(assembly, "Loops::FeatureCountdown(uint)", "FeatureLoop",
    "theorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i32 3)] Examples.empty).map Prod.snd = .ok [.scalar (.i32 0)] := rfl");
var feature = Execute(Extract("extract", assembly, "Examples", "Loops::FeatureCountdown(uint)", Path.Combine(root, "FeatureReject"), "x64-avx2"));
if (feature.Code == 0 || !feature.Output.Contains("Unsupported instruction"))
    throw new InvalidOperationException("Feature loop failed to reject reachable array: " + feature.Output);
Console.WriteLine("PASS fixed feature selection inside a loop");

var wrong = Path.Combine(root, "WrongContract");
Directory.CreateDirectory(wrong);
File.Copy(Path.Combine(correct, "verified.json"), Path.Combine(wrong, "verified.json"), overwrite: true);
bool rejected = false;
try
{
    verification.Verify(assembly, "Examples", "Loops::WrongCountdown(uint)", contract, wrong);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}
if (!rejected || File.Exists(Path.Combine(wrong, "verified.json")))
    throw new InvalidOperationException("Incorrect countdown passed or retained a verification report");
Console.WriteLine("PASS unchanged universal contract rejects incorrect loop");

string Fixture(string name, Action<ModuleDefinition, MethodDefinition> populate)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    var method = module.GetType("Examples.Loops").Methods.Single(m => m.Name == "Countdown");
    method.Body = new Mono.Cecil.Cil.MethodBody(method) { InitLocals = true };
    populate(module, method);
    module.Write(dll);
    return dll;
}

// A well-formed infinite loop is extractable. Every fuel budget fails; admitting
// the CFG does not establish termination, even when a finite test budget is large.
var infinite = Fixture("Infinite", (_, method) =>
{
    var branch = Instruction.Create(OpCodes.Nop);
    branch.OpCode = OpCodes.Br;
    branch.Operand = branch;
    method.Body.Instructions.Add(branch);
});
Prove(infinite, "Loops::Countdown(uint)", "InfiniteProof", """
theorem exhausted (fuel : Nat) (args : List CIL.Safety.Value)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    CIL.Safety.run Extracted.program fuel 0 0 args frame [] memory =
      .error ⟨0, 0, .fuelExhausted⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [CIL.Safety.run_next Extracted.lookup0 Extracted.method0_instruction0 (show
      CIL.Safety.step Extracted.method0 (.branch 0) 0 args frame [] memory =
        .ok (.next 0 [] frame memory) from rfl)]
    exact ih
theorem correctness (fuel : Nat) (x : CIL.W32) :
    CIL.Safety.invoke Extracted.program fuel 0 [.scalar (.i32 x)] Examples.empty =
      .error ⟨0, 0, .fuelExhausted⟩ := by
  exact exhausted fuel _ _ _
""");
Console.WriteLine("PASS infinite loop exhausts every fuel budget");

// Backward switch edges preserve runtime dispatch: zero cycles, nonzero returns.
var backwardSwitch = Fixture("BackwardSwitch", (_, method) =>
{
    var code = method.Body.Instructions;
    var start = Instruction.Create(OpCodes.Ldarg_0);
    code.Add(start);
    code.Add(Instruction.Create(OpCodes.Switch, new[] { start }));
    code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
    code.Add(Instruction.Create(OpCodes.Ret));
});
Prove(backwardSwitch, "Loops::Countdown(uint)", "BackwardSwitchProof", """
theorem correctness :
    CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i32 0)] Examples.empty =
      .error ⟨0, 0, .fuelExhausted⟩ ∧
    (CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i32 1)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i32 0)] := ⟨rfl, rfl⟩
""");
Console.WriteLine("PASS backward switch dispatch and fuel exhaustion");

// Entry jumps over the body to the condition. The backedge must visit and type
// the earlier body, including mixed native/int32 arithmetic. Unsigned comparisons
// require an explicit native-width bound, independent of JIT constant provenance.
string NativeLoop(string name, bool convertBound) => Fixture(name, (_, method) =>
{
    var code = method.Body.Instructions;
    var body = Instruction.Create(OpCodes.Ldc_I4_1);
    var condition = Instruction.Create(OpCodes.Dup);
    code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
    code.Add(Instruction.Create(OpCodes.Conv_U));
    code.Add(Instruction.Create(OpCodes.Br, condition));
    code.Add(body);
    code.Add(Instruction.Create(OpCodes.Add));
    code.Add(condition);
    code.Add(Instruction.Create(OpCodes.Ldc_I4_3));
    if (convertBound) code.Add(Instruction.Create(OpCodes.Conv_U));
    code.Add(Instruction.Create(OpCodes.Blt_Un, body));
    code.Add(Instruction.Create(OpCodes.Conv_U4));
    code.Add(Instruction.Create(OpCodes.Ret));
});
var native = NativeLoop("NativeLoop", convertBound: true);
var nativeRuntime = Assembly.Load(File.ReadAllBytes(native)).GetType("Examples.Loops")!.GetMethod("Countdown")!;
if ((uint)nativeRuntime.Invoke(null, [0u])! != 3u)
    throw new InvalidOperationException("Explicitly widened native loop changed its runtime result");
Prove(native, "Loops::Countdown(uint)", "NativeLoopProof", """
theorem correctness : (CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i32 0)] Examples.empty).map Prod.snd =
    .ok [.scalar (.i32 3)] := rfl
""");
Console.WriteLine("PASS native stack typing through backward-reachable body");

var ambiguousNative = NativeLoop("NativeLoopAmbiguous", convertBound: false);
var ambiguousOutput = Path.Combine(root, "NativeLoopAmbiguous", "Extracted");
var ambiguousResult = Execute(Extract("extract", ambiguousNative, "Examples", "Loops::Countdown(uint)", ambiguousOutput));
if (ambiguousResult.Code == 0 ||
    !ambiguousResult.Output.Contains("Unsupported mixed native/int32 unsigned branch; insert explicit conv.i or conv.u") ||
    File.Exists(Path.Combine(ambiguousOutput, "Extracted.lean")))
    throw new InvalidOperationException("Unconverted native loop was not rejected: " + ambiguousResult.Output);
Console.WriteLine("PASS unconverted mixed unsigned loop comparison rejected");

foreach (var mutation in new[] { "stack-height", "stack-type", "local-fact", "stack-fact", "recursive-call", "fallthrough", "bad-target", "middle-target" })
{
    var dll = Fixture("Reject-" + mutation, (module, method) =>
    {
        var code = method.Body.Instructions;
        if (mutation == "stack-height")
        {
            var start = Instruction.Create(OpCodes.Ldc_I4_0);
            code.Add(start);
            code.Add(Instruction.Create(OpCodes.Br, start));
        }
        else if (mutation == "stack-type")
        {
            var header = Instruction.Create(OpCodes.Pop);
            code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            code.Add(Instruction.Create(OpCodes.Br, header));
            code.Add(header);
            code.Add(Instruction.Create(OpCodes.Ldc_I8, 0L));
            code.Add(Instruction.Create(OpCodes.Br, header));
        }
        else if (mutation is "local-fact" or "stack-fact")
        {
            // First iteration skips the array. A backedge changes zero to one;
            // a single forward pass would incorrectly prune the unsupported arm.
            method.Body.Variables.Add(new VariableDefinition(module.TypeSystem.Int32));
            bool local = mutation == "local-fact";
            var header = Instruction.Create(local ? OpCodes.Ldloc_0 : OpCodes.Dup);
            var unsupported = Instruction.Create(OpCodes.Ldc_I4_0);
            code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            if (local) code.Add(Instruction.Create(OpCodes.Stloc_0));
            code.Add(header);
            code.Add(Instruction.Create(OpCodes.Brtrue, unsupported));
            if (!local) code.Add(Instruction.Create(OpCodes.Pop));
            code.Add(Instruction.Create(OpCodes.Ldc_I4_1));
            if (local) code.Add(Instruction.Create(OpCodes.Stloc_0));
            code.Add(Instruction.Create(OpCodes.Br, header));
            code.Add(unsupported);
            code.Add(Instruction.Create(OpCodes.Newarr, module.TypeSystem.Int32));
            code.Add(Instruction.Create(OpCodes.Pop));
            if (!local) code.Add(Instruction.Create(OpCodes.Pop));
            code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            code.Add(Instruction.Create(OpCodes.Ret));
        }
        else if (mutation == "recursive-call")
        {
            code.Add(Instruction.Create(OpCodes.Ldarg_0));
            code.Add(Instruction.Create(OpCodes.Call, method));
            code.Add(Instruction.Create(OpCodes.Ret));
        }
        else if (mutation is "bad-target" or "middle-target")
        {
            var start = Instruction.Create(OpCodes.Nop);
            start.OpCode = OpCodes.Br;
            start.Operand = start;
            code.Add(start);
        }
        else code.Add(Instruction.Create(OpCodes.Nop));
    });
    if (mutation is "bad-target" or "middle-target")
    {
        var bytes = File.ReadAllBytes(dll);
        using var module = ModuleDefinition.ReadModule(new MemoryStream(bytes));
        var method = module.GetType("Examples.Loops").Methods.Single(m => m.Name == "Countdown");
        using var pe = new PEReader(new MemoryStream(bytes));
        var section = pe.PEHeaders.SectionHeaders.Single(s => method.RVA >= s.VirtualAddress && method.RVA < s.VirtualAddress + s.SizeOfRawData);
        var body = section.PointerToRawData + method.RVA - section.VirtualAddress;
        var header = (bytes[body] & 3) == 2 ? 1 : (BinaryPrimitives.ReadUInt16LittleEndian(bytes.AsSpan(body)) >> 12) * 4;
        BinaryPrimitives.WriteInt32LittleEndian(bytes.AsSpan(body + header + 1), mutation == "bad-target" ? int.MaxValue : -3);
        File.WriteAllBytes(dll, bytes);
    }
    var output = Path.Combine(root, "Reject-" + mutation, "Extracted");
    var result = Execute(Extract("extract", dll, "Examples", "Loops::Countdown(uint)", output));
    var marker = mutation switch
    {
        "stack-height" => "Inconsistent evaluation stack",
        "stack-type" => "Incompatible native stack types",
        "recursive-call" => "Recursive managed dependency",
        "fallthrough" => "Control falls off method",
        "bad-target" or "middle-target" => "Malformed control-flow target",
        _ => "Unsupported instruction"
    };
    if (result.Code == 0 || !result.Output.Contains(marker) || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Incorrect loop rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
