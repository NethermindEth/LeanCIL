#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Buffers.Binary;
using System.Reflection.PortableExecutable;
using System.Text.RegularExpressions;
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

// A loop that calls a helper is proved from the helper's contract alone. Reimplementing the
// helper re-proves only that contract; the loop proof is reused byte for byte.
const string CountCalls = "Loops::CountCalls(uint)";
var countProof = File.ReadAllText(At("Examples/Proofs/CountCalls.lean"));
var helperStart = countProof.IndexOf("theorem decrement_holds", StringComparison.Ordinal);
var helperEnd = helperStart < 0 ? -1 : countProof.IndexOf("bind_entry entry", helperStart, StringComparison.Ordinal);
var loopStart = countProof.IndexOf("theorem terminates", StringComparison.Ordinal);
if (helperEnd < 0 || loopStart < helperEnd)
    throw new InvalidDataException("Examples/Proofs/CountCalls.lean has no helper section before its loop proof");
var loopLine = countProof[..loopStart].Count(c => c == '\n') + 1;
verification.Verify(assembly, "Examples", CountCalls, At("Examples/Proofs/CountCalls.lean"), Path.Combine(root, "CountCalls"));
Console.WriteLine("PASS counted loop returns its iteration count for every uint through the helper contract");

// A struct local's fields are read and stored as named values, and the call crossed by its
// contract, with no step facts passed to the loop tactics.
verification.Verify(assembly, "Examples", "Loops::TallyTwice(uint)", At("Examples/Proofs/TallyTwice.lean"),
    Path.Combine(root, "TallyTwice"));
Console.WriteLine("PASS struct-local loop doubles every uint through the helper contract");

var tally = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Loops")!.GetMethod("TallyTwice")!
    .CreateDelegate<Func<uint, uint>>();
foreach (var value in new uint[] { 0, 1, 7, 1000 })
    if (tally(value) != unchecked(2 * value))
        throw new InvalidOperationException($"TallyTwice({value}) returned {tally(value)}, not {unchecked(2 * value)}");
Console.WriteLine("PASS struct-local loop runtime comparisons return twice the input");

// A helper that adds three and a return of the count field each break the doubling claim.
foreach (var (name, mutate) in new (string, Action<TypeDefinition>)[]
{
    ("TallyTwiceAddsThree", type => type.Methods.Single(m => m.Name == "AddTwo").Body.Instructions
        .Single(i => i.OpCode == OpCodes.Ldc_I4_2).OpCode = OpCodes.Ldc_I4_3),
    ("TallyTwiceReturnsCount", type =>
    {
        var body = type.Methods.Single(m => m.Name == "TallyTwice").Body.Instructions;
        var load = body.Last(i => i.OpCode == OpCodes.Ldfld);
        if (((FieldReference)load.Operand).Name != "Sum")
            throw new InvalidDataException("TallyTwice no longer returns its Sum field last");
        load.Operand = ((FieldReference)load.Operand).DeclaringType.Resolve().Fields.Single(f => f.Name == "Count");
    })
})
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        mutate(module.GetType("Examples.Loops"));
        module.Write(dll);
    }
    Run(Extract("extract", dll, "Examples", "Loops::TallyTwice(uint)", output));
    var refused = false;
    try
    {
        verification.Verify(dll, "Examples", "Loops::TallyTwice(uint)", At("Examples/Proofs/TallyTwice.lean"), output,
            existingArtifacts: true);
    }
    catch (InvalidOperationException error)
        when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
    {
        refused = true;
    }
    if (!refused || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException($"{name} satisfied the struct-local loop proof");
    Console.WriteLine($"PASS unchanged struct-local loop proof rejects {name}");
}

// A loop over a struct with a bool field that writes caller memory through a helper and stops early.
const string CopyUntilZero = "Loops::CopyUntilZero(System.ReadOnlySpan`1<System.UInt32>,uint&)";
var copyProof = At("Examples/Proofs/CopyUntilZero.lean");
verification.Verify(assembly, "Examples", CopyUntilZero, copyProof, Path.Combine(root, "CopyUntilZero"));
Console.WriteLine("PASS early-exit struct loop copies up to the first zero through the ref-writing helper's contract");

var copyUntilZero = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Loops")!.GetMethod("CopyUntilZero")!
    .CreateDelegate<CopyUntilZeroDelegate>();
const uint StoppedBit = 0x80000000u;
const uint Untouched = 0xDEADBEEFu;
foreach (uint[] values in new uint[][] { [], [1, 2, 3], [5, 0, 7], [0], [9, uint.MaxValue, 0] })
{
    var zero = Array.IndexOf(values, 0u);
    var stopped = zero >= 0;
    var copied = stopped ? zero : values.Length;
    var expected = stopped ? (uint)copied | StoppedBit : (uint)copied;
    var output = new uint[values.Length + 1];
    Array.Fill(output, Untouched);
    var result = copyUntilZero(values, ref output[0]);
    var wrongWords = !output[..copied].SequenceEqual(values[..copied])
        || output[copied..].Any(word => word != Untouched);
    if (result != expected || wrongWords)
        throw new InvalidOperationException(
            $"CopyUntilZero([{string.Join(", ", values)}]) returned {result:X} with [{string.Join(", ", output)}]");
}
Console.WriteLine("PASS early-exit struct loop runtime comparisons copy up to the first zero and flag the stop");

// A helper that stamps zero and a loop that copies past a zero each break the copy claim.
foreach (var (name, mutate) in new (string, Action<TypeDefinition>)[]
{
    ("CopyUntilZeroStampsZero", type => type.Methods.Single(m => m.Name == "Stamp").Body.Instructions
        .Single(i => i.OpCode == OpCodes.Ldarg_1).OpCode = OpCodes.Ldc_I4_0),
    ("CopyUntilZeroIgnoresZero", type =>
    {
        var test = type.Methods.Single(m => m.Name == "CopyUntilZero").Body.Instructions
            .First(i => i.OpCode == OpCodes.Brtrue || i.OpCode == OpCodes.Brtrue_S);
        test.OpCode = test.OpCode == OpCodes.Brtrue ? OpCodes.Br : OpCodes.Br_S;
        // The tested word is still loaded; an unconditional branch must not leave it on the stack.
        test.Previous.OpCode = OpCodes.Nop;
    })
})
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        mutate(module.GetType("Examples.Loops"));
        module.Write(dll);
    }
    Run(Extract("extract", dll, "Examples", CopyUntilZero, output));
    var refused = false;
    try { verification.Verify(dll, "Examples", CopyUntilZero, copyProof, output, existingArtifacts: true); }
    catch (InvalidOperationException error)
        when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
    {
        refused = true;
    }
    if (!refused || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException($"{name} satisfied the early-exit copy proof");
    Console.WriteLine($"PASS unchanged early-exit copy proof rejects {name}");
}

string CountVariant(string name, Action<MethodDefinition, MethodDefinition> mutate)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = module.GetType("Examples.Loops");
        mutate(type.Methods.Single(m => m.Name == "CountCalls"), type.Methods.Single(m => m.Name == "Decrement"));
        module.Write(dll);
    }
    Run(Extract("extract", dll, "Examples", CountCalls, output));
    return dll;
}

uint Invoke(string dll, string name, uint input) =>
    (uint)Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Loops")!.GetMethod(name)!.Invoke(null, [input])!;

var replacedCount = CountVariant("CountCallsReplaced", (_, helper) =>
{
    var il = helper.Body.GetILProcessor();
    helper.Body.Instructions.Clear();
    il.Append(Instruction.Create(OpCodes.Ldarg_0));
    il.Append(Instruction.Create(OpCodes.Ldc_I4_M1));
    il.Append(Instruction.Create(OpCodes.Add));
    il.Append(Instruction.Create(OpCodes.Ret));
});
if (Invoke(replacedCount, "Decrement", 0) != uint.MaxValue || Invoke(replacedCount, "CountCalls", 7) != 7)
    throw new InvalidOperationException("The reimplemented helper changed the runtime results");
const string ReplacedHelper = """
theorem decrement_holds : decrementContract.Holds Extracted.program decrement := by
  rintro x m -
  dsimp only [decrementContract]
  refine ⟨8, m, _, ?_, Confined.refl _ m, x + 4294967295#32, rfl, by bv_omega⟩
  cil_checked_steps


""";
var replacedProof = Path.Combine(root, "CountCallsReplaced", "CountCalls.lean");
File.WriteAllText(replacedProof, countProof[..helperStart] + ReplacedHelper + countProof[helperEnd..]);
verification.Verify(replacedCount, "Examples", CountCalls, replacedProof, Path.Combine(root, "CountCallsReplaced"), existingArtifacts: true);
Console.WriteLine("PASS unchanged loop proof after reimplementing the helper and re-proving only its contract");

// Both builds keep the helper, so the unchanged proof must fail inside the loop proof:
// a discarded helper result never decreases the measure; counting twice breaks the invariant.
foreach (var (name, opcode, replacement) in new[] { ("CountCallsDiscarded", OpCodes.Stloc_0, OpCodes.Pop), ("CountCallsOvercount", OpCodes.Ldc_I4_1, OpCodes.Ldc_I4_2) })
{
    var dll = CountVariant(name, (caller, _) => caller.Body.Instructions.Single(i => i.OpCode == opcode &&
        (opcode != OpCodes.Stloc_0 || i.Previous.OpCode == OpCodes.Call)).OpCode = replacement);
    if (name == "CountCallsOvercount" && Invoke(dll, "CountCalls", 3) != 6)
        throw new InvalidOperationException("The overcounting fixture did not change the result");
    var lines = RejectedLines(dll, At("Examples/Proofs/CountCalls.lean"), name, existingArtifacts: true);
    if (lines.Length == 0 || lines.Any(line => line < loopLine))
        throw new InvalidOperationException($"{name} was not rejected by the loop proof: lines {string.Join(", ", lines)}");
    Console.WriteLine($"PASS unchanged loop proof rejects {name}");
}

// On the correct build, the rule itself must refuse a nondecreasing measure and an invariant
// that holds at entry and exit but is not preserved, each at exactly that obligation.
int LineOf(string text) => countProof.IndexOf(text, StringComparison.Ordinal) is var at and >= 0
    ? countProof[..at].Count(c => c == '\n') + 1
    : throw new InvalidDataException("Examples/Proofs/CountCalls.lean has no line containing: " + text);
foreach (var (name, original, mutated, obligation) in new[]
{
    ("CountCallsCountMeasure", "(fun s => s.values.1.toNat)",
        "(fun s => s.values.2.toNat)", "show (x - 1).toNat < x.toNat"),
    ("CountCallsProductInvariant", "state.values.2 + state.values.1 = value",
        "state.values.2 + state.values.1 = value + state.values.2 * state.values.1",
        "show count + 1 + (x - 1) = value")
})
{
    if (countProof.Split(original).Length != 2) throw new InvalidDataException("Ambiguous proof mutation: " + original);
    Directory.CreateDirectory(Path.Combine(root, name));
    var proof = Path.Combine(root, name, "CountCalls.lean");
    File.WriteAllText(proof, countProof.Replace(original, mutated));
    var lines = RejectedLines(assembly, proof, name, existingArtifacts: false);
    if (lines.Length == 0 || lines.Any(line => line != LineOf(obligation)))
        throw new InvalidOperationException($"{name} was not rejected at line {LineOf(obligation)}: lines {string.Join(", ", lines)}");
    Console.WriteLine($"PASS loop rule rejects {name} at its obligation");
}

// A loop whose helper can throw is proved from the helper's outcome contract alone: every input
// returns its value, or raises the helper's exception after `limit` successful calls.
const string CountUntil = "Loops::CountUntil(uint,uint)";
var untilPath = At("Examples/Proofs/CountUntil.lean");
var untilProof = File.ReadAllText(untilPath);
var bumpStart = untilProof.IndexOf("theorem bump_holds", StringComparison.Ordinal);
var bumpEnd = bumpStart < 0 ? -1 : untilProof.IndexOf("/-- `CountUntil` raises exactly", bumpStart, StringComparison.Ordinal);
var untilLoopStart = untilProof.IndexOf("theorem outcome", StringComparison.Ordinal);
var contractStart = untilProof.IndexOf("def bumpContract", StringComparison.Ordinal);
if (contractStart < 0 || bumpStart < contractStart || bumpEnd < 0 || untilLoopStart < bumpEnd)
    throw new InvalidDataException("Examples/Proofs/CountUntil.lean has no helper section before its loop proof");
var untilLoopLine = untilProof[..untilLoopStart].Count(c => c == '\n') + 1;
verification.Verify(assembly, "Examples", CountUntil, untilPath, Path.Combine(root, "CountUntil"));
Console.WriteLine("PASS loop returns its input or propagates the helper exception for every pair of uints");

// Runtime throws are independent expected values: a raise after earlier calls, on the first call, and none.
object Outcome(string dll, string name, uint value, uint limit)
{
    try { return Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Loops")!.GetMethod(name)!.Invoke(null, [value, limit])!; }
    catch (TargetInvocationException error) { return error.InnerException!.GetType().FullName!; }
}
(uint Value, uint Limit)[] untilInputs = [(0, 0), (3, 7), (3, 3), (5, 2), (4, 0)];
var untilClaims = untilInputs.Select(input => (input, Outcome(assembly, "CountUntil", input.Value, input.Limit))).Select(pair =>
{
    var invocation = $"CIL.Safety.invoke Extracted.program {32 + 16 * pair.input.Value} 0 [.scalar (.i32 {pair.input.Value}), .scalar (.i32 {pair.input.Limit})] CIL.Safety.Memory.empty";
    return pair.Item2 is uint result
        ? $"({invocation}).map Prod.snd = .ok [.scalar (.i32 {result})]"
        : $"(match {invocation} with | .error fault => fault.fault | .ok _ => .invalidState) = .thrown \"{pair.Item2}\"";
}).ToArray();
if (untilClaims.Count(claim => claim.Contains("System.InvalidOperationException")) != 2)
    throw new InvalidOperationException("CountUntil fixture did not raise for exactly the two inputs above their limit");
Prove(assembly, CountUntil, "CountUntilRuntime",
    "theorem correctness :\n" + string.Join(" ∧\n", untilClaims) + " := by\n  exact ⟨" + string.Join(", ", untilClaims.Select(_ => "rfl")) + "⟩");
Console.WriteLine($"PASS CountUntil: {untilClaims.Length} runtime comparisons, including raises after earlier calls");

string UntilVariant(string name, Action<ModuleDefinition, MethodDefinition> mutate)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        mutate(module, module.GetType("Examples.Loops").Methods.Single(m => m.Name == "Bump"));
        module.Write(dll);
    }
    Run(Extract("extract", dll, "Examples", CountUntil, output));
    return dll;
}

// Testing inequality instead of equality and subtracting minus one keep the contract, so only the helper proof changes.
var replacedBump = UntilVariant("CountUntilReplaced", (_, helper) =>
{
    var ctor = helper.Body.Instructions.Single(i => i.OpCode == OpCodes.Newobj);
    var thrown = ctor.Next;
    var il = helper.Body.GetILProcessor();
    var normal = Instruction.Create(OpCodes.Ldarg_0);
    helper.Body.Instructions.Clear();
    il.Append(Instruction.Create(OpCodes.Ldarg_0));
    il.Append(Instruction.Create(OpCodes.Ldarg_1));
    il.Append(Instruction.Create(OpCodes.Bne_Un, normal));
    il.Append(ctor);
    il.Append(thrown);
    il.Append(normal);
    il.Append(Instruction.Create(OpCodes.Ldc_I4_M1));
    il.Append(Instruction.Create(OpCodes.Sub));
    il.Append(Instruction.Create(OpCodes.Ret));
});
foreach (var input in untilInputs)
    if (!Outcome(replacedBump, "CountUntil", input.Value, input.Limit).Equals(Outcome(assembly, "CountUntil", input.Value, input.Limit)))
        throw new InvalidOperationException("The reimplemented helper changed the runtime outcome");
const string ReplacedBump = """
theorem bump_holds : bumpContract.Holds Extracted.program bump := by
  rintro ⟨count, limit⟩ m -
  by_cases same : count = limit
  · subst same
    simp only [bumpContract, ite_true]
    cil_raise_steps []
  · simp only [bumpContract, same, ite_false]
    refine ⟨8, m, _, ?_, Confined.refl _ m, count - 4294967295#32, rfl, by bv_omega⟩
    cil_checked_steps [same]


""";
var replacedUntil = Path.Combine(root, "CountUntilReplaced", "CountUntil.lean");
File.WriteAllText(replacedUntil, untilProof[..bumpStart] + ReplacedBump + untilProof[bumpEnd..]);
verification.Verify(replacedBump, "Examples", CountUntil, replacedUntil, Path.Combine(root, "CountUntilReplaced"), existingArtifacts: true);
Console.WriteLine("PASS unchanged outcome loop proof after reimplementing the throwing helper");

int UntilLine(string text) => untilProof.IndexOf(text, StringComparison.Ordinal) is var at and >= 0 && untilProof.Split(text).Length == 2
    ? untilProof[..at].Count(c => c == '\n') + 1
    : throw new InvalidDataException("Examples/Proofs/CountUntil.lean has no unique line containing: " + text);
var exceptionalExit = UntilLine("case raises => simp only [bumpContract, ite_true]");

// A helper that throws another type, with its contract re-proved to say so, no longer
// establishes the loop's specified exception: the unchanged loop proof fails at that exit.
var otherException = UntilVariant("CountUntilOtherException", (module, helper) =>
{
    var ctor = helper.Body.Instructions.Single(i => i.OpCode == OpCodes.Newobj);
    var original = (MethodReference)ctor.Operand;
    var type = new TypeReference("System", "ArgumentException", module, original.DeclaringType.Scope);
    ctor.Operand = new MethodReference(".ctor", module.TypeSystem.Void, type) { HasThis = true };
});
if (!Outcome(otherException, "CountUntil", 5, 2).Equals("System.ArgumentException"))
    throw new InvalidOperationException("The other-exception fixture did not change the thrown type");
var helperContract = untilProof[contractStart..bumpStart];
if (helperContract.Split("\"System.InvalidOperationException\"").Length != 2)
    throw new InvalidDataException("Ambiguous helper contract mutation");
Directory.CreateDirectory(Path.Combine(root, "CountUntilOtherException"));
var otherProof = Path.Combine(root, "CountUntilOtherException", "CountUntil.lean");
File.WriteAllText(otherProof, untilProof[..contractStart] +
    helperContract.Replace("System.InvalidOperationException", "System.ArgumentException") + untilProof[bumpStart..]);
var otherLines = RejectedLines(otherException, otherProof, "CountUntilOtherException", existingArtifacts: true, CountUntil);
if (otherLines.Length == 0 || otherLines.Any(line => line != exceptionalExit))
    throw new InvalidOperationException($"CountUntilOtherException was not rejected at line {exceptionalExit}: lines {string.Join(", ", otherLines)}");
Console.WriteLine("PASS unchanged outcome loop proof rejects a helper that raises another exception");

// On the correct build, a nondecreasing measure, an invariant that holds at entry and both exits
// but is not preserved, and a different specified exception each fail at exactly that obligation.
foreach (var (name, original, mutated, obligation) in new[]
{
    ("CountUntilCountMeasure", "(fun s => s.values.1.toNat)",
        "(fun s => s.values.2.toNat)", "show (x - 1).toNat < x.toNat"),
    ("CountUntilLimitInvariant", "state.values.2.toNat ≤ limit.toNat\n",
        "state.values.2.toNat ≤ limit.toNat - state.values.1.toNat\n",
        "show (count + 1).toNat ≤ limit.toNat"),
    ("CountUntilWrongException", "then some \"System.InvalidOperationException\" else none\n\nbind_entry entry",
        "then some \"System.ArgumentException\" else none\n\nbind_entry entry",
        "case raises => simp only [bumpContract, ite_true]")
})
{
    if (untilProof.Split(original).Length != 2) throw new InvalidDataException("Ambiguous proof mutation: " + original);
    Directory.CreateDirectory(Path.Combine(root, name));
    var proof = Path.Combine(root, name, "CountUntil.lean");
    File.WriteAllText(proof, untilProof.Replace(original, mutated));
    var lines = RejectedLines(assembly, proof, name, existingArtifacts: false, CountUntil);
    if (lines.Length == 0 || lines.Any(line => line != UntilLine(obligation) || line < untilLoopLine))
        throw new InvalidOperationException($"{name} was not rejected at line {UntilLine(obligation)}: lines {string.Join(", ", lines)}");
    Console.WriteLine($"PASS outcome loop rule rejects {name} at its obligation");
}

int[] RejectedLines(string dll, string proof, string name, bool existingArtifacts, string selector = CountCalls)
{
    string? failure = null;
    try { verification.Verify(dll, "Examples", selector, proof, Path.Combine(root, name), existingArtifacts: existingArtifacts); }
    catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
    {
        failure = error.Message;
    }
    if (failure is null || File.Exists(Path.Combine(root, name, "verified.json")))
        throw new InvalidOperationException($"{name} passed verification");
    return Regex.Matches(failure, @"Proof\.lean:(\d+):\d+: error").Select(m => int.Parse(m.Groups[1].Value)).Distinct().ToArray();
}

void Prove(string dll, string selector, string name, string source)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nimport CIL.Safety.StepComposition\n" +
        "set_option maxRecDepth 16384\nset_option maxHeartbeats 2000000\nnamespace ExampleProof\n" + source + "\nend ExampleProof\n");
    verification.Verify(dll, "Examples", selector, proof, output);
}

Prove(assembly, "Loops::Countdown(uint)", "Boundaries", """
theorem correctness :
    CIL.Safety.invoke Extracted.program 6 0 [.scalar (.i32 0)] CIL.Safety.Memory.empty =
      .error ⟨0, 10, .fuelExhausted⟩ ∧
    Extracted.method0.code[5]? = some .sub ∧
    CIL.Safety.step Extracted.method0 .sub 5 [] ⟨0, [], [], [], 0⟩
      [.scalar (.i32 1), .scalar (.i32 4294967295)] CIL.Safety.Memory.empty =
      .ok (.next 6 [.scalar (.i32 4294967294)] ⟨0, [], [], [], 0⟩ CIL.Safety.Memory.empty) := ⟨rfl, rfl, rfl⟩
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
        $"(CIL.Safety.invoke Extracted.program {16 + 8 * value} 0 [.scalar (.i32 {value})] CIL.Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i32 {method.Invoke(null, [value])})]");
    Prove(assembly, $"Loops::{name}(uint)", name + "Runtime",
        "theorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", inputs.Select(_ => "rfl")) + "⟩");
    Console.WriteLine($"PASS {name}: {inputs.Length} runtime comparisons");
}

// A profile-fixed false feature remains false even across a backedge. The array
// operation is unreachable under scalar, and must be rejected under AVX2.
Prove(assembly, "Loops::FeatureCountdown(uint)", "FeatureLoop",
    "theorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i32 3)] CIL.Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i32 0)] := rfl");
var feature = Execute(Extract("extract", assembly, "Examples", "Loops::FeatureCountdown(uint)", Path.Combine(root, "FeatureReject"), "x64-v3"));
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

var constantMeasure = File.ReadAllText(contract).Replace("(fun s => s.values.toNat)", "(fun _ => 0)",
    StringComparison.Ordinal);
if (constantMeasure == File.ReadAllText(contract))
    throw new InvalidOperationException("Countdown measure mutation did not match");
var constantMeasureProof = Path.Combine(root, "CountdownConstantMeasure.lean");
File.WriteAllText(constantMeasureProof, constantMeasure);
RejectedLines(assembly, constantMeasureProof, "CountdownConstantMeasure", false, "Loops::Countdown(uint)");
Console.WriteLine("PASS generated loop continuation obligations reject a constant measure");

const string Drain = "Loops::Drain(System.ReadOnlySpan`1<System.Int32>)";
var drainProof = At("Examples/Proofs/SpanDrain.lean");
verification.Verify(assembly, "Examples", Drain, drainProof, Path.Combine(root, "SpanDrain"));
Console.WriteLine("PASS symbolic span entry, slicing loop, zero result and exact caller-memory preservation");

var stutteringSpan = Path.Combine(root, "SpanDrainStuttering");
Directory.CreateDirectory(stutteringSpan);
var stutteringSpanAssembly = Path.Combine(stutteringSpan, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.Loops").Methods.Single(method => method.Name == "Drain");
    method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldc_I4_1).OpCode = OpCodes.Ldc_I4_0;
    module.Write(stutteringSpanAssembly);
}
Run(Extract("extract", stutteringSpanAssembly, "Examples", Drain, stutteringSpan));
var rejectedSpan = RejectedLines(stutteringSpanAssembly, drainProof, "SpanDrainStuttering", true, Drain);
if (rejectedSpan.Length == 0) throw new InvalidOperationException("Span loop rejection has no proof diagnostic");
Console.WriteLine("PASS unchanged span loop proof rejects a nondecreasing slice");

const string AllZero = "Loops::AllZero(System.ReadOnlySpan`1<System.UInt32>)";
var allZeroProof = At("Examples/Proofs/SpanAllZero.lean");
verification.Verify(assembly, "Examples", AllZero, allZeroProof, Path.Combine(root, "SpanAllZero"));
var allZero = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Loops")!
    .GetMethod("AllZero")!.CreateDelegate<AllZeroDelegate>();
foreach (uint[] values in new uint[][] { [], [0], [0, 0], [0, 1, 0], [uint.MaxValue] })
    if (allZero(values) != values.All(value => value == 0))
        throw new InvalidOperationException("Span content loop differs from its sequence predicate");
if (!allZero(default)) throw new InvalidOperationException("Null empty span must satisfy AllZero");
Console.WriteLine("PASS symbolic span contents, all-zero predicate and exact caller-memory preservation");

var skippedRead = Path.Combine(root, "SpanAllZeroSkippedRead");
Directory.CreateDirectory(skippedRead);
var skippedReadAssembly = Path.Combine(skippedRead, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.Loops").Methods.Single(method => method.Name == "AllZero");
    var load = method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldind_U4);
    load.OpCode = OpCodes.Pop;
    method.Body.GetILProcessor().InsertAfter(load, Instruction.Create(OpCodes.Ldc_I4_0));
    module.Write(skippedReadAssembly);
}
Run(Extract("extract", skippedReadAssembly, "Examples", AllZero, skippedRead));
var wrongAllZero = Assembly.Load(File.ReadAllBytes(skippedReadAssembly)).GetType("Examples.Loops")!
    .GetMethod("AllZero")!.CreateDelegate<AllZeroDelegate>();
if (!wrongAllZero([1])) throw new InvalidOperationException("Skipped-read mutation did not change the result");
RejectedLines(skippedReadAssembly, allZeroProof, "SpanAllZeroSkippedRead", true, AllZero);
Console.WriteLine("PASS unchanged content theorem rejects replacing every read with zero");

// A fold carries a running total in a frame home while consuming symbolic span contents.
const string Sum = "Loops::Sum(System.ReadOnlySpan`1<System.UInt64>)";
var sumProof = At("Examples/Proofs/SpanSum.lean");
verification.Verify(assembly, "Examples", Sum, sumProof, Path.Combine(root, "SpanSum"));
var sum = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Loops")!
    .GetMethod("Sum")!.CreateDelegate<SumDelegate>();
static ulong WrappingSum(ulong[] values) => values.Aggregate(0UL, (total, value) => unchecked(total + value));
ulong[][] sumInputs = [[], [7], [1, 2, 3], [ulong.MaxValue, 2], [ulong.MaxValue, ulong.MaxValue, 5]];
foreach (var values in sumInputs)
    if (sum(values) != WrappingSum(values))
        throw new InvalidOperationException("Span fold differs from its wrapping sum");
if (sum(default) != 0) throw new InvalidOperationException("Null empty span must sum to zero");
Console.WriteLine("PASS symbolic span fold, wrapping sum and caller-memory preservation");

// Stopping while one element remains is still a terminating fold, but omits the last element.
var skippedLast = Path.Combine(root, "SpanSumSkippedLast");
Directory.CreateDirectory(skippedLast);
var skippedLastAssembly = Path.Combine(skippedLast, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.Loops").Methods.Single(method => method.Name == "Sum");
    var guard = method.Body.Instructions.Single(
        instruction => instruction.OpCode.FlowControl == FlowControl.Cond_Branch);
    method.Body.GetILProcessor().InsertBefore(guard, Instruction.Create(OpCodes.Ldc_I4_1));
    guard.OpCode = OpCodes.Bgt;
    module.Write(skippedLastAssembly);
}
Run(Extract("extract", skippedLastAssembly, "Examples", Sum, skippedLast));
var wrongSum = Assembly.Load(File.ReadAllBytes(skippedLastAssembly)).GetType("Examples.Loops")!
    .GetMethod("Sum")!.CreateDelegate<SumDelegate>();
if (wrongSum([1, 2, 3]) != 3)
    throw new InvalidOperationException("Skipped-last mutation did not drop the last element");
RejectedLines(skippedLastAssembly, sumProof, "SpanSumSkippedLast", true, Sum);
Console.WriteLine("PASS unchanged fold theorem rejects skipping the last element");

// A buffer loop is proved as a sequence property: every nonnegative count fills exactly that
// many words from write authority alone and changes no other caller byte.
const string FillWords = "Loops::FillWords(ulong&,ulong,int)";
var fillProof = At("Examples/Proofs/FillWords.lean");
verification.Verify(assembly, "Examples", FillWords, fillProof, Path.Combine(root, "FillWords"));
Console.WriteLine("PASS buffer fill loop yields the replicated words for every nonnegative count");

var fill = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Loops")!.GetMethod("FillWords")!
    .CreateDelegate<FillWordsDelegate>();
foreach (var count in new[] { 0, 1, 2, 5 })
{
    var buffer = new ulong[count + 2];
    Array.Fill(buffer, 3UL);
    fill(ref buffer[1], 7, count);
    if (buffer[0] != 3 || buffer[^1] != 3 || buffer[1..^1].Any(word => word != 7))
        throw new InvalidOperationException($"FillWords({count}) changed the wrong words: {string.Join(", ", buffer)}");
}
Console.WriteLine("PASS buffer fill runtime comparisons keep both neighbouring words");

// Shifting every store one word and skipping every other word each break the sequence claim.
foreach (var (name, mutate) in new (string, Action<MethodDefinition>)[]
{
    ("FillWordsShifted", method =>
    {
        var index = method.Body.Instructions.Single(i => i.OpCode == OpCodes.Call).Previous;
        var il = method.Body.GetILProcessor();
        il.InsertAfter(index, Instruction.Create(OpCodes.Add));
        il.InsertAfter(index, Instruction.Create(OpCodes.Ldc_I4_1));
    }),
    ("FillWordsSkipping", method => method.Body.Instructions.Single(i => i.OpCode == OpCodes.Ldc_I4_1).OpCode = OpCodes.Ldc_I4_2)
})
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        mutate(module.GetType("Examples.Loops").Methods.Single(m => m.Name == "FillWords"));
        module.Write(dll);
    }
    Run(Extract("extract", dll, "Examples", FillWords, output));
    var refused = false;
    try { verification.Verify(dll, "Examples", FillWords, fillProof, output, existingArtifacts: true); }
    catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
    {
        refused = true;
    }
    if (!refused || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException($"{name} satisfied the buffer fill proof");
    Console.WriteLine($"PASS unchanged buffer fill proof rejects {name}");
}

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
    CIL.Safety.invoke Extracted.program fuel 0 [.scalar (.i32 x)] CIL.Safety.Memory.empty =
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
    CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i32 0)] CIL.Safety.Memory.empty =
      .error ⟨0, 0, .fuelExhausted⟩ ∧
    (CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i32 1)] CIL.Safety.Memory.empty).map Prod.snd =
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
theorem correctness : (CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i32 0)] CIL.Safety.Memory.empty).map Prod.snd =
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
            code.Add(Instruction.Create(OpCodes.Newarr, module.TypeSystem.Single));
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

// A generated starting proof must elaborate with only its holes open, and verification must refuse it
// until every hole is filled; otherwise an author could mistake the outline for a proof.
// Loops reuse the checked extraction an earlier section left under their name; the straight-line
// methods cover `bool`, narrow and array parameters and a `bool` result, the indexed loops reading and storing
// array elements, the loops slicing a span local made from a span or an array argument, and the object methods
// `this`, field loads and stores, an object result, calls and a loop over a `callvirt`.
var outlined = new (string Name, string? Selector)[]
{
    ("Countdown", null), ("FillWords", null), ("CountUntil", null), ("CountCalls", null), ("SpanDrain", null),
    ("SpanAllZero", null), ("SpanSum", null), ("TallyTwice", null), ("CopyUntilZero", null),
    ("Choose", "Arithmetic::Choose(bool,ulong,ulong)"), ("Narrow", "Arguments::Narrow(byte)"),
    ("ReverseI16", "Bits::ReverseI16(short)"), ("PowerU32", "Bits::PowerU32(uint)"),
    ("Deposit", "Account::Deposit(System.UInt64)"), ("Headroom", "Account::get_Headroom()"),
    ("SetLimit", "Objects::SetLimit(Examples.Account,System.UInt32)"),
    ("Replace", "Objects::Replace(Examples.Account,System.UInt64)"),
    ("SecondValue", "Objects::SecondValue(Examples.Node)"),
    ("Link", "Objects::Link(Examples.Node,Examples.Node)"),
    ("LinkBoth", "Objects::LinkBoth(Examples.Node,Examples.Node,Examples.Node)"),
    // Its nodes are named like the hypotheses and memories the proof introduces, which must not capture them.
    ("Relink", "Objects::Relink(Examples.Node,Examples.Node,Examples.Node)"),
    ("FirstPresent", "Objects::FirstPresent(Examples.Account,Examples.Account)"),
    ("DepositBoth", "Objects::DepositBoth(Examples.Account,Examples.Account,System.UInt64)"),
    ("DepositTimes", "Objects::DepositTimes(Examples.Account,System.UInt64,System.UInt32)"),
    ("DepositFrom", "Objects::DepositFrom(Examples.Account,Examples.Account,System.UInt32)"),
    ("Withdraw", "Objects::Withdraw(Examples.Account,System.UInt64)"),
    ("LinkedValue", "Objects::LinkedValue(Examples.Node,Examples.Node)"),
    ("IsIdle", "ItemPool::IsIdle(Examples.PooledItem)"),
    ("DownThenUp", "Loops::DownThenUp(uint)"),
    ("CheckedAdd", "CheckedArithmetic::Add(uint,uint)"), ("Log64", "Bits::Log64(ulong)"),
    ("AddSigned", "CheckedArithmetic::AddSigned(int,int)"), ("Distance", "Arithmetic::Distance(ulong,ulong)"),
    ("Larger", "Arithmetic::Larger(int,int)"), ("CounterAdd", "Counter::Add(ulong)"),
    ("OdometerNext", "Odometer::Next()"),
    // A string field's reference is copied, compared, tested and cleared without being read through.
    ("CopyTag", "Objects::CopyTag(Examples.Tagged,Examples.Tagged)"),
    ("SameTag", "Objects::SameTag(Examples.Tagged,Examples.Tagged)"),
    ("HasTag", "Objects::HasTag(Examples.Tagged)"),
    ("FillTag", "Objects::FillTag(Examples.Tagged,Examples.Tagged)"),
    ("ClearTag", "Objects::ClearTag(Examples.Tagged)"),
    ("Detach", "Objects::Detach(Examples.Node)"),
    // Array arguments of class references: an element load, the length and a covariance-checked store.
    ("ArrayElement", "NodeArrays::At(Examples.Node[],System.Int32)"),
    ("ArrayLength", "NodeArrays::Count(Examples.Node[])"),
    ("ArrayCovariance", "NodeArrays::Put(Examples.Shape[],System.Int32,Examples.Shape)"),
    ("TagStore", "TagArrays::Put(System.String[],System.Int32,Examples.Tagged)"),
    ("TagLoad", "TagArrays::Take(Examples.Tagged,System.String[],System.Int32)"),
    // Element facts carried across element and field stores: a load after them reads back what was stored.
    ("ElementShift", "NodeArrays::Shift(Examples.Node[],Examples.Node)"),
    ("ElementInstall", "NodeArrays::Install(Examples.Node[],System.Int32,Examples.Node,System.UInt64)"),
    ("ElementStamp", "TagArrays::Stamp(System.String[],Examples.Tagged,System.UInt64)"),
    // A fresh array charged to the heap budget, filled and read back, forgotten by the footprint.
    ("FreshPair", "NodeArrays::Pair(Examples.Node,Examples.Node)"),
    // A writable span filled from the front, directly or through a helper storing its first element, and that
    // helper alone.
    ("SpanFill", "Loops::Fill(System.Span`1<System.UInt32>,uint)"),
    ("SpanFillThrough", "Loops::FillThrough(System.Span`1<System.UInt32>,uint)"),
    ("SpanPut", "Loops::Put(System.Span`1<System.UInt32>,uint)"),
    // Element reads of word arrays, directly and through a helper returning the element's address.
    ("ArrayReadInt32", "PrimitiveArrays::ReadInt32(int[],int)"),
    ("ArrayReadUInt64", "PrimitiveArrays::ReadUInt64(ulong[],int)"),
    ("ArrayRead", "ArrayElementReferences::Read(int[],int)"),
    ("ArraySum", "Loops::SumIndexed(ulong[])"), ("ArrayFill", "Loops::FillIndexed(uint[],uint)"),
    ("SpanLocalSum", "Loops::SumThroughLocal(System.ReadOnlySpan`1<System.UInt64>)"),
    ("ArraySpanSum", "Loops::SumThroughSpan(ulong[])"), ("ArraySpanFill", "Loops::FillThroughSpan(uint[],uint)"),
    // Value arrays class fields hold: measured, stored from an argument, returned, and shared through a local
    // whose length is read after the store; struct and vector elements are named by their field.
    ("SampleCount", "SampleArrays::Count(Examples.Samples)"),
    ("SampleRefill", "SampleArrays::Refill(Examples.Samples,System.Int32[])"),
    ("SampleValues", "SampleArrays::ValuesOf(Examples.Samples)"),
    ("SampleShare", "SampleArrays::Share(Examples.Samples,Examples.Samples)"),
    ("TilePairCount", "TileArrays::PairCount(Examples.Tiles)"),
    ("TileRelane", "TileArrays::Relane(Examples.Tiles,System.Runtime.Intrinsics.Vector128`1<System.UInt64>[])"),
    ("TilePairs", "TileArrays::PairsOf(Examples.Tiles)"),
    // A struct array argument no field names: its element is a definition whose identity spans two lines.
    ("PairLength",
        "AggregateArrays::ConstructedLength(Examples.AggregateArrays/Pair[],System.Int32,System.Int32)")
};
var outlineTimer = System.Diagnostics.Stopwatch.StartNew();
var outlineRoot = Path.Combine(root, "Outlines");
if (Directory.Exists(outlineRoot)) DeleteTree(outlineRoot);
Directory.CreateDirectory(outlineRoot);
string[] Cli(params string[] arguments) => ["dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll"), .. arguments];
var libraryPath = verification.CheckoutLeanPath();
var elaborated = outlined.AsParallel().WithDegreeOfParallelism(Environment.ProcessorCount).Select(entry =>
{
    var (name, selector) = entry;
    var scratch = Path.Combine(outlineRoot, name);
    Directory.CreateDirectory(scratch);
    var extraction = selector is null ? Path.Combine(root, name) : Path.Combine(scratch, "Extraction");
    if (selector is not null) Run(Extract("extract", assembly, "Examples", selector, extraction));
    var outline = Path.Combine(scratch, "Proof.lean");
    Run(Cli("new-proof", extraction, outline));
    Run(Cli("new-proof", extraction, Path.Combine(scratch, "Again.lean")));
    var source = File.ReadAllText(outline);
    if (source != File.ReadAllText(Path.Combine(scratch, "Again.lean")))
        return $"new-proof wrote different outlines of {name}";
    Run([verification.LeanExecutable, "--root=" + extraction, "-o", Path.Combine(scratch, "Extracted.olean"),
        Path.Combine(extraction, "Extracted.lean")], leanPath: libraryPath);
    // The outline imports the keyed module the editor workspace builds, which re-exports the extraction.
    var keyed = Regex.Match(source, @"\Aimport Extracted\.(\w+)\n");
    if (!keyed.Success) return $"The {name} outline does not import a keyed extraction module:\n{source}";
    var module = Path.Combine(scratch, "Extracted", keyed.Groups[1].Value + ".lean");
    Directory.CreateDirectory(Path.GetDirectoryName(module)!);
    File.WriteAllText(module, "import Extracted\n");
    Run([verification.LeanExecutable, "--root=" + scratch, "-o", Path.ChangeExtension(module, ".olean"), module],
        leanPath: scratch + Path.PathSeparator + libraryPath);
    var result = Execute([verification.LeanExecutable, outline],
        leanPath: scratch + Path.PathSeparator + libraryPath);
    var messages = Regex.Matches(result.Output, @"Proof\.lean:\d+:\d+: (error|warning): (.*)")
        .Select(match => (Kind: match.Groups[1].Value, Text: match.Groups[2].Value.Trim())).ToArray();
    var holes = Regex.Match(result.Output, @"'ExampleProof\.correctness' depends on axioms: \[[^\]]*sorryAx");
    return result.Code != 0 || messages.Length == 0 || !holes.Success ||
        messages.Any(message => message.Kind == "error" || message.Text != "declaration uses `sorry`")
        ? $"The {name} outline did not elaborate with only its holes open:\n{result.Output}" : null;
}).Where(failure => failure is not null).ToArray();
if (elaborated.Length > 0) throw new InvalidOperationException(string.Join("\n", elaborated));
Console.WriteLine($"PASS new-proof outlines {outlined.Length} methods that elaborate with only their holes open");

// The element definition must read back as the extraction's own element, or the outline states another array type,
// and a body the outline does not step may write the array, so its footprint is the author's to state.
var pairOutline = File.ReadAllText(Path.Combine(outlineRoot, "PairLength", "Proof.lean"));
var pairElement = Regex.Match(pairOutline,
    @"@\[reducible\] def sourceElement : CIL\.ArrayElement :=\n  (?<term>(?:[^\n]*\\\n)+[^\n]*)\n");
var pairExtraction = File.ReadAllText(Path.Combine(outlineRoot, "PairLength", "Extraction", "Extracted.lean"));
if (!pairElement.Success ||
    !pairExtraction.Contains($"({Regex.Replace(pairElement.Groups["term"].Value, @"\\\n\s*", "")})",
        StringComparison.Ordinal) ||
    !pairOutline.Contains("  sorry -- caller memory the method may write", StringComparison.Ordinal))
    throw new InvalidOperationException("The PairLength outline does not name its struct element across lines " +
        "or leaves its footprint stated:\n" + pairOutline);
Console.WriteLine("PASS a struct element wider than a line reads back as the extraction's element, and an " +
    "unstepped body over a value array leaves its footprint to the author");

// A loop asks write authority only of the object whose field it or a callee stores; the other is only read.
var depositFrom = File.ReadAllText(Path.Combine(outlineRoot, "DepositFrom", "Proof.lean"));
if (!depositFrom.Contains("Account.Balance.Owned initial account", StringComparison.Ordinal) ||
    !depositFrom.Contains("Account.Balance.Readable initial source", StringComparison.Ordinal) ||
    depositFrom.Contains("Account.Balance.Owned initial source", StringComparison.Ordinal))
    throw new InvalidOperationException("The DepositFrom outline does not ask per-object field facts:\n" + depositFrom);
Console.WriteLine("PASS a loop outline asks Owned only of the object its callee stores and Readable of the one it reads");

// An object local changes its frame slot at each store, so the head must name the slot from the loop state, and its
// null test must split the walk rather than stop it.
var isIdle = File.ReadAllText(Path.Combine(outlineRoot, "IsIdle", "Proof.lean"));
if (!isIdle.Contains("locals := [.object (some state.values)]", StringComparison.Ordinal) ||
    !isIdle.Contains("cases node with", StringComparison.Ordinal) ||
    !isIdle.Contains("by_cases branch1 : ((.address nodeObject) : ManagedReference) = (.address item)",
        StringComparison.Ordinal))
    throw new InvalidOperationException("The IsIdle outline does not follow its object local:\n" + isIdle);
Console.WriteLine("PASS a loop outline carries an object local in its head and splits on its null and identity tests");
// A test of a `bool` struct field splits on the word its load zero-extends, and each side steps to its return.
var copyOutline = File.ReadAllText(Path.Combine(outlineRoot, "CopyUntilZero", "Proof.lean"));
if (!copyOutline.Contains("by_cases branch1 : (scanStopped.setWidth 8).setWidth 32 = 0", StringComparison.Ordinal) ||
    copyOutline.Contains("narrow field", StringComparison.Ordinal))
    throw new InvalidOperationException(
        "The CopyUntilZero outline does not split on its narrow field:\n" + copyOutline);
Console.WriteLine("PASS a loop outline splits on a narrow struct field's loaded word");

// The audit refuses an outline for its holes, whatever the method; one loop shows it end to end.
var countdownOutline = Path.Combine(root, "Countdown");
var countdownSource = Path.Combine(outlineRoot, "Countdown", "Proof.lean");
var outlineRefused = Execute(Cli("verify", countdownOutline, "--proof", countdownSource));
if (outlineRefused.Code == 0 || !outlineRefused.Output.Contains("Unapproved proof axioms: sorryAx") ||
    outlineRefused.Output.Contains(": error") || File.Exists(Path.Combine(countdownOutline, "verified.json")))
    throw new InvalidOperationException("verify did not refuse the Countdown outline for its holes:\n" +
        outlineRefused.Output);

// Filling only the holes, with nothing else edited, must give a proof that verifies.
var filled = Path.Combine(outlineRoot, "Countdown", "Filled.lean");
var countdownHoles = new (string Hole, string Filled)[]
{
    ("def Precondition (value : W32) : Prop := sorry", "def Precondition (value : W32) : Prop := True"),
    ("def Postcondition (value result : W32) : Prop := sorry",
        "def Postcondition (value result : W32) : Prop := result = 0"),
    ("(state : State home0) : Prop := sorry", "(state : State home0) : Prop := True"),
    ("(state : State home0) : Nat := sorry", "(state : State home0) : Nat := state.values.toNat"),
    ("case invariant => sorry -- invariant at the first loop head", "case invariant => trivial"),
    (@"sorry -- Postcondition at the return at Loops\.cs:\d+", "simp_all [Postcondition]"),
    ("case invariant => sorry -- invariant again at the loop head", "case invariant => trivial"),
    ("case measure => sorry -- measure decreases over this iteration", """
    case measure =>
          show (remaining - 1).toNat < remaining.toNat
          have positive : 0 < remaining.toNat := by
            have : remaining.toNat ≠ 0 := fun zero => guard (BitVec.eq_of_toNat_eq zero)
            omega
          rw [BitVec.toNat_sub_of_le]
          · simp; omega
          · change 1 ≤ remaining.toNat
            omega
    """.Trim())
};
var filledSource = File.ReadAllText(countdownSource);
// The CLI reference shows this outline, so the page must change when the generator does.
var documented = Regex.Match(File.ReadAllText(At("docs/CLI.md")).ReplaceLineEndings("\n"),
    "```lean extracted\n(import Extracted\\.\\w+\n.*?)```", RegexOptions.Singleline);
if (!documented.Success || documented.Groups[1].Value != filledSource)
    throw new InvalidOperationException("docs/CLI.md does not show the current Countdown outline");
foreach (var (hole, replacement) in countdownHoles)
{
    var pattern = hole.Contains(@"\d") ? hole : Regex.Escape(hole);
    if (Regex.Matches(filledSource, pattern).Count != 1)
        throw new InvalidOperationException("The Countdown outline lacks the hole " + hole);
    filledSource = Regex.Replace(filledSource, pattern, replacement.Replace("$", "$$"));
}
if (Regex.IsMatch(filledSource, @"(?<![`\w])sorry(?![`\w])"))
    throw new InvalidOperationException("The Countdown outline has a hole the test does not fill");
File.WriteAllText(filled, filledSource);
var proved = Execute(Cli("verify", countdownOutline, "--proof", filled));
if (proved.Code != 0 || !proved.Stdout.StartsWith("Verified: ExampleProof.correctness"))
    throw new InvalidOperationException("The filled Countdown outline did not verify:\n" + proved.Output);
Console.WriteLine("PASS verify refuses the Countdown outline until its holes are filled, then verifies it " +
    $"({outlineTimer.Elapsed.TotalSeconds:F0}s for every outline check)");

// A reader returns the element its index selects; an index outside the array throws, which the precondition rules
// out. Only a read through a helper leaves the memory as the caller's frame left it.
(string Hole, string Filled)[] ArrayReadSpecification(string word, string memory) => [
    ($"""
        def Precondition (values1 : ArrayView) (values1Elements : List {word}) (index : W32) (initial : Memory)
            : Prop := sorry
        """,
        $"""
        def Precondition (_ : ArrayView) (values1Elements : List {word}) (index : W32) (_ : Memory) : Prop :=
          index.toNat < values1Elements.length
        """),
    ($"""
        def Postcondition (values1 : ArrayView) (values1Elements : List {word}) (index : W32)
            (initial final : Memory) (result : {word}) : Prop := sorry
        """,
        $"""
        def Postcondition (_ : ArrayView) (values1Elements : List {word}) (index : W32)
            (initial final : Memory) (result : {word}) : Prop :=
          final = initial ∧ values1Elements[index.toNat]? = some result
        """),
    ("      sorry -- Postcondition of `values1Elements[index.toNat]`", $"      simp [Postcondition{memory}]"),
    ("    sorry -- Precondition excludes an index outside `values1`", "    exact values1Bound assumed")];

// A span filled from the front, directly or through a helper, has one specification and loop head proof.
(string Hole, string Filled)[] spanFillSpecification = [
    ("def Precondition (target1 : SpanView) (value : W32) (initial : Memory) : Prop := sorry",
        """
        def Precondition (_ : SpanView) (_ : W32) (_ : Memory) : Prop := True
        """),
    ("def Postcondition (target1 : SpanView) (value : W32) (initial final : Memory) : Prop := sorry",
        """
        def Postcondition (target1 : SpanView) (value : W32) (_ final : Memory) : Prop :=
          ∀ base, target1.reference = .address base →
            Contents final base 4 (List.replicate target1.length (value : BitVec (8 * 4)))
        """),
    ("""
    def invariant (target1 : SpanView) (value : W32)
        {memory : Memory} {written : List (Reference × Nat)} (state : State memory written)
        : Prop := sorry
    """,
        """
        def invariant (target1 : SpanView) (value : W32)
            {memory : Memory} {written : List (Reference × Nat)} (state : State memory written)
            : Prop :=
          ∀ base, target1.reference = .address base → ∃ done,
            done + state.values.remaining = target1.length ∧
            state.values.view.reference = .address (base.element 4 done) ∧
            Filled state.memory base 4 (List.replicate done (value : BitVec (8 * 4)))
              state.values.remaining
        """),
    ("""
    def measure (target1 : SpanView) (value : W32) {memory : Memory} {written : List (Reference × Nat)}
        (state : State memory written) : Nat := sorry
    """,
        """
        def measure (_ : SpanView) (_ : W32) {memory : Memory} {written : List (Reference × Nat)}
            (state : State memory written) : Nat := state.values.remaining
        """),
    ("    case invariant => sorry -- invariant at the first loop head",
        """
            case invariant =>
              dsimp only [invariant]
              intro base address
              refine ⟨0, by simp, by simp [address], ?_⟩
              have room := (target1Authority.writable base address).after_confined entryFrame.confined
                wellFormed
              rw [target1Width] at room
              simpa using Filled.start room
        """),
    ("    case measure => sorry -- measure decreases over this iteration",
        """
            case measure =>
              simp only [measure]
              omega
        """)];

// A span local over a span argument or a whole array folds as the argument itself does: the local's suffix is
// the loop state, and the theorem names the source's elements.
(string Hole, string Filled)[] SpanLocalSumSpecification(string source, int returnLine) => [
    ($"def Precondition (values1 : {source}) (values1Elements : List W64) (initial : Memory)\n    : Prop := sorry",
        $"def Precondition (_ : {source}) (_ : List W64) (_ : Memory) : Prop := True"),
    ("    (result : W64) : Prop := sorry", "    (result : W64) : Prop := result = values1Elements.sum"),
    ("{memory : Memory} {home1 : Reference} (state : State memory home1) : Prop := sorry",
        "{memory : Memory} {home1 : Reference} (state : State memory home1) : Prop :=\n" +
        "  state.values.2 + state.values.1.values.sum = values1Elements.sum"),
    ("(state : State memory home1) : Nat := sorry",
        "(state : State memory home1) : Nat := state.values.1.values.length"),
    ("case invariant => sorry -- invariant at the first loop head", "case invariant => simp [invariant]"),
    ($"sorry -- Postcondition at the return at Loops.cs:{returnLine}",
        "simpa [Postcondition, invariant] using holds"),
    ("case invariant => sorry -- invariant again at the loop head",
        "case invariant => simpa [invariant, BitVec.add_assoc] using holds"),
    ("case measure => sorry -- measure decreases over this iteration", "case measure => simp [measure]")];

// Object outlines leave only their specification: once it is written, an instance method's field store, a
// reference field store, a null test of an argument followed through a local, a split on a field value and a
// call to a callee that loads the object a field holds each verify.
const string storedHole = "sorry -- Postcondition of the returned value, with `held1` the stored fields";
foreach (var (name, fills) in new (string Name, (string Hole, string Filled)[] Fills)[]
{
    ("Deposit", [
        ("def Precondition (account : Reference) (amount : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : W64) (_ : Memory) : Prop := True"),
        ("def Postcondition (account : Reference) (amount : W64) (initial final : Memory) : Prop := sorry",
            "def Postcondition (account : Reference) (amount : W64) (initial final : Memory) : Prop :=\n" +
            "  Account.Balance.Holds final account (Account.Balance.of initial account + amount)"),
        (storedHole, "exact held1")]),
    ("Link", [
        ("def Precondition (node next : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (node next : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (node next : Reference) (_ final : Memory) : Prop :=\n" +
            "  Node.Next.Holds final node (.address next)"),
        (storedHole, "exact held1")]),
    ("FirstPresent", [
        ("def Precondition (first second : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (first second : Reference) (initial final : Memory) (result : ManagedReference)\n" +
            "    : Prop := sorry",
            "def Postcondition (first _ : Reference) (_ _ : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = .address first"),
        ("sorry -- Postcondition of the returned value", "rfl")]),
    // The second store may reach the first node's field too, which `across` splits on.
    ("LinkBoth", [
        ("def Precondition (first second next : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (first second next : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (first second next : Reference) (_ final : Memory) : Prop :=\n" +
            "  Node.Next.Holds final first (.address next) ∧ Node.Next.Holds final second (.address next)"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields", """
        have firstHeld := held1.1.across secondLive1 framed2 held2
          rw [held1.2, ite_self] at firstHeld
          exact ⟨firstHeld, held2⟩
        """.Trim())]),
    ("DepositBoth", [
        ("def Precondition (first second : Reference) (amount : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (first second : Reference) (_ : W64) (_ : Memory) : Prop := first ≠ second"),
        ("def Postcondition (first second : Reference) (amount : W64) (initial final : Memory) : Prop := sorry",
            "def Postcondition (first second : Reference) (amount : W64) (initial final : Memory) : Prop :=\n" +
            "  Account.Balance.Holds final first (Account.Balance.of initial first + amount) ∧\n" +
            "    Account.Balance.Holds final second (Account.Balance.of initial second + amount)"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields", """
        have distinct : first ≠ second := assumed
          have firstHeld := held1.1.across secondLive1 framed2 held2
          have secondBefore := (secondBalance.across firstLive framed1 held1).2
          simp only [distinct, ite_false] at secondBefore
          simp only [Ne.symm distinct, ite_false, held1.2] at firstHeld
          rw [secondBefore] at held2
          exact ⟨firstHeld, held2⟩
        """.Trim())]),
    // Each side of the test on the balance steps to its own return and leaves its own postcondition.
    ("Withdraw", [
        ("def Precondition (account : Reference) (amount : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : W64) (_ : Memory) : Prop := True"),
        ("def Postcondition (account : Reference) (amount : W64) (initial final : Memory) (result : W64)\n" +
            "    : Prop := sorry",
            "def Postcondition (account : Reference) (amount : W64) (initial final : Memory) (result : W64)\n" +
            "    : Prop :=\n" +
            "  if amount ≤ Account.Balance.of initial account then\n" +
            "    result = amount ∧\n" +
            "      Account.Balance.Holds final account (Account.Balance.of initial account - amount)\n" +
            "  else result = 0 ∧ final = initial"),
        ("-- Postcondition of the returned value where `branch1` holds, with `held1` the stored fields\n" +
            "    sorry",
            "simp only [Postcondition, branch1, ↓reduceIte, true_and]\n    exact held1"),
        ("sorry -- Postcondition of the returned value where `branch1` fails",
            "simp only [Postcondition, branch1, ↓reduceIte]\n    exact ⟨rfl, rfl⟩")]),
    // The callee's contract states its result of whatever node the field holds; the caller names it by the
    // store just before the call, so the result is the value of `next`.
    ("LinkedValue", [
        ("def Precondition (node next : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (node next : Reference) (initial final : Memory) (result : W64) : Prop := sorry",
            "def Postcondition (_ next : Reference) (initial _ : Memory) (result : W64) : Prop :=\n" +
            "  result = Node.Value.of initial next"),
        (storedHole, "exact (nextValue.frame framed1 (apart_of_entries rfl)).2")]),
    // Each path stores the total before it loads the span again, and the loop tactics step on with no frame lemma.
    ("SpanSum", [
        ("def Precondition (values1 : SpanView) (values1Elements : List W64) (initial : Memory)\n    : Prop := sorry",
            "def Precondition (_ : SpanView) (_ : List W64) (_ : Memory) : Prop := True"),
        ("    (result : W64) : Prop := sorry", "    (result : W64) : Prop := result = values1Elements.sum"),
        ("{memory : Memory} {home0 : Reference} (state : State memory home0) : Prop := sorry",
            "{memory : Memory} {home0 : Reference} (state : State memory home0) : Prop :=\n" +
            "  state.values.1 + state.values.2.values.sum = values1Elements.sum"),
        ("(state : State memory home0) : Nat := sorry",
            "(state : State memory home0) : Nat := state.values.2.values.length"),
        ("case invariant => sorry -- invariant at the first loop head", "case invariant => simp [invariant]"),
        ("sorry -- Postcondition at the return at Loops.cs:25", "simpa [Postcondition, invariant] using holds"),
        ("case invariant => sorry -- invariant again at the loop head",
            "case invariant => simpa [invariant, BitVec.add_assoc] using holds"),
        ("case measure => sorry -- measure decreases over this iteration", "case measure => simp [measure]")]),
    // A test of a `bool` argument splits the run into one stepped side per value.
    ("Choose", [
        ("def Precondition (flag : Bool) (x y : W64) : Prop := sorry",
            "def Precondition (_ : Bool) (_ _ : W64) : Prop := True"),
        ("def Postcondition (flag : Bool) (x y result : W64) : Prop := sorry",
            "def Postcondition (flag : Bool) (x y result : W64) : Prop := result = if flag then x else y"),
        ("sorry -- Postcondition of the returned value where `flag` is false", "rfl"),
        ("sorry -- Postcondition of the returned value where `flag` is true", "rfl")]),
    // An `Unsafe.Add` store's write authority, index bound and footprint follow from the specification.
    ("FillWords", [
        ("""
            def Precondition (destination : Reference) (value : W64) (count : W32) (initial : Memory)
                : Prop := sorry
            """,
            """
            def Precondition (destination : Reference) (_ : W64) (count : W32) (initial : Memory)
                : Prop := count.toNat < 2 ^ 31 ∧ Writable initial destination 8 0 count.toNat
            """),
        ("""
            def Postcondition (destination : Reference) (value : W64) (count : W32) (initial final : Memory)
                : Prop := sorry
            """,
            """
            def Postcondition (destination : Reference) (value : W64) (count : W32) (_ final : Memory)
                : Prop := Contents final destination 8 (List.replicate count.toNat (value : BitVec (8 * 8)))
            """),
        ("""
            def footprint (destination : Reference) (value : W64) (count : W32) : List (Reference × Nat) :=
              sorry -- caller memory the loop may write
            """,
            """
            def footprint (destination : Reference) (_ : W64) (count : W32) : List (Reference × Nat) :=
              [(destination, 8 * count.toNat)]
            """),
        ("    (state : State memory written home0) : Prop := sorry",
            """
                (state : State memory written home0) : Prop :=
              state.values.toNat ≤ count.toNat ∧ Filled state.memory destination 8
                (List.replicate state.values.toNat (value : BitVec (8 * 8))) (count.toNat - state.values.toNat)
            """),
        ("def measure (destination : Reference) (value : W64) (count : W32)",
            "def measure (_ : Reference) (_ : W64) (count : W32)"),
        ("    (state : State memory written home0) : Nat := sorry",
            "    (state : State memory written home0) : Nat := count.toNat - state.values.toNat"),
        ("    case invariant => sorry -- invariant at the first loop head",
            """
                case invariant =>
                  simp only [Precondition] at assumed
                  simpa [invariant] using Filled.start (assumed.2.after_confined storedFrame.confined wellFormed)
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  simp only [Precondition] at assumed
                  simp only [invariant] at holds ⊢
                  obtain ⟨-, filled⟩ := holds
                  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at guard
                  simp only [show 2 * i.toNat < 2 ^ 32 by omega, show 2 * count.toNat < 2 ^ 32 by omega,
                    ↓reduceIte] at guard
                  have lower : i.toNat < count.toNat := by omega
                  rw [show count.toNat - i.toNat = count.toNat - (i.toNat + 1) + 1 by omega] at filled
                  have pushed := filled.push (x := (value : BitVec (8 * 8))) (by simpa using destinationWrote)
                  rw [toNat_succ lower, List.replicate_succ']
                  exact ⟨by omega, pushed.after_below storedBelow (wellFormed.form_bound destinationForm)⟩
            """),
        ("    case measure => sorry -- measure decreases over this iteration",
            """
                case measure =>
                  simp only [Precondition] at assumed
                  simp only [invariant] at holds
                  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at guard
                  simp only [show 2 * i.toNat < 2 ^ 32 by omega, show 2 * count.toNat < 2 ^ 32 by omega,
                    ↓reduceIte] at guard
                  simp only [measure, toNat_succ (show i.toNat < count.toNat by omega)]
                  omega
            """),
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:69",
            """
                case postcondition =>
                  simp only [Precondition] at assumed
                  simp only [invariant] at holds
                  obtain ⟨bounded, filled⟩ := holds
                  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at guard
                  simp only [show 2 * i.toNat < 2 ^ 32 by omega, show 2 * count.toNat < 2 ^ 32 by omega,
                    ↓reduceIte] at guard
                  rw [show i.toNat = count.toNat by omega] at filled
                  exact filled.1.after_below exitBelow (wellFormed.form_bound destinationForm)
            """)]),
    // A callee that throws where its precondition fails is split, and the call keeps its output's name.
    ("CountUntil", [
        ("  pre _ _ := sorry",
            "  pre input _ := input.1 ≠ input.2"),
        ("  post _ _ _ _ := sorry",
            "  post input _ _ result := result = input.1 + 1"),
        ("    case postcondition1 => sorry",
            "    case postcondition1 => rfl"),
        ("def Precondition (value limit : W32) : Prop := sorry",
            "def Precondition (value limit : W32) : Prop := value.toNat ≤ limit.toNat"),
        ("def Postcondition (value limit result : W32) : Prop := sorry",
            "def Postcondition (value _ result : W32) : Prop := result = value"),
        ("""
            def invariant (value limit : W32) {home0 home1 : Reference} (state : State home0 home1)
                : Prop := sorry
            """,
            """
            def invariant (value _ : W32) {home0 home1 : Reference} (state : State home0 home1)
                : Prop := state.values.1.toNat + state.values.2.toNat = value.toNat
            """),
        ("def measure (value limit : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat := sorry",
            """
            def measure (_ _ : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat :=
              state.values.1.toNat
            """),
        ("    case invariant => sorry -- invariant at the first loop head",
            "    case invariant => simp [invariant]"),
        ("      sorry -- Postcondition at the return at Loops.cs:145",
            """
                  simp only [invariant] at holds
                  simp only [Postcondition]
                  subst guard
                  exact BitVec.eq_of_toNat_eq (by simpa using holds)
            """),
        ("    case precondition => sorry -- Bump's precondition at this call",
            """
                case precondition =>
                  simp only [invariant] at holds
                  simp only [Precondition] at assumed
                  have positive : remaining.toNat ≠ 0 := fun zero =>
                    guard (BitVec.eq_of_toNat_eq (by simpa using zero))
                  intro same
                  subst same
                  omega
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  simp only [invariant] at holds ⊢
                  simp only [Precondition] at assumed
                  subst returned
                  have positive : remaining.toNat ≠ 0 := fun zero =>
                    guard (BitVec.eq_of_toNat_eq (by simpa using zero))
                  simp [BitVec.toNat_sub, BitVec.toNat_add]
                  omega
            """),
        ("    case measure => sorry -- measure decreases over this iteration",
            """
                case measure =>
                  have positive : remaining.toNat ≠ 0 := fun zero =>
                    guard (BitVec.eq_of_toNat_eq (by simpa using zero))
                  simp [measure, BitVec.toNat_sub]
                  omega
            """)]),
    // A storing callee's contract is proved from its body, and the element passed to it through `Unsafe.Add`
    // is named at the call; this specification needs its own proofs of the element's side conditions.
    ("CopyUntilZero", [
        ("""
            /-- Replace with what callers must guarantee about the arguments, or `True`. -/
            def Precondition (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                (initial : Memory) : Prop := sorry
            """,
            """
            /-- The words copied: those before the first zero, or all of them. -/
            def copied (values : List W32) : List W32 := values.takeWhile (· ≠ 0#32)

            /-- The count of copied words, with bit 31 set exactly when a zero ended the copy. -/
            def answer (values : List W32) : W32 :=
              let count := BitVec.ofNat 32 (copied values).length
              if 0#32 ∈ values then count ||| 0x80000000 else count

            /-- Copying is unaffected by a nonzero prefix. -/
            theorem copied_append {done : List W32} (nonzero : 0#32 ∉ done) (rest : List W32) :
                copied (done ++ rest) = done ++ copied rest :=
              List.takeWhile_append_of_pos fun word mem => by
                simpa using fun same : word = 0#32 => nonzero (same ▸ mem)

            /-- A nonzero word after a nonzero prefix is copied. -/
            theorem copy_bound {values done tail : List W32} {head : W32} (nonzero : 0#32 ∉ done)
                (more : ¬head = 0#32) (split : values = done ++ head :: tail) :
                done.length < (copied values).length := by
              rw [split, copied_append nonzero]
              simp [copied, more]

            /-- The output has room for the copied words, apart from the span. -/
            def Precondition (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                (initial : Memory) : Prop :=
              Writable initial argument1 4 0 (copied values1Elements).length ∧
                SpanApart values1 (argument1, 4 * (copied values1Elements).length)
            """),
        ("""
            def Postcondition (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                (initial final : Memory) (result : W32) : Prop := sorry
            """,
            """
            def Postcondition (_ : SpanView) (values1Elements : List W32) (argument1 : Reference)
                (_ final : Memory) (result : W32) : Prop :=
              result = answer values1Elements ∧ Contents final argument1 4 (copied values1Elements)
            """),
        ("""
            def footprint (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                : List (Reference × Nat) :=
              sorry -- caller memory the loop may write
            """,
            """
            def footprint (_ : SpanView) (values1Elements : List W32) (argument1 : Reference)
                : List (Reference × Nat) :=
              [(argument1, 4 * (copied values1Elements).length)]
            """),
        ("    (state : State memory written home0 home1) : Prop := sorry",
            """
                (state : State memory written home0 home1) : Prop :=
              ∃ done, values1Elements = done ++ state.values.2.2.2.values ∧ 0#32 ∉ done ∧
                state.values.1.toNat = done.length ∧ state.values.2.1 = 0 ∧
                Filled state.memory argument1 4 done (copied state.values.2.2.2.values).length ∧
                SpanApart state.values.2.2.2.view (argument1, 4 * (copied values1Elements).length)
            """),
        ("def measure (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)",
            "def measure (_ : SpanView) (_ : List W32) (_ : Reference)"),
        ("    (state : State memory written home0 home1) : Nat := sorry",
            "    (state : State memory written home0 home1) : Nat := state.values.2.2.2.values.length"),
        ("    case invariant => sorry -- invariant at the first loop head",
            """
                case invariant =>
                  simp only [Precondition] at assumed
                  simp only [invariant]
                  exact ⟨[], by simp, by simp, by simp, by simp,
                    Filled.start (assumed.1.after_confined storedFrame.confined wellFormed), assumed.2⟩
            """),
        ("""
                have values1Apart : ∀ entry ∈ footprint values1 values1Elements argument1,
                    SpanApart values1View entry :=
                    sorry -- `values1` lies apart from the memory the loop writes
            """,
            """
                have values1Apart : ∀ entry ∈ footprint values1 values1Elements argument1,
                    SpanApart values1View entry := by
                  simp only [invariant] at holds
                  obtain ⟨-, -, -, -, -, -, apart⟩ := holds
                  simpa [footprint] using apart
            """),
        ("""
                  have argument1Reach : Writable initial (argument1.element 4 scanCount.toNat) 4 0 1 := by
                    cil_loop_obligation [invariant, Precondition, footprint]
            """,
            """
                  have argument1Reach : Writable initial (argument1.element 4 scanCount.toNat) 4 0 1 := by
                    simp only [invariant] at holds
                    simp only [Precondition] at assumed
                    obtain ⟨done, split, nonzero, counted, -, -, -⟩ := holds
                    have := copy_bound nonzero branch2 split
                    exact Writable.element_writable assumed.1 (by omega) (by omega)
            """),
        ("""
                  have argument1Small : scanCount.toNat < 2 ^ 31 := by
                    cil_loop_obligation [invariant, Precondition, footprint]
            """,
            """
                  have argument1Small : scanCount.toNat < 2 ^ 31 := by
                    simp only [invariant] at holds
                    obtain ⟨done, split, -, counted, -, -, -⟩ := holds
                    have short := values1Contents.length ▸ SpanView.length_bounded values1 initial values1Valid
                    have lengths := congrArg List.length split
                    simp only [List.length_append, List.length_cons] at lengths
                    omega
            """),
        ("""
                      Within (argument1.element 4 scanCount.toNat, 4) entry := by
                    cil_loop_obligation [invariant, Precondition, footprint]
            """,
            """
                      Within (argument1.element 4 scanCount.toNat, 4) entry := by
                    simp only [invariant] at holds
                    obtain ⟨done, split, nonzero, counted, -, -, -⟩ := holds
                    have := copy_bound nonzero branch2 split
                    refine ⟨_, List.mem_singleton_self _, ?_⟩
                    simp [Within]
                    omega
            """),
        ("""
            def invariant (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                {memory : Memory}
            """,
            """
            def invariant (_ : SpanView) (values1Elements : List W32) (argument1 : Reference)
                {memory : Memory}
            """),
        ("""
                · -- leaves the loop at Loops.cs:129
                  cil_loop_finish [branch1]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    sorry -- Postcondition at the return at Loops.cs:129
                · -- leaves the loop at Loops.cs:129
                  cil_loop_finish [branch1]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    sorry -- Postcondition at the return at Loops.cs:129
            """,
            """
                · -- leaves the loop at Loops.cs:129
                  cil_loop_finish [branch1]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    simp only [invariant] at holds
                    obtain ⟨done, split, nonzero, counted, stopped, filled, -⟩ := holds
                    simp only [List.append_nil] at split
                    subst split
                    have whole : copied values1Elements = values1Elements := by
                      simpa [copied] using copied_append nonzero []
                    simp only [Postcondition]
                    refine ⟨?_, ?_⟩
                    · simp only [answer, whole, nonzero, ite_false, ← counted, BitVec.ofNat_toNat,
                        BitVec.setWidth_eq]
                    · rw [whole]
                      exact filled.1.after_below exitBelow (wellFormed.form_bound argument1Form)
                · -- leaves the loop at Loops.cs:129
                  cil_loop_finish [branch1]
                  case postcondition =>
                    simp only [invariant] at holds
                    obtain ⟨-, -, -, -, stopped, -, -⟩ := holds
                    simp [stopped] at branch1
            """),
        ("""
                  cil_loop_finish [branch2]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    sorry -- Postcondition at the return at Loops.cs:129
            """,
            """
                  cil_loop_finish [branch2]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    simp only [invariant] at holds
                    obtain ⟨done, split, nonzero, counted, stopped, filled, -⟩ := holds
                    subst branch2
                    have whole : copied values1Elements = done := by
                      rw [split, copied_append nonzero]
                      simp [copied]
                    have old := wellFormed.form_bound argument1Form
                    simp only [Postcondition]
                    refine ⟨?_, ?_⟩
                    · unfold answer
                      rw [whole, ← counted, BitVec.ofNat_toNat, BitVec.setWidth_eq]
                      simp [split]
                    · rw [whole]
                      exact ((filled.1.after_below storedBelow old).after_below storedBelow_1 old).after_below
                        exitBelow old
            """),
        ("""
                  case invariant => sorry -- invariant again at the loop head
                  case measure => sorry -- measure decreases over this iteration
            """,
            """
                  case invariant =>
                    simp only [invariant] at holds ⊢
                    obtain ⟨done, split, nonzero, counted, stopped, filled, apart⟩ := holds
                    have room : (copied (values1Head :: values1Tail)).length =
                        (copied values1Tail).length + 1 := by
                      simp [copied, show values1Head ≠ 0#32 from branch2]
                    have old := wellFormed.form_bound argument1Form
                    have atCalled := (filled.after_below storedBelow old).after_confined confined
                      storedFrame.wellFormed (by
                        intro entry member
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                        subst member
                        right; left
                        simp [Reference.element_offset]
                        omega)
                    have atHead := atCalled.after_below storedBelow_1 old
                    rw [room] at atHead
                    refine ⟨done ++ [values1Head], by simp [split], by simpa using ⟨nonzero, Ne.symm branch2⟩,
                      ?_, stopped, atHead.extend returned (by omega), apart.slice values1Cut⟩
                    simp only [List.length_append, List.length_singleton, ← counted, BitVec.toNat_add]
                    simp
                    omega
                  case measure => simp [measure]
            """)]),
    // The first loop's exit enters the second loop, whose own invariant and measure the proof writes.
    ("DownThenUp", [
        ("def Precondition (value : W32) : Prop := sorry",
            "def Precondition (_ : W32) : Prop := True"),
        ("def Postcondition (value result : W32) : Prop := sorry",
            "def Postcondition (value result : W32) : Prop := result = value"),
        ("def invariant (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Prop := sorry",
            "def invariant (_ : W32) {home0 home1 : Reference} (_ : State home0 home1) : Prop := True"),
        ("def measure (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat := sorry",
            """
            def measure (_ : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat :=
              state.values.1.toNat
            """),
        ("def invariant2 (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Prop := sorry",
            """
            def invariant2 (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Prop :=
              state.values.2.toNat ≤ value.toNat
            """),
        ("def measure2 (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat := sorry",
            """
            def measure2 (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat :=
              value.toNat - state.values.2.toNat
            """),
        ("    case invariant => sorry -- invariant at the first loop head",
            "    case invariant => trivial"),
        ("      case invariant => sorry -- invariant2 at loop 2's first head",
            "      case invariant => simp [invariant2]"),
        ("        sorry -- Postcondition at the return at Loops.cs:157",
            "        simp [Postcondition]"),
        ("""
                  cil_loop_recurse recurse (remaining, climbed + 1) [guard]
                  case invariant => sorry -- invariant again at the loop head
                  case measure => sorry -- measure decreases over this iteration
            """,
            """
                  cil_loop_recurse recurse (remaining, climbed + 1) [guard]
                  case invariant =>
                    simp only [invariant2] at holds ⊢
                    have below : climbed.toNat < value.toNat :=
                      Nat.lt_of_le_of_ne holds fun same => guard (BitVec.eq_of_toNat_eq same)
                    rw [BitVec.toNat_add_of_lt (by simp; omega)]
                    simp
                    omega
                  case measure =>
                    simp only [invariant2] at holds
                    have below : climbed.toNat < value.toNat :=
                      Nat.lt_of_le_of_ne holds fun same => guard (BitVec.eq_of_toNat_eq same)
                    simp only [measure2]
                    rw [BitVec.toNat_add_of_lt (by simp; omega)]
                    simp
                    omega
            """),
        ("""
                cil_loop_recurse recurse (remaining - 1, climbed) [guard]
                case invariant => sorry -- invariant again at the loop head
                case measure => sorry -- measure decreases over this iteration
            """,
            """
                cil_loop_recurse recurse (remaining - 1, climbed) [guard]
                case invariant => trivial
                case measure =>
                  have positive : remaining.toNat ≠ 0 := fun zero => guard (BitVec.eq_of_toNat_eq zero)
                  simp [measure, BitVec.toNat_sub]
                  omega
            """)]),
    // The overflow side is closed from the precondition, so only the fitting side is left.
    ("CheckedAdd", [
        ("def Precondition (x y : W32) : Prop := sorry",
            "def Precondition (x y : W32) : Prop := x.toNat + y.toNat < 2 ^ 32"),
        ("def Postcondition (x y result : W32) : Prop := sorry",
            "def Postcondition (x y result : W32) : Prop := result.toNat = x.toNat + y.toNat"),
        ("      sorry -- Postcondition of the returned value",
            """
                  simp only [Postcondition]
                  rw [BitVec.toNat_add, Nat.mod_eq_of_lt fits1]
            """)]),
    ("Log64", [
        ("def Precondition (value : W64) : Prop := sorry",
            "def Precondition (_ : W64) : Prop := True"),
        ("def Postcondition (value : W64) (result : W32) : Prop := sorry",
            """
            def Postcondition (value : W64) (result : W32) : Prop :=
              result = BitVec.ofNat 32 value.toNat.log2
            """),
        ("    sorry -- Postcondition of the returned value",
            "    rfl")]),
    ("AddSigned", [
        ("def Precondition (x y : W32) : Prop := sorry",
            "def Precondition (x y : W32) : Prop := -2 ^ 31 ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ 31"),
        ("def Postcondition (x y result : W32) : Prop := sorry",
            "def Postcondition (x y result : W32) : Prop := result.toInt = x.toInt + y.toInt"),
        ("      sorry -- Postcondition of the returned value",
            """
                  simp only [Postcondition]
                  rw [BitVec.toInt_add_of_not_saddOverflow]
                  simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.reduceSub]
                  omega
            """)]),
    ("Distance", [
        ("def Precondition (x y : W64) : Prop := sorry", "def Precondition (_ _ : W64) : Prop := True"),
        ("def Postcondition (x y result : W64) : Prop := sorry",
            "def Postcondition (x y result : W64) : Prop := result = if x < y then y - x else x - y"),
        ("      sorry -- Postcondition of the returned value where `branch1` holds",
            "      simp [Postcondition, branch1]"),
        ("      sorry -- Postcondition of the returned value where `branch1` fails",
            "      simp [Postcondition, branch1]")]),
    // A signed test splits on the words read through `toInt`.
    ("Larger", [
        ("def Precondition (x y : W32) : Prop := sorry", "def Precondition (_ _ : W32) : Prop := True"),
        ("def Postcondition (x y result : W32) : Prop := sorry",
            "def Postcondition (x y result : W32) : Prop := result = if x.toInt < y.toInt then y else x"),
        ("      sorry -- Postcondition of the returned value where `branch1` holds",
            "      simp [Postcondition, branch1]"),
        ("      sorry -- Postcondition of the returned value where `branch1` fails",
            "      simp [Postcondition, branch1]")]),
    // A struct receiver's field store leaves its contents as `held1`, which is the postcondition.
    ("CounterAdd", [
        ("def Precondition (counter : Reference) (value counterValue : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ _ : W64) (_ : Memory) : Prop := True"),
        ("""
        def Postcondition (counter : Reference) (value counterValue : W64) (initial final : Memory)
            (result : W64) : Prop := sorry
        """,
            """
            def Postcondition (counter : Reference) (value counterValue : W64) (_ final : Memory)
                (result : W64) : Prop :=
              result = counterValue + value ∧ Contents final counter 8 [counterValue + value]
            """),
        ("  case postcondition => sorry", "  case postcondition => exact ⟨rfl, held1⟩")]),
    // Its field sits at offset 8, so the outline names it `odometer.element 1 8`.
    ("OdometerNext", [
        ("def Precondition (odometer : Reference) (odometerCount : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : W64) (_ : Memory) : Prop := True"),
        ("""
        def Postcondition (odometer : Reference) (odometerCount : W64) (initial final : Memory)
            (result : W64) : Prop := sorry
        """,
            """
            def Postcondition (odometer : Reference) (odometerCount : W64) (_ final : Memory)
                (result : W64) : Prop :=
              result = odometerCount + 1 ∧ Contents final (odometer.element 1 8) 8 [odometerCount + 1]
            """),
        ("  case postcondition => sorry", "  case postcondition => exact ⟨rfl, held1⟩")]),
    // The string the tag holds is named by the field it was loaded from, whether or not it is null.
    ("CopyTag", [
        ("def Precondition (target1 source : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (target1 source : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (target1 source : Reference) (initial final : Memory) : Prop :=\n" +
            "  Tagged.Tag.Holds final target1 (Tagged.Tag.of initial source)"),
        (storedHole, "exact held1")]),
    // A null test of the tag splits the proof; only the side where it is null stores.
    ("FillTag", [
        ("def Precondition (target1 source : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (target1 source : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (target1 source : Reference) (initial final : Memory) : Prop :=\n" +
            "  if Tagged.Tag.of initial target1 = .null then\n" +
            "    Tagged.Tag.Holds final target1 (Tagged.Tag.of initial source)\n" +
            "  else final = initial"),
        ("-- Postcondition of the returned value where `branch1` holds, with `held1` the stored fields\n" +
            "    sorry",
            "simp only [Postcondition, branch1, ↓reduceIte]\n    exact held1"),
        ("sorry -- Postcondition of the returned value where `branch1` fails",
            "simp only [Postcondition, branch1, ↓reduceIte]\n    rfl")]),
    // The returned word is computed from a comparison, so the proof chooses the Bool it encodes.
    ("HasTag", [
        ("def Precondition (item : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (item : Reference) (initial final : Memory) (result : Bool) : Prop := sorry",
            "def Postcondition (item : Reference) (initial final : Memory) (result : Bool) : Prop :=\n" +
            "  result = (Tagged.Tag.of initial item != .null) ∧ final = initial"),
        ("case result => sorry -- the Bool the returned word encodes",
            "case result => exact Tagged.Tag.of initial item != .null"),
        ("case encoded => sorry -- the returned word is that Bool's encoding",
            "case encoded => by_cases present : Tagged.Tag.of initial item = .null <;> simp [present]"),
        ("sorry -- Postcondition of the returned value", "exact ⟨rfl, rfl⟩")]),
    // A null store into a class field, after which the returned node must still form.
    ("Detach", [
        ("def Precondition (node : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (node : Reference) (initial final : Memory) (result : ManagedReference)\n" +
            "    : Prop := sorry",
            "def Postcondition (node : Reference) (initial final : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = Node.Next.of initial node ∧ Node.Next.Holds final node .null"),
        (storedHole, "exact ⟨nodeNextHeld.symm, held1⟩")]),
    // The element is named by the array and index it was loaded from, null or not.
    ("ArrayElement", [
        ("def Precondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32) (_ : Memory) :\n" +
            "    Prop := True"),
        ("def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (initial final : Memory) (result : ManagedReference) : Prop := sorry",
            "def Postcondition (nodes : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (index : W32)\n" +
            "    (initial final : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = ReferenceArray.of initial nodes index.toNat ∧ final = initial"),
        ("sorry -- Postcondition of the returned value", "exact ⟨rfl, rfl⟩")]),
    ("ArrayLength", [
        ("def Precondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : Memory) : Prop :=\n" +
            "  True"),
        ("def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (initial final : Memory) (result : W32) : Prop :=\n" +
            "  result = BitVec.ofNat 32 nodesLength ∧ final = initial"),
        ("sorry -- Postcondition of the returned value", "exact ⟨rfl, rfl⟩")]),
    // The statement leaves the covariance check of the stored shape as a premise, since a `Shape[]` may be an
    // array of any class derived from `Shape`.
    ("ArrayCovariance", [
        ("def Precondition (shapes : Reference) (shapesElement : CIL.Extraction.TypeExpr) (shapesLength : Nat)\n" +
            "    (index : W32) (shape : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32)\n" +
            "    (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (shapes : Reference) (shapesElement : CIL.Extraction.TypeExpr)\n" +
            "    (shapesLength : Nat) (index : W32) (shape : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (shapes : Reference) (shapesElement : CIL.Extraction.TypeExpr)\n" +
            "    (shapesLength : Nat) (index : W32) (shape : Reference) (_ final : Memory) : Prop :=\n" +
            "  ReferenceArray.Holds final shapes shapesElement shapesLength index.toNat (.address shape)"),
        (storedHole, "exact held1")]),
    // A string moves between a field and an element as the reference it is, never read through.
    ("TagStore", [
        ("def Precondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (index : W32) (tagged : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32)\n" +
            "    (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (index : W32) (tagged : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (index : W32) (tagged : Reference) (initial final : Memory) : Prop :=\n" +
            "  ReferenceArray.Holds final tags tagsElement tagsLength index.toNat\n" +
            "    (Tagged.Tag.of initial tagged)"),
        (storedHole, "exact held1")]),
    ("TagLoad", [
        ("def Precondition (tagged tags : Reference) (tagsElement : CIL.Extraction.TypeExpr)\n" +
            "    (tagsLength : Nat) (index : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32)\n" +
            "    (_ : Memory) : Prop := True"),
        ("def Postcondition (tagged tags : Reference) (tagsElement : CIL.Extraction.TypeExpr)\n" +
            "    (tagsLength : Nat) (index : W32) (initial final : Memory) : Prop := sorry",
            "def Postcondition (tagged tags : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat)\n" +
            "    (index : W32) (initial final : Memory) : Prop :=\n" +
            "  Tagged.Tag.Holds final tagged (ReferenceArray.of initial tags index.toNat)"),
        (storedHole, "exact held1")]),
    // The load after two stores reads back the first element's old reference, carried across the store into
    // the other element.
    ("ElementShift", [
        ("def Precondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (node : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : Reference)\n" +
            "    (_ : Memory) : Prop := True"),
        ("def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (node : Reference) (initial final : Memory) (result : ManagedReference) : Prop := sorry",
            "def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (node : Reference) (initial final : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = ReferenceArray.of initial nodes 0 ∧\n" +
            "    ReferenceArray.Holds final nodes nodesElement nodesLength 0 (.address node) ∧\n" +
            "    ReferenceArray.Holds final nodes nodesElement nodesLength 1 (ReferenceArray.of initial nodes 0)"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields",
            "exact ⟨rfl, held2, nodesSlot2At2⟩")]),
    // The element keeps the stored node across the store into the node's own field.
    ("ElementInstall", [
        ("def Precondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (node : Reference) (value : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32)\n" +
            "    (_ : Reference) (_ : W64) (_ : Memory) : Prop := True"),
        ("def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (node : Reference) (value : W64) (initial final : Memory)\n" +
            "    (result : ManagedReference) : Prop := sorry",
            "def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (node : Reference) (value : W64) (_ final : Memory)\n" +
            "    (result : ManagedReference) : Prop :=\n" +
            "  result = .address node ∧\n" +
            "    ReferenceArray.Holds final nodes nodesElement nodesLength index.toNat (.address node) ∧\n" +
            "    Node.Value.Holds final node value"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields",
            "exact ⟨rfl, nodesSlot1At2, held2⟩")]),
    // A string element copied after a field store forms and passes the covariance check as it did before it.
    ("ElementStamp", [
        ("def Precondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (tagged : Reference) (id : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : Reference)\n" +
            "    (_ : W64) (_ : Memory) : Prop := True"),
        ("def Postcondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (tagged : Reference) (id : W64) (initial final : Memory) : Prop := sorry",
            "def Postcondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (tagged : Reference) (id : W64) (initial final : Memory) : Prop :=\n" +
            "  Tagged.Id.Holds final tagged id ∧\n" +
            "    ReferenceArray.Holds final tags tagsElement tagsLength 1 (ReferenceArray.of initial tags 0)"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields",
            "exact ⟨held1.after_confined framed2 (ReferenceArray.apart_single (show\n" +
            "      tagged.allocation ≠ tags.allocation from tagsLive1.field_ne held1.1.located rfl)), held2⟩")]),
    // The second node comes back, and the caller's memory is confined to nothing.
    ("FreshPair", [
        ("def Precondition (first second : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (first second : Reference) (initial final : Memory) (result : ManagedReference)\n" +
            "    : Prop := sorry",
            "def Postcondition (_ second : Reference) (_ _ : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = .address second"),
        ("sorry -- Postcondition of the returned value, with `held2`, `held3` the stored fields", "rfl")]),
    // A written span needs authority over its elements, not readable contents; the invariant states the
    // filled prefix from the span's own address.
    ("SpanFill", [
        .. spanFillSpecification,
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:168",
            """
                case postcondition =>
                  dsimp only [invariant] at holds
                  intro base address
                  obtain ⟨done, total, -, filled⟩ := holds base address
                  rw [Nat.add_zero] at total
                  subst total
                  exact filled.complete.after_below exitBelow
                    (SpanView.allocation_below target1Valid wellFormed address)
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  dsimp only [invariant] at holds ⊢
                  intro base address
                  obtain ⟨done, total, place, filled⟩ := holds base address
                  rw [place] at target1Address
                  cases target1Address
                  refine ⟨done + 1, by omega, ?_, ?_⟩
                  · rw [SpanView.slice_reference _ _ _ _ _ _ place target1Cut, target1Span.elementWidth]
                    simp only [Reference.element, ManagedReference.address.injEq, Reference.mk.injEq,
                      true_and]
                    omega
                  · rw [List.replicate_succ']
                    exact filled.push (by simpa using target1Wrote)
            """)]),
    // A helper writes each element; the frame after its call keeps the filled prefix, apart from the lent span.
    ("SpanFillThrough", [
        .. spanFillSpecification,
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:181",
            """
                case postcondition =>
                  dsimp only [invariant] at holds
                  intro base address
                  obtain ⟨done, total, -, filled⟩ := holds base address
                  rw [Nat.add_zero] at total
                  subst total
                  exact filled.complete.after_below exitBelow
                    (SpanView.allocation_below target1Valid wellFormed address)
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  dsimp only [invariant] at holds ⊢
                  intro base address
                  obtain ⟨done, total, place, filled⟩ := holds base address
                  refine ⟨done + 1, by omega, ?_, ?_⟩
                  · rw [SpanView.slice_reference _ _ _ _ _ _ place target1Cut, target1Span.elementWidth]
                    simp only [Reference.element, ManagedReference.address.injEq, Reference.mk.injEq,
                      true_and]
                    omega
                  · rw [List.replicate_succ']
                    refine (filled.after_confined confined frame.wellFormed ?_).extend
                      (returned _ place) (by simp)
                    intro entry member
                    simp only [SpanView.footprint, place, List.mem_singleton] at member
                    subst member
                    rw [target1Span.elementWidth, target1Span.length, List.length_replicate]
                    simpa using base.element_run_apart 4 (first := 0) (left := done) (second := done)
                      (right := target1Rest + 1) (Or.inl (by omega))
            """)]),
    // One store into a span outside a loop: an empty span throws, which the precondition rules out.
    ("SpanPut", [
        ("def Precondition (target1 : SpanView) (value : W32) (initial : Memory) : Prop := sorry",
            """
            def Precondition (target1 : SpanView) (_ : W32) (_ : Memory) : Prop := 0 < target1.length
            """),
        ("def Postcondition (target1 : SpanView) (value : W32) (initial final : Memory) : Prop := sorry",
            """
            def Postcondition (target1 : SpanView) (value : W32) (_ final : Memory) : Prop :=
              ∀ base, target1.reference = .address base → Contents final base 4 [value]
            """),
        ("    sorry -- Precondition excludes an empty `target1`",
            "    simp [Precondition, target1Count] at assumed"),
        ("    case postcondition => sorry", "    case postcondition => exact target1Filled")]),
    ("ArrayReadInt32", ArrayReadSpecification("W32", "")),
    ("ArrayReadUInt64", ArrayReadSpecification("W64", "")),
    ("ArrayRead", ArrayReadSpecification("W32", ", leaveFrame")),
    // An indexed loop over an array reads each element from the storage span's contents; the bound test reads
    // the array's length as a signed word, below 2^31 for a valid array.
    ("ArraySum", [
        ("""
        def Precondition (values1 : ArrayView) (values1Elements : List W64) (initial : Memory)
            : Prop := sorry
        """,
            """
            def Precondition (values1 : ArrayView) (_ : List W64) (_ : Memory) : Prop :=
              values1.reference ≠ .null
            """),
        ("""
        def Postcondition (values1 : ArrayView) (values1Elements : List W64) (initial final : Memory)
            (result : W64) : Prop := sorry
        """,
            """
            def Postcondition (_ : ArrayView) (values1Elements : List W64) (_ _ : Memory)
                (result : W64) : Prop := result = values1Elements.foldl (· + ·) 0
            """),
        ("""
        def invariant (values1 : ArrayView) (values1Elements : List W64)
            {memory : Memory} {home0 home1 : Reference} (state : State memory home0 home1) : Prop := sorry
        """,
            """
            def invariant (_ : ArrayView) (values1Elements : List W64)
                {memory : Memory} {home0 home1 : Reference} (state : State memory home0 home1) : Prop :=
              state.values.2.toNat ≤ values1Elements.length ∧
                state.values.1 = (values1Elements.take state.values.2.toNat).foldl (· + ·) 0
            """),
        ("""
        def measure (values1 : ArrayView) (values1Elements : List W64)
            {memory : Memory} {home0 home1 : Reference} (state : State memory home0 home1) : Nat := sorry
        """,
            """
            def measure (_ : ArrayView) (values1Elements : List W64)
                {memory : Memory} {home0 home1 : Reference} (state : State memory home0 home1) : Nat :=
              values1Elements.length - state.values.2.toNat
            """),
        ("    case invariant => sorry -- invariant at the first loop head", "    case invariant => simp [invariant]"),
        ("""
            case invariant => sorry -- invariant again at the loop head
            case measure => sorry -- measure decreases over this iteration
        """,
            """
                case invariant =>
                  have next : (index + 1).toNat = index.toNat + 1 := by
                    simp [BitVec.toNat_add]
                    omega
                  dsimp only [invariant] at holds ⊢
                  refine ⟨by omega, ?_⟩
                  rw [next, List.take_add_one, List.getElem?_eq_getElem values1Bound, List.foldl_append,
                    ← holds.2]
                  simp
                case measure =>
                  have next : (index + 1).toNat = index.toNat + 1 := by
                    simp [BitVec.toNat_add]
                    omega
                  simp only [measure]
                  omega
            """),
        ("      sorry -- Postcondition at the return at Loops.cs:188",
            """
                  dsimp only [invariant] at holds
                  simp (disch := omega) only [BitVec.toInt_eq_toNat_of_lt, toInt_ofNat_of_lt] at guard
                  simp only [Postcondition, holds.2]
                  rw [List.take_of_length_le (by omega)]
            """)]),
    // An indexed fill stores into the storage span by authority alone; the invariant states the filled prefix
    // from the array's own address.
    ("ArrayFill", [
        ("def Precondition (values1 : ArrayView) (value : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (values1 : ArrayView) (_ : W32) (_ : Memory) : Prop := values1.reference ≠ .null"),
        ("def Postcondition (values1 : ArrayView) (value : W32) (initial final : Memory) : Prop := sorry",
            """
            def Postcondition (values1 : ArrayView) (value : W32) (_ final : Memory) : Prop :=
              ∀ base, values1.reference = .address base →
                Contents final base 4 (List.replicate values1.length (value : BitVec (8 * 4)))
            """),
        ("    (state : State memory written home0) : Prop := sorry",
            """
                (state : State memory written home0) : Prop :=
              state.values.toNat ≤ values1.length ∧ ∀ base, values1.reference = .address base →
                Filled state.memory base 4 (List.replicate state.values.toNat (value : BitVec (8 * 4)))
                  (values1.length - state.values.toNat)
            """),
        ("def measure (values1 : ArrayView) (value : W32)", "def measure (values1 : ArrayView) (_ : W32)"),
        ("    (state : State memory written home0) : Nat := sorry",
            "    (state : State memory written home0) : Nat := values1.length - state.values.toNat"),
        ("    case invariant => sorry -- invariant at the first loop head",
            """
                case invariant =>
                  dsimp only [invariant]
                  refine ⟨by simp, ?_⟩
                  intro base address
                  simp only [ManagedReference.address.injEq] at address
                  subst address
                  have room := (values1Authority.writable values1Base rfl).after_confined
                    storedFrame.confined wellFormed
                  simpa [ArrayView.storage, CIL.ArrayElement.width] using Filled.start room
            """),
        ("""
            case invariant => sorry -- invariant again at the loop head
            case measure => sorry -- measure decreases over this iteration
        """,
            """
                case invariant =>
                  have next : (index + 1).toNat = index.toNat + 1 := by
                    simp [BitVec.toNat_add]
                    omega
                  dsimp only [invariant] at holds ⊢
                  refine ⟨by omega, ?_⟩
                  intro base address
                  simp only [ManagedReference.address.injEq] at address
                  subst address
                  have filled := holds.2 values1Base rfl
                  rw [show values1Length - index.toNat = (values1Length - (index.toNat + 1)) + 1 by omega]
                    at filled
                  rw [next, List.replicate_succ']
                  exact (filled.push (by simpa using values1Wrote)).after_below storedBelow values1Below
                case measure =>
                  have next : (index + 1).toNat = index.toNat + 1 := by
                    simp [BitVec.toNat_add]
                    omega
                  simp only [measure]
                  omega
            """),
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:195",
            """
                case postcondition =>
                  dsimp only [invariant] at holds
                  simp only [Postcondition]
                  intro base address
                  simp only [ManagedReference.address.injEq] at address
                  subst address
                  simp (disch := omega) only [BitVec.toInt_eq_toNat_of_lt, toInt_ofNat_of_lt] at guard
                  have done : index.toNat = values1Length := by omega
                  have filled := holds.2 values1Base rfl
                  rw [done, Nat.sub_self] at filled
                  simpa using (filled.after_below exitBelow values1Below).complete
            """)]),
    ("SpanLocalSum", SpanLocalSumSpecification("SpanView", 220)),
    // A span over a whole array, null or not, holds the storage span's elements under the span's access mode.
    ("ArraySpanSum", SpanLocalSumSpecification("ArrayView", 207)),
    // A fill through a writable span over the array has authority over its storage span, as an indexed fill does.
    ("ArraySpanFill", [
        ("def Precondition (values1 : ArrayView) (value : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : ArrayView) (_ : W32) (_ : Memory) : Prop := True"),
        ("def Postcondition (values1 : ArrayView) (value : W32) (initial final : Memory) : Prop := sorry",
            """
            def Postcondition (values1 : ArrayView) (value : W32) (_ final : Memory) : Prop :=
              ∀ base, values1.reference = .address base →
                Contents final base 4 (List.replicate values1.length (value : BitVec (8 * 4)))
            """),
        ("""
        def invariant (values1 : ArrayView) (value : W32)
            {memory : Memory} {written : List (Reference × Nat)} (state : State memory written)
            : Prop := sorry
        """,
            """
            def invariant (values1 : ArrayView) (value : W32)
                {memory : Memory} {written : List (Reference × Nat)} (state : State memory written)
                : Prop :=
              ∀ base, values1.reference = .address base → ∃ done,
                done + state.values.remaining = values1.length ∧
                state.values.view.reference = .address (base.element 4 done) ∧
                Filled state.memory base 4 (List.replicate done (value : BitVec (8 * 4)))
                  state.values.remaining
            """),
        ("""
        def measure (values1 : ArrayView) (value : W32) {memory : Memory} {written : List (Reference × Nat)}
            (state : State memory written) : Nat := sorry
        """,
            """
            def measure (_ : ArrayView) (_ : W32) {memory : Memory} {written : List (Reference × Nat)}
                (state : State memory written) : Nat := state.values.remaining
            """),
        ("    case invariant => sorry -- invariant at the first loop head",
            """
                case invariant =>
                  dsimp only [invariant]
                  intro base address
                  refine ⟨0, by simp, by simp [ArrayView.span, address], ?_⟩
                  have room := (values1Authority.writable base address).after_confined entryFrame.confined
                    wellFormed
                  simp only [ArrayView.storage, values1Type, CIL.ArrayElement.width] at room
                  simpa using Filled.start room
            """),
        ("    case measure => sorry -- measure decreases over this iteration",
            """
                case measure =>
                  simp only [measure]
                  omega
            """),
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:232",
            """
                case postcondition =>
                  dsimp only [invariant] at holds
                  intro base address
                  obtain ⟨done, total, -, filled⟩ := holds base address
                  rw [Nat.add_zero] at total
                  subst total
                  exact filled.complete.after_below exitBelow
                    (SpanView.allocation_below (view := values1.storage) values1Valid wellFormed address)
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  dsimp only [invariant] at holds ⊢
                  intro base address
                  obtain ⟨done, total, place, filled⟩ := holds base address
                  rw [place] at restAddress
                  cases restAddress
                  refine ⟨done + 1, by omega, ?_, ?_⟩
                  · rw [SpanView.slice_reference _ _ _ _ _ _ place restCut, restSpan.elementWidth]
                    simp only [Reference.element, ManagedReference.address.injEq, Reference.mk.injEq,
                      true_and]
                    omega
                  · rw [List.replicate_succ']
                    exact filled.push (by simpa using restWrote)
            """)]),
    // A length of the array a field holds leaves memory as it was.
    ("SampleCount", [
        ("def Precondition (samples : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (samples : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (_ : Reference) (initial final : Memory) (_ : W32) : Prop := final = initial"),
        ("sorry -- Postcondition of the returned value", "rfl")]),
    // The field holds the array argument's origin.
    ("SampleRefill", [
        ("def Precondition (samples values1 : Reference) (values1Length : Nat) (initial : Memory)\n" +
            "    : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Nat) (_ : Memory) : Prop := True"),
        ("def Postcondition (samples values1 : Reference) (values1Length : Nat) (initial final : Memory)\n" +
            "    : Prop := sorry",
            "def Postcondition (samples values1 : Reference) (_ : Nat) (_ final : Memory) : Prop :=\n" +
            "  Samples.Values.Holds final samples (.address values1)"),
        ("sorry -- Postcondition of the returned value, with `held1` the stored fields", "exact held1")]),
    // The returned view is of the array the field holds.
    ("SampleValues", [
        ("def Precondition (samples : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (samples : Reference) (initial final : Memory) (result : ArrayView)\n" +
            "    : Prop := sorry",
            "def Postcondition (samples : Reference) (initial final : Memory) (result : ArrayView) : Prop :=\n" +
            "  result.reference = Samples.Values.of initial samples ∧ final = initial"),
        ("sorry -- Postcondition of the returned value", "exact ⟨samplesValuesHeld.symm, rfl⟩")]),
    // The target's field holds what the source's held, whose length is read after the store.
    ("SampleShare", [
        ("def Precondition (source target1 : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (source target1 : Reference) (initial final : Memory) (result : W32)\n" +
            "    : Prop := sorry",
            "def Postcondition (source target1 : Reference) (initial final : Memory) (_ : W32) : Prop :=\n" +
            "  Samples.Values.Holds final target1 (Samples.Values.of initial source)"),
        ("sorry -- Postcondition of the returned value, with `held1` the stored fields",
            "exact sourceValuesHeld ▸ held1")]),
    // A struct array's length leaves memory as it was.
    ("TilePairCount", [
        ("def Precondition (tiles : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (tiles : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (_ : Reference) (initial final : Memory) (_ : W32) : Prop := final = initial"),
        ("sorry -- Postcondition of the returned value", "rfl")]),
    // The field holds the vector array argument's origin.
    ("TileRelane", [
        ("def Precondition (tiles lanes : Reference) (lanesLength : Nat) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Nat) (_ : Memory) : Prop := True"),
        ("def Postcondition (tiles lanes : Reference) (lanesLength : Nat) (initial final : Memory)\n" +
            "    : Prop := sorry",
            "def Postcondition (tiles lanes : Reference) (_ : Nat) (_ final : Memory) : Prop :=\n" +
            "  Tiles.Lanes.Holds final tiles (.address lanes)"),
        ("sorry -- Postcondition of the returned value, with `held1` the stored fields", "exact held1")]),
    // The returned view is of the struct array the field holds.
    ("TilePairs", [
        ("def Precondition (tiles : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (tiles : Reference) (initial final : Memory) (result : ArrayView) : Prop := sorry",
            "def Postcondition (tiles : Reference) (initial final : Memory) (result : ArrayView) : Prop :=\n" +
            "  result.reference = Tiles.Pairs.of initial tiles ∧ final = initial"),
        ("sorry -- Postcondition of the returned value", "exact ⟨tilesPairsHeld.symm, rfl⟩")])
})
{
    var source = File.ReadAllText(Path.Combine(outlineRoot, name, "Proof.lean"));
    foreach (var (hole, replacement) in fills)
    {
        if (Regex.Matches(source, Regex.Escape(hole)).Count != 1)
            throw new InvalidOperationException($"The {name} outline lacks the hole {hole}:\n{source}");
        source = source.Replace(hole, replacement, StringComparison.Ordinal);
    }
    if (Regex.IsMatch(source, @"(?<![`\w])sorry(?![`\w])"))
        throw new InvalidOperationException($"The {name} outline has a hole the test does not fill:\n{source}");
    var filledOutline = Path.Combine(outlineRoot, name, "Filled.lean");
    File.WriteAllText(filledOutline, source);
    var verified = Execute(Cli("verify", OutlineExtraction(name), "--proof", filledOutline));
    if (verified.Code != 0 || !verified.Stdout.StartsWith("Verified: ExampleProof.correctness"))
        throw new InvalidOperationException($"The filled {name} outline did not verify:\n{verified.Output}");
}
Console.WriteLine("PASS filled outlines verify with only their specification written: a field store, " +
    "two reference field stores that may alias, a null test followed through a local, two calls through a " +
    "generated contract, a split on a field value, a call whose callee loads the node a field holds, a " +
    "span fold that stores its total before each span load, a split on a `bool` argument, a " +
    "store through `Unsafe.Add` of a reference argument, a call to a callee that throws where its " +
    "precondition fails, a call storing through `Unsafe.Add` of a reference argument, two loops in sequence, " +
    "a checked add, a base-two logarithm, a signed checked add, splits on unsigned and signed tests of words, " +
    "a field store through a struct receiver at offsets 0 and 8, a string reference copied, " +
    "tested for null and compared, a null store before returning the node it held, an array argument's element " +
    "load, length and covariance-checked store, element facts carried across element and field stores, " +
    "an array the method allocates, fills and reads back, value arrays of words, structs and vectors that class " +
    "fields hold, measured, stored, returned and shared through a local, a fill through a writable span, and a fill " +
    "through a helper storing the first element of the span it is lent, that helper alone, and element reads of " +
    "`int[]` and `ulong[]` arrays, directly and through a helper returning the element's address, an indexed sum " +
    "and fill of arrays, and a sum and fill through a span local over a span or an array");

// A written footprint that leaves out the element a loop writes is an error at the write, never an admission.
var narrowed = Path.Combine(outlineRoot, "FillWords", "Narrowed.lean");
File.WriteAllText(narrowed, File.ReadAllText(Path.Combine(outlineRoot, "FillWords", "Filled.lean"))
    .Replace("  [(destination, 8 * count.toNat)]", "  []", StringComparison.Ordinal));
var outside = Execute(Cli("verify", OutlineExtraction("FillWords"), "--proof", narrowed));
if (outside.Code == 0 || !outside.Output.Contains("cil_loop_obligation could not prove"))
    throw new InvalidOperationException("verify did not reject a write outside the footprint:\n" + outside.Output);
Console.WriteLine("PASS a loop write outside its written footprint is an error at the write");

// One hole left, an obligation or a path the outline could not step, keeps an outline from certifying:
// verify refuses it for `sorryAx` and removes the report the filled proof left.
var unfinished = new List<(string Name, string Source)>
{
    ("SpanSum", File.ReadAllText(Path.Combine(outlineRoot, "SpanSum", "Filled.lean"))
        .Replace("case measure => simp [measure]", "case measure => sorry"))
};
var unstepped = outlined.Select(entry => entry.Name).FirstOrDefault(name => File.ReadAllText(
    Path.Combine(outlineRoot, name, "Proof.lean")).Contains("-- not outlined:", StringComparison.Ordinal));
if (unstepped is not null)
    unfinished.Add((unstepped, File.ReadAllText(Path.Combine(outlineRoot, unstepped, "Proof.lean"))));
foreach (var (name, source) in unfinished)
{
    var partial = Path.Combine(outlineRoot, name, "Unfinished.lean");
    File.WriteAllText(partial, source);
    var refused = Execute(Cli("verify", OutlineExtraction(name), "--proof", partial));
    if (refused.Code == 0 || !refused.Output.Contains("Unapproved proof axioms: sorryAx") ||
        refused.Output.Contains(": error") || File.Exists(Path.Combine(OutlineExtraction(name), "verified.json")))
        throw new InvalidOperationException($"verify did not refuse the unfinished {name} outline:\n{refused.Output}");
}
Console.WriteLine(unstepped is null
    ? "PASS verify refuses an outline with one obligation left; no outline leaves a path not outlined"
    : $"PASS verify refuses an outline with one obligation left and the {unstepped} outline's path not outlined");

// A loop outline reuses the extraction an earlier section left under its name.
string OutlineExtraction(string name) => outlined.Single(entry => entry.Name == name).Selector is null
    ? Path.Combine(root, name) : Path.Combine(outlineRoot, name, "Extraction");

// LeanCIL's own closure that lays out a static word's bytes: its outline states the getter's contract
// and steps through it, and the checked-in proof fills only the outline's holes and verifies.
var wordByte = Path.Combine(outlineRoot, "WordByte");
var wordByteExtraction = Path.Combine(wordByte, "Extraction");
Run(Cli("extract", At("Extractor/bin/Nethermind.LeanCIL.dll"),
    "Nethermind.LeanCIL.StaticValues/<>c__DisplayClass10_0::<Bytes>b__0(System.Int32)", wordByteExtraction));
var wordByteOutline = Path.Combine(wordByte, "Proof.lean");
Run(Cli("new-proof", wordByteExtraction, wordByteOutline));
var wordByteSource = File.ReadAllText(wordByteOutline);
if (wordByteSource.Contains("-- not outlined:", StringComparison.Ordinal) ||
    !wordByteSource.Contains("theorem get_Bits_holds", StringComparison.Ordinal))
    throw new InvalidOperationException("The closure outline does not step its getter call:\n" + wordByteSource);
static string Statement(string source) =>
    Regex.Match(source.ReplaceLineEndings("\n"), @"^theorem correctness .*?:= by$",
        RegexOptions.Singleline | RegexOptions.Multiline).Value;
var wordByteProof = At("Tests/Outlines/WordByte.lean");
var outlineStatement = Statement(wordByteSource);
if (outlineStatement.Length == 0 || outlineStatement != Statement(File.ReadAllText(wordByteProof)))
    throw new InvalidOperationException("Tests/Outlines/WordByte.lean no longer states the outline's theorem:\n" +
        outlineStatement);
var wordByteVerified = Execute(Cli("verify", wordByteExtraction, "--proof", wordByteProof));
if (wordByteVerified.Code != 0 || !wordByteVerified.Stdout.StartsWith("Verified: ExampleProof.correctness"))
    throw new InvalidOperationException("The closure's filled outline did not verify:\n" + wordByteVerified.Output);
Console.WriteLine("PASS the outline of LeanCIL's own byte-layout closure, filled, verifies its little-endian byte");

delegate void FillWordsDelegate(ref ulong destination, ulong value, int count);
delegate uint CopyUntilZeroDelegate(ReadOnlySpan<uint> values, ref uint output);
delegate bool AllZeroDelegate(ReadOnlySpan<uint> values);
delegate ulong SumDelegate(ReadOnlySpan<ulong> values);
