#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Runtime.CompilerServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Blocks");
Directory.CreateDirectory(root);
var cases = 0;
const string memory = """
def memory : CIL.Safety.Memory := {
  allocations := fun id => if id < 2 then some ⟨.callerStack, ⟨16, 8, []⟩, true, [16]⟩ else none
  cells := fun id offset => ⟨BitVec.ofNat 8 (if id = 0 then 165 else 32 + offset), true⟩
  views := [⟨0, 0, 16, true, true⟩, ⟨1, 0, 16, true, true⟩]
  nextIdentity := 2
}
""";

void Prove(string dll, string selector, string name, List<string> claims)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 8192\nnamespace ExampleProof\n" + memory +
        "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact ⟨" +
        string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    verification.Verify(dll, "Examples", selector, proof, output);
    cases += claims.Count;
    Console.WriteLine($"PASS {name}: {claims.Count} checks");
}

// Model-owned scalar homes retain natural alignment, including addressed parameters.
var runtimeBlocks = Assembly.LoadFile(assembly).GetType("Examples.Blocks")!;
foreach (var name in new[] { "FillLocal", "FillParameter", "CopyLocal", "CopyParameter" })
{
    var method = runtimeBlocks.GetMethod(name)!;
    var claims = new List<string>();
    foreach (var count in new uint[] { 0, 1, 8 })
    foreach (var bits in new ulong[] { 0, 0x8070605040302010, ulong.MaxValue })
    {
        object[] arguments = name switch
        {
            "FillLocal" => [(byte)bits, count],
            "FillParameter" => [bits, (byte)165, count],
            "CopyLocal" => [bits, count],
            _ => [ulong.MaxValue, bits, count]
        };
        var expected = (ulong)method.Invoke(null, arguments)!;
        var values = arguments.Select(value => value is ulong word
            ? $".scalar (.i64 {word})" : $".scalar (.i32 {value})");
        claims.Add($"(CIL.Safety.invoke Extracted.program 64 0 [{string.Join(", ", values)}] memory).map Prod.snd = .ok [.scalar (.i64 {expected})]");
    }
    var prefix = name switch
    {
        "FillLocal" => ".scalar (.i32 165)",
        "FillParameter" => ".scalar (.i64 0), .scalar (.i32 165)",
        "CopyLocal" => ".scalar (.i64 0)",
        _ => ".scalar (.i64 0), .scalar (.i64 0)"
    };
    // Never execute out-of-bounds writes in the CLR; require the model to reject them.
    claims.Add($"((CIL.Safety.invoke Extracted.program 64 0 [{prefix}, .scalar (.i32 9)] memory).map (fun _ => false)).mapError (fun f => match f.fault with | .memory .outsideAllocation _ _ => true | _ => false) = .error true");
    var parameters = name switch
    {
        "FillLocal" => "byte,uint",
        "FillParameter" => "ulong,byte,uint",
        "CopyLocal" => "ulong,uint",
        _ => "ulong,ulong,uint"
    };
    Prove(assembly, $"Blocks::{name}({parameters})", name, claims);
}

// Exercise compiler-generated runtime calls and actual block opcodes with each prefix.
foreach (var copy in new[] { false, true })
foreach (var alignment in new[] { 0, 1, 2, 4, 8 })
{
    var name = (copy ? "Copy" : "Fill") + alignment;
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    var methodName = (copy ? "Copy" : "Fill") + (alignment == 8 ? "Aligned" : "");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Blocks").Methods.Single(m => m.Name == methodName);
        if (alignment != 0)
        {
            var call = method.Body.Instructions.Single(i => i.OpCode.Code == Code.Call);
            call.OpCode = copy ? OpCodes.Cpblk : OpCodes.Initblk;
            call.Operand = null;
            if (alignment != 8)
                method.Body.GetILProcessor().InsertBefore(call, Instruction.Create(OpCodes.Unaligned, (byte)alignment));
        }
        selector = method.FullName;
        module.Write(dll);
    }
    var runtime = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Blocks")!.GetMethod(methodName)!;
    var fill = copy ? null : runtime.CreateDelegate<FillBlock>();
    var move = copy ? runtime.CreateDelegate<CopyBlock>() : null;
    var claims = new List<string>();
    var offset = alignment is 0 or 1 ? 1 : alignment == 8 ? 0 : alignment;
    foreach (var count in new[] { 0, 1, 3, 8 })
    foreach (var value in new byte[] { 0, 127, 255 })
    {
        var destination = Enumerable.Repeat((byte)165, 16).ToArray();
        var source = Enumerable.Range(32, 16).Select(x => (byte)x).ToArray();
        if (copy) move!(ref destination[offset], ref source[offset], (uint)count);
        else fill!(ref destination[offset], value, (uint)count);
        var second = copy ? $".reference (.address ⟨1, {offset}⟩)" : $".scalar (.i32 {value})";
        claims.Add($"(CIL.Safety.invoke Extracted.program 16 0 [.reference (.address ⟨0, {offset}⟩), {second}, .scalar (.i32 {count})] memory).map (fun (m, values) => ((List.range 16).map (fun i => (m.cells 0 i).bits.toNat), values)) = .ok ([{string.Join(", ", destination)}], [])");
    }

    var sourceArgument = copy ? ".reference (.address ⟨1, 0⟩)" : ".scalar (.i32 255)";
    string Invoke(string args, string state = "memory") => $"CIL.Safety.invoke Extracted.program 16 0 [{args}] ({state})";
    string Fault(string args, string rule, string state = "memory") =>
        $"(({Invoke(args, state)}).map (fun _ => false)).mapError (fun f => match f.fault with | .memory .{rule} _ _ => true | _ => false) = .error true";
    claims.Add(Fault($"Examples.reference, {sourceArgument}, .scalar (.i32 17)", "outsideAllocation"));
    claims.Add(Fault($"Examples.reference, {sourceArgument}, .scalar (.i32 4294967295)", "outsideAllocation"));
    claims.Add(Fault($"Examples.reference, {sourceArgument}, .scalar (.i32 1)", "unwritable", "{ memory with views := [⟨1, 0, 16, true, true⟩] }"));
    claims.Add(Fault($".reference .null, {sourceArgument}, .scalar (.i32 1)", "nullDereference"));
    claims.Add(Fault($"Examples.reference, {sourceArgument}, .scalar (.i32 1)", "expiredLifetime", "{ memory with allocations := fun _ => some ⟨.callerStack, ⟨16, 8, []⟩, false, []⟩ }"));
    claims.Add(Fault($"Examples.reference, {sourceArgument}, .scalar (.i32 1)", "unsupportedLayout", "{ memory with allocations := fun _ => some ⟨.callerStack, ⟨16, 8, [(0, 8)]⟩, true, []⟩ }"));
    claims.Add(Fault($"Examples.reference, {sourceArgument}, .scalar (.i32 1)", "unwritable", "{ memory with allocations := fun _ => some ⟨.immutableStatic, ⟨16, 8, []⟩, true, []⟩ }"));
    if (alignment > 1)
        claims.Add(Fault($".reference (.address ⟨0, 1⟩), {sourceArgument}, .scalar (.i32 1)", "alignment"));
    if (copy)
    {
        claims.Add(Fault($"Examples.reference, {sourceArgument}, .scalar (.i32 1)", "uninitialized", "{ memory with cells := fun _ _ => ⟨0, false⟩ }"));
        claims.Add(Fault($"Examples.reference, {sourceArgument}, .scalar (.i32 1)", "unreadable", "{ memory with views := [⟨0, 0, 16, true, true⟩] }"));
        foreach (var start in new[] { 0, 1 })
            claims.Add($"({Invoke($"Examples.reference, .reference (.address ⟨0, {start}⟩), .scalar (.i32 2)")}).map Prod.snd = .error ⟨0, {(alignment is 1 or 2 or 4 ? 4 : 3)}, .unsupported \"Overlapping block copy\"⟩");
    }
    var emptySource = copy ? ".reference .null" : ".scalar (.i32 0)";
    if (copy) move!(ref Unsafe.NullRef<byte>(), ref Unsafe.NullRef<byte>(), 0);
    else fill!(ref Unsafe.NullRef<byte>(), 0, 0);
    claims.Add($"({Invoke($".reference .null, {emptySource}, .scalar (.i32 0)")}).map Prod.snd = .ok []");
    if (!copy && alignment == 0)
        claims.Add("(CIL.Safety.memoryInstruction (.initBlock 1) [.scalar (.i32 1), .scalar (.i32 4660), Examples.reference] memory).map (fun (m, _) => (m.cells 0 0).bits.toNat) = .ok 52");
    Prove(dll, selector, name, claims);
}

verification.Verify(assembly, "Examples", "Blocks::Fill(byte&,byte,uint)",
    At("Examples/Proofs/BlockOverrun.lean"), Path.Combine(root, "Overrun"));

// Ordinary typed/indirect accesses retain their checked memory semantics with prefixes.
foreach (var alignment in new byte[] { 1, 2, 4 })
foreach (var typed in new[] { false, true })
foreach (var store in new[] { false, true })
{
    var name = $"Access{alignment}-{typed}-{store}";
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Blocks").Methods.Single(m => m.Name == "Fill");
        method.ReturnType = module.TypeSystem.UInt32;
        method.Parameters.RemoveAt(2);
        method.Parameters.RemoveAt(1);
        var code = method.Body.Instructions;
        code.Clear();
        if (store)
        {
            code.Add(Instruction.Create(OpCodes.Ldarg_0));
            code.Add(Instruction.Create(OpCodes.Ldc_I4, 0x11223344));
            code.Add(Instruction.Create(OpCodes.Unaligned, alignment));
            code.Add(typed ? Instruction.Create(OpCodes.Stobj, module.TypeSystem.UInt32) : Instruction.Create(OpCodes.Stind_I4));
        }
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        code.Add(Instruction.Create(OpCodes.Unaligned, alignment));
        code.Add(typed ? Instruction.Create(OpCodes.Ldobj, module.TypeSystem.UInt32) : Instruction.Create(OpCodes.Ldind_U4));
        code.Add(Instruction.Create(OpCodes.Ret));
        selector = method.FullName;
        module.Write(dll);
    }
    var read = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Blocks")!.GetMethod("Fill")!.CreateDelegate<ReadBlock>();
    var bytes = Enumerable.Repeat((byte)165, 16).ToArray();
    var value = read(ref bytes[alignment]);
    Prove(dll, selector, name,
        [$"(CIL.Safety.invoke Extracted.program 16 0 [.reference (.address ⟨0, {alignment}⟩)] memory).map Prod.snd = .ok [.scalar (.i32 {value})]",
         $"(CIL.Safety.invoke Extracted.program 16 0 [.reference (.address ⟨0, {alignment}⟩)] memory).map (fun (m, _) => (List.range 16).map (fun i => (m.cells 0 i).bits.toNat)) = .ok [{string.Join(", ", bytes)}]"]);
}

// Prefixes are attached to instructions; control flow cannot bypass them.
foreach (var mutation in new[] { "zero", "three", "eight", "target", "duplicate", "branch", "switch", "count64", "native-count", "value64" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Blocks").Methods.Single(m => m.Name == "Fill");
        var call = method.Body.Instructions.Single(i => i.OpCode.Code == Code.Call);
        call.OpCode = OpCodes.Initblk;
        call.Operand = null;
        var prefix = Instruction.Create(OpCodes.Unaligned, (byte)(mutation switch { "zero" => 0, "three" => 3, "eight" => 8, _ => 1 }));
        var il = method.Body.GetILProcessor();
        il.InsertBefore(call, prefix);
        switch (mutation)
        {
            case "target": il.InsertAfter(prefix, Instruction.Create(OpCodes.Nop)); break;
            case "duplicate": il.InsertBefore(prefix, Instruction.Create(OpCodes.Unaligned, (byte)1)); break;
            case "branch": il.InsertBefore(prefix, Instruction.Create(OpCodes.Br, call)); break;
            case "switch": il.InsertBefore(prefix, Instruction.Create(OpCodes.Switch, new[] { call })); break;
            case "count64": method.Parameters[2].ParameterType = module.TypeSystem.UInt64; break;
            case "native-count": method.Parameters[2].ParameterType = module.TypeSystem.UIntPtr; break;
            case "value64": method.Parameters[1].ParameterType = module.TypeSystem.UInt64; break;
        }
        selector = method.FullName;
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", selector, output));
    var expected = mutation is "branch" or "switch" ? "Branch enters" :
        mutation is "count64" or "native-count" or "value64" ? "Unsupported block memory operand types" : "malformed unaligned prefix";
    if (result.Code == 0 || !result.Output.Contains(expected) || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Incorrect block metadata rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}

Console.WriteLine($"PASS {cases} block memory checks and universal overrun rejection");

delegate void FillBlock(ref byte destination, byte value, uint count);
delegate void CopyBlock(ref byte destination, ref byte source, uint count);
delegate uint ReadBlock(ref byte source);
