#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AssemblyName=LeanCIL.IdentityTests
#:project ../Extractor/Extractor.csproj
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include GeneratedEvidence.cs

extern alias IdentityExtractor;

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;
using IdentityExtractor::Nethermind.LeanCIL;

CheckPrefixes();

// The extractor predicts which methods Lean's decoder defines from its own opcode table. Lean decides that the
// table holds exactly the opcodes of `Instruction.valueOpcode`, so the prediction cannot drift from the decoder.
var opcodes = typeof(OpCodes).GetFields(BindingFlags.Public | BindingFlags.Static)
    .Select(field => (OpCode)field.GetValue(null)!).ToArray();
var table = opcodes.Where(opcode => GenericEvidence.DecodedOpcodes.Contains(opcode.Code))
    .Select(opcode => (ushort)opcode.Value).Order().ToArray();
if (table.Length != GenericEvidence.DecodedOpcodes.Count)
    throw new InvalidOperationException("A decoded opcode has no Cecil opcode value.");
var directory = At("artifacts/DecodedOpcodes");
Directory.CreateDirectory(directory);
var path = Path.Combine(directory, "Table.lean");
File.WriteAllText(path, $$"""
    import CIL.Extraction.ValueDecoding

    /-- The opcodes the extractor predicts `Instruction.ofRaw?` decodes. -/
    def table : List Nat := [{{string.Join(", ", table)}}]

    /-- Every one-byte opcode and every two-byte opcode `0xFE nn`, numbered as raw instructions are. -/
    def opcodes : List Nat := List.range 256 ++ (List.range 256).map (65024 + ·)

    /-- The table holds an opcode exactly when `Instruction.valueOpcode` does. -/
    theorem table_is_valueOpcode :
        (opcodes.all fun opcode =>
          CIL.Instruction.valueOpcode opcode == table.contains opcode) = true := by
      decide +kernel
    #print axioms table_is_valueOpcode
    """ + "\n");
Run(["lake", "env", "lean", path], cwd: FixturePackage());
Console.WriteLine($"PASS the extractor's {table.Length} decoded opcodes are those of Instruction.valueOpcode");

// The decoder reads every pc, but the feature check requires a hole at each pc the reachability certificate rules
// out, so a body of decoded opcodes with an unreachable tail must keep its literal and still build.
var deadDirectory = Path.Combine(directory, "UnreachableTail");
Directory.CreateDirectory(deadDirectory);
var deadAssembly = Path.Combine(deadDirectory, "Examples.dll");
// The examples assembly carries the identity and target framework extraction admits.
using (var module = Mono.Cecil.ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
{
    var owner = new Mono.Cecil.TypeDefinition("Examples", "UnreachableTail", Mono.Cecil.TypeAttributes.Public |
        Mono.Cecil.TypeAttributes.Abstract | Mono.Cecil.TypeAttributes.Sealed, module.TypeSystem.Object);
    module.Types.Add(owner);
    var method = new Mono.Cecil.MethodDefinition("One",
        Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
    owner.Methods.Add(method);
    var il = method.Body.GetILProcessor();
    foreach (var opcode in new[] { OpCodes.Ldc_I4_1, OpCodes.Ret, OpCodes.Ldc_I4_0, OpCodes.Ret }) il.Emit(opcode);
    var hash = new MethodReference("GetHashCode", module.TypeSystem.Int32, module.TypeSystem.Object)
        { HasThis = true };
    il.Emit(OpCodes.Ldnull);
    il.Emit(OpCodes.Tail);
    il.Emit(OpCodes.Callvirt, hash);
    il.Emit(OpCodes.Ret);
    module.Write(deadAssembly);
}
var deadOutput = Path.Combine(deadDirectory, "Extraction");
Run(["dotnet", ExtractorPath, "extract", deadAssembly, "UnreachableTail::One()", deadOutput]);
var deadSource = Path.Combine(deadOutput, "Extracted.lean");
var deadText = File.ReadAllText(deadSource).ReplaceLineEndings("\n");
string[] literal = [.. ExtractedInstructions(deadText).Where(instruction => instruction.Method == 0)
    .Select(instruction => instruction.Op)];
string[] expectedLiteral =
    [".ldc_i4 1", ".ret", $".unadmitted {OpCodes.Ldc_I4_0.Value}", $".unadmitted {OpCodes.Ret.Value}",
        $".unadmitted {OpCodes.Ldnull.Value}", $".unadmitted {(ushort)OpCodes.Tail.Value}",
        $".unadmitted {OpCodes.Callvirt.Value}", $".unadmitted {OpCodes.Ret.Value}"];
if (IsDecodedMethod(deadText, 0) ||
    !literal.SequenceEqual(expectedLiteral, StringComparer.Ordinal))
    throw new InvalidOperationException("A method with an unreachable tail must keep its literal with a hole " +
        "at each dead pc, found:\n" + string.Join('\n', literal));
Run(["lake", "env", "lean", deadSource], cwd: FixturePackage());
Console.WriteLine("PASS a method with an unreachable tail keeps its literal, with holes at its dead pcs, and builds");

static void CheckPrefixes()
{
    var bytes = File.ReadAllBytes(At("Examples/Assembly/bin/Examples.dll"));
    var hash = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes));
    using var pinned = new PinnedAssemblies(bytes, hash, []);
    var module = pinned.Selected;
    var method = new MethodDefinition("Body", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
    var element = module.TypeSystem.Int32;
    static Instruction Raw(OpCode opcode, object? operand = null)
    {
        var instruction = Instruction.Create(OpCodes.Nop);
        instruction.OpCode = opcode;
        instruction.Operand = operand;
        return instruction;
    }

    void Check(bool accepted, params Instruction[] sequence)
    {
        method.Body.Instructions.Clear();
        foreach (var instruction in sequence) method.Body.Instructions.Add(instruction);
        try { InstructionPrefixes.Validate(method); }
        catch (InvalidDataException) when (!accepted) { return; }
        if (!accepted)
        {
            var opcodes = string.Join(" ", sequence.Select(instruction => instruction.OpCode.Name));
            throw new InvalidOperationException($"Accepted prefix sequence {opcodes}");
        }
    }

    foreach (var alignment in new byte[] { 1, 2, 4 })
        Check(true, Raw(OpCodes.Unaligned, alignment), Raw(OpCodes.Ldind_I4));
    Check(true, Raw(OpCodes.Readonly), Raw(OpCodes.Ldelema, element));
    Check(true, Raw(OpCodes.Tail), Raw(OpCodes.Call, method), Raw(OpCodes.Ret));
    Check(true, Raw(OpCodes.Tail), Raw(OpCodes.Calli, new CallSite(method.ReturnType)), Raw(OpCodes.Ret));
    var receiver = module.GetType("Examples.StepOn");
    var slot = module.GetType("Examples.IStepFlag").Properties.Single().GetMethod;
    Check(false, Raw(OpCodes.Ret), Raw(OpCodes.Constrained, element), Raw(OpCodes.Call, method));
    Check(true, Raw(OpCodes.Constrained, receiver), Raw(OpCodes.Call, slot));
    Check(false, Raw(OpCodes.Ret), Raw(OpCodes.Tail), Raw(OpCodes.Calli, new CallSite(element)), Raw(OpCodes.Ret));
    Check(false, Raw(OpCodes.Ret), Raw(OpCodes.Tail), Raw(OpCodes.Call, slot), Raw(OpCodes.Ret));
    var instance = new MethodReference("Instance", element, element) { HasThis = true };
    Check(true, Raw(OpCodes.Constrained, element), Raw(OpCodes.Callvirt, instance));
    var virtualVoid = new MethodReference("Visit", method.ReturnType, element) { HasThis = true };
    Check(true, Raw(OpCodes.Ret), Raw(OpCodes.Tail), Raw(OpCodes.Callvirt, virtualVoid), Raw(OpCodes.Ret));
    try
    {
        TailCalls.ValidateReachable(method, method.Body.Instructions[1]);
        throw new InvalidOperationException("Accepted a reachable virtual tail transfer");
    }
    catch (InvalidDataException error) when (error.Message.StartsWith("Unsupported tail prefix:",
        StringComparison.Ordinal)) { }
    foreach (var flags in Enumerable.Range(0, 256))
        Check(false, Raw(OpCodes.No, (byte)flags), Raw(OpCodes.Ldelem_I4));
    Check(false, Raw(OpCodes.Ret), Raw(OpCodes.No, (byte)255), Raw(OpCodes.Add));
    Check(false, Raw(OpCodes.Volatile), Raw(OpCodes.Ldind_I4));
    Check(false, Raw(OpCodes.Ret), Raw(OpCodes.Volatile), Raw(OpCodes.Ldsfld));
    Check(false, Raw(OpCodes.Unaligned, (byte)3), Raw(OpCodes.Ldfld));
    Check(false, Raw(OpCodes.Unaligned), Raw(OpCodes.Ldind_I4));
    Check(false, Raw(OpCodes.Unaligned, (byte)1), Raw(OpCodes.Add));
    Check(false, Raw(OpCodes.Unaligned, (byte)1), Raw(OpCodes.Cpblk, 1));
    Check(false, Raw(OpCodes.Unaligned, (byte)1), Raw(OpCodes.Ldind_I4, 1));
    Check(false, Raw(OpCodes.Readonly, 3), Raw(OpCodes.Ldelema, element));
    Check(false, Raw(OpCodes.Readonly), Raw(OpCodes.Add));
    Check(false, Raw(OpCodes.Constrained), Raw(OpCodes.Call, method));
    Check(false, Raw(OpCodes.Constrained, element), Raw(OpCodes.Call, instance));
    Check(false, Raw(OpCodes.Constrained, element), Raw(OpCodes.Add));
    Check(false, Raw(OpCodes.Tail, 1), Raw(OpCodes.Call, method), Raw(OpCodes.Ret));
    Check(false, Raw(OpCodes.Tail), Raw(OpCodes.Add));
    Check(false, Raw(OpCodes.Tail), Raw(OpCodes.Call, method));
    foreach (var opcode in new[] { OpCodes.Unaligned, OpCodes.Tail, OpCodes.Constrained, OpCodes.Readonly })
        Check(false, Raw(opcode));
    Check(false, Raw(OpCodes.Readonly), Raw(OpCodes.Readonly), Raw(OpCodes.Ldelema, element));
    Check(false, Raw(OpCodes.Unaligned, (byte)1), Raw(OpCodes.Volatile), Raw(OpCodes.Ldind_I4));
    Console.WriteLine("PASS extractor prefix operands, takers and adjacency");
}
