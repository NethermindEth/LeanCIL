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

// A dead tail includes a raw prefix and virtual call. Both retain their opcode at the original pc.
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
    var frame = new MethodDefinition("Frame", Mono.Cecil.MethodAttributes.Public |
        Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
    owner.Methods.Add(frame);
    var array = new ParameterDefinition(new ArrayType(module.TypeSystem.Int32));
    frame.Parameters.Add(array);
    var vector = new MethodDefinition("VectorLocal", Mono.Cecil.MethodAttributes.Public |
        Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
    owner.Methods.Add(vector);
    var unsafeReturn = module.GetType("Examples.DivisionIntrinsics").Methods
        .Single(candidate => candidate.Name == "UnsafeReturn");
    var create = (MethodReference)unsafeReturn.Body.Instructions.Single(op => op.OpCode == OpCodes.Call).Operand;
    vector.Body.Variables.Add(new VariableDefinition(unsafeReturn.ReturnType));
    var constructor = new MethodReference(".ctor", module.TypeSystem.Void, module.TypeSystem.Object)
        { HasThis = true };
    var body = frame.Body.GetILProcessor();
    body.Emit(OpCodes.Ldarg_0);
    body.Emit(OpCodes.Starg_S, array);
    body.Emit(OpCodes.Call, vector);
    body.Emit(OpCodes.Ret);
    body.Emit(OpCodes.Ldarga_S, array);
    body.Emit(OpCodes.Pop);
    body.Emit(OpCodes.Ret);
    body = vector.Body.GetILProcessor();
    body.Emit(OpCodes.Ret);
    body.Emit(OpCodes.Ldc_I8, 0L);
    body.Emit(OpCodes.Call, create);
    body.Emit(OpCodes.Pop);
    body.Emit(OpCodes.Newobj, constructor);
    body.Emit(OpCodes.Pop);
    body.Emit(OpCodes.Ret);
    module.Write(deadAssembly);
}
var deadOutput = Path.Combine(deadDirectory, "Extraction");
Run(["dotnet", ExtractorPath, "extract", deadAssembly, "UnreachableTail::One()", deadOutput]);
var deadSource = Path.Combine(deadOutput, "Extracted.lean");
var deadText = File.ReadAllText(deadSource).ReplaceLineEndings("\n");
RequireDecoded(deadText, "UnreachableTail::One");
File.AppendAllText(deadSource, """

    namespace Extracted
    open CIL CIL.Extraction

    /-- Every excluded instruction retains its raw opcode, including both bytes of the prefix. -/
    theorem dead_tail : method0.code = [.ldc_i4 1, .ret, .unadmitted 22, .unadmitted 42,
        .unadmitted 20, .unadmitted 65044, .unadmitted 111, .unadmitted 42] := rfl
    #print axioms dead_tail

    /-- A mask that excludes the entry instruction. -/
    def hidden : List Bool := false :: method0Reachable.tail
    cil_decoded_method forged := Method.ofRaw? profile environment method0Links hidden
      method0Original method0TypeArgumentsRaw

    /-- The entry state in the certificate requires the first instruction to be live. -/
    theorem hidden_entry_rejected : Not (FeatureFlowValid rawLayouts.toArray
        (evidenceConstants methodEvidence) (linkIndex forged) method0Closed profile
        method0FeatureStates hidden forged.code) := by decide +kernel
    #print axioms hidden_entry_rejected
    end Extracted

    """);
Run(["lake", "env", "lean", deadSource], cwd: FixturePackage());
Console.WriteLine("PASS the decoded tail preserves its holes and the feature check rejects a hidden entry");

var frameOutput = Path.Combine(deadDirectory, "Frame");
Run(["dotnet", ExtractorPath, "extract", deadAssembly, "UnreachableTail::Frame(int[])", frameOutput]);
var framePath = Path.Combine(frameOutput, "Extracted.lean");
var frames = File.ReadAllText(framePath);
RequireDecoded(frames, "UnreachableTail::Frame");
RequireDecoded(frames, "UnreachableTail::VectorLocal", 1);
File.AppendAllText(framePath, """

    namespace Extracted
    open CIL CIL.Extraction

    /-- The live store homes the array. Its dead address and the dead vector call are holes. -/
    theorem dead_frame :
        (method0.parameterHomes, method1.localKinds, method1.opaqueVectorLocals,
          method0.code[4]?, method1.code[2]?, method1.code[4]?) =
        ([(0, .array .signed32)], [.vector128], [], some (.unadmitted 15),
          some (.unadmitted 40), some (.unadmitted 115)) := rfl
    #print axioms dead_frame

    /-- A link at the dead runtime call or the dead construction fails the call check. -/
    theorem dead_links :
        let fits := fun (method : Method) => ManagedCallsValid specializedMethods imports
          (callModelled method) method1Closed method1Reachable method
        And (fits method1) (And (Not (fits { method1 with links := [(2, .direct 999)] }))
          (Not (fits { method1 with links := [(4, .direct 0)] }))) := by decide +kernel
    #print axioms dead_links
    end Extracted

    """);
Run(["lake", "env", "lean", framePath], cwd: FixturePackage());
Console.WriteLine("PASS dead argument addresses, vector calls and constructions preserve the frame and reject links");

var examples = At("Examples/Assembly/bin/Examples.dll");
var getter = Path.Combine(directory, "Both");
var trace = Path.Combine(directory, "Trace");
var shared = Path.Combine(directory, "Templates");
Run(["dotnet", ExtractorPath, "extract", examples, "ComputedFlags::get_Both()", getter]);
Run(["dotnet", ExtractorPath, "extract", examples, "ComputedFlags::TraceGated(ulong)", trace]);
RequireDecoded(File.ReadAllText(Path.Combine(getter, "Extracted.lean")), "ComputedFlags::get_Both");
RequireDecoded(File.ReadAllText(Path.Combine(trace, "Extracted.lean")), "ComputedFlags::TraceGated");
Run(["dotnet", ExtractorPath, "templates", shared, getter]);
var searchPath = string.Join(Path.PathSeparator, getter, shared, FixtureLeanPath());
foreach (var (root, name) in new[] { (getter, "Extracted"), (shared, "Templates"), (shared, "TemplateBindings0") })
{
    var result = Run(["lean", $"--root={root}", "-o", Path.Combine(root, $"{name}.olean"),
        Path.Combine(root, $"{name}.lean")], leanPath: searchPath);
    if (result.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException($"Admitted declaration in {name}.");
}
Run(["lake", "env", "lean", Path.Combine(trace, "Extracted.lean")], cwd: FixturePackage());
Console.WriteLine("PASS get_Both binds to its template and TraceGated's frame checks");

static void RequireDecoded(string source, string name, int number = 0)
{
    if (!IsDecodedMethod(source, number)) throw new InvalidOperationException($"{name} must decode.");
}

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
