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
    import CIL.Extraction.Folds

    /-! The extractor opcode table and folded instructions against the Lean decoder. -/

    open CIL CIL.Extraction

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

    /-- The instruction selected by a recognized role at its raw pc. -/
    private def folded (code : List RawInstruction) (pc : Nat) : Option Instruction := do
      let role <- (foldRoles code)[pc]?.join
      let raw <- code[pc]?
      Instruction.ofRole? role (rawBefore (fun i => code[i]?) pc) raw

    /-- All three opcodes are required for the indirect tail transfer. -/
    theorem tail_opcodes :
        let tailPrefix := RawInstruction.mk 0 {{(ushort)OpCodes.Tail.Value}} .none
        let indirect := RawInstruction.mk 2 {{OpCodes.Calli.Value}} (.indirectCall .void [] false false 0)
        let code := [tailPrefix, indirect, RawInstruction.mk 7 {{OpCodes.Ret.Value}} .none]
        let nop := RawInstruction.mk 0 {{OpCodes.Nop.Value}} .none
        foldRoles code == [some .head, some .tailCall, some .argument] &&
          (folded code 0 matches some .nop) && (folded code 1 matches some (.calli _ true)) &&
          ([0, 1, 2].all fun pc =>
            foldRoles (code.set pc nop) == List.replicate 3 none) := by
      decide +kernel
    #print axioms tail_opcodes

    /-- A null throw needs both the null load and the throw opcode. -/
    theorem throw_opcodes :
        let loadNull := RawInstruction.mk 0 {{OpCodes.Ldnull.Value}} .none
        let raise := RawInstruction.mk 1 {{OpCodes.Throw.Value}} .none
        let code := [loadNull, raise]
        let nop := RawInstruction.mk 0 {{OpCodes.Nop.Value}} .none
        foldRoles code == [none, none] &&
          (Instruction.ofRaw? none loadNull matches some .ldnull) &&
          (Instruction.ofRaw? (some loadNull) raise matches some (.throw none)) &&
          (Instruction.ofRaw? none nop matches some .nop) := by
      decide +kernel
    #print axioms throw_opcodes

    """ + "\n");
CheckLean(path);
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
    var deadArray = new ParameterDefinition(new ArrayType(module.TypeSystem.Int32));
    frame.Parameters.Add(deadArray);
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
    body.Emit(OpCodes.Ldarga_S, deadArray);
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
    var liveVector = new MethodDefinition("LiveVector", Mono.Cecil.MethodAttributes.Public |
        Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
    owner.Methods.Add(liveVector);
    liveVector.Body.InitLocals = true;
    liveVector.Body.Variables.Add(new VariableDefinition(unsafeReturn.ReturnType));
    body = liveVector.Body.GetILProcessor();
    body.Emit(OpCodes.Ldc_I8, 0L);
    body.Emit(OpCodes.Call, create);
    body.Emit(OpCodes.Stloc_0);
    body.Emit(OpCodes.Ret);
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
CheckLean(deadSource);
Console.WriteLine("PASS the decoded tail preserves its holes and the feature check rejects a hidden entry");

foreach (var (name, selector, method, code) in new[]
{
    ("SameText", "Strings::SameText()", 0,
        """[.ldstr "x", .ldstr "x", .ceq, .ret]"""),
    ("WordFlag", "GenericReceivers::CountWide(ulong)", 2, """
        (let word := CIL.Extraction.TypeExpr.atom CIL.Extraction.runtimeScope "System.UInt64"
         let getType := CIL.Extraction.getTypeFromHandle.method
         [.ldtoken (.type word), .call getType, .ldtoken (.type word), .call getType,
          .call (CIL.Extraction.runtimeTypeComparison true).method, .ret])
        """)
})
{
    var output = Path.Combine(directory, name);
    Run(["dotnet", ExtractorPath, "extract", At("Examples/Assembly/bin/Examples.dll"), selector, output]);
    var pathToSource = Path.Combine(output, "Extracted.lean");
    RequireDecoded(File.ReadAllText(pathToSource), name, method);
    File.AppendAllText(pathToSource, $$"""

        /-- The closed example decodes to its exact instruction sequence. -/
        theorem decoded_code : Extracted.method{{method}}.code = {{code}} := rfl
        #print axioms decoded_code

        """);
    if (name == "WordFlag")
        File.AppendAllText(pathToSource, $$"""

            open CIL CIL.Extraction

            /-- Both type-handle opcodes are required for this closed equality fold. -/
            theorem token_opcodes :
                let code := Extracted.method{{method}}Closed.code
                let token := {{(ushort)OpCodes.Ldtoken.Value}}
                let nop := RawInstruction.mk 0 {{OpCodes.Nop.Value}} .none
                let opcode := fun (pc : Nat) => (code[pc]?).map RawInstruction.opcode
                (opcode 0, opcode 2) == (some token, some token) &&
                  foldRoles code == [some .typeHead, some .typeOperand, some .typeOperand, some .typeOperand,
                    some (.result true), none] &&
                  ([0, 2].all fun pc => foldRoles (code.set pc nop) == List.replicate 6 none) := by
              decide +kernel
            #print axioms token_opcodes

            """);
    CheckLean(pathToSource);
}

CheckClassAddress(directory);
CheckReceiverMethods(directory);

var frameOutput = Path.Combine(deadDirectory, "Frame");
Run(["dotnet", ExtractorPath, "extract", deadAssembly, "UnreachableTail::Frame(int[],int[])", frameOutput]);
var framePath = Path.Combine(frameOutput, "Extracted.lean");
var frames = File.ReadAllText(framePath);
RequireDecoded(frames, "UnreachableTail::Frame");
RequireDecoded(frames, "UnreachableTail::VectorLocal", 1);
File.AppendAllText(framePath, """

    namespace Extracted
    open CIL CIL.Extraction

    /-- Only the live store homes its parameter. The other parameter's dead address is a hole. -/
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
CheckLean(framePath);
Console.WriteLine("PASS dead argument addresses, vector calls and constructions preserve the frame and reject links");

var liveOutput = Path.Combine(deadDirectory, "LiveVector");
Run(["dotnet", ExtractorPath, "extract", deadAssembly, "UnreachableTail::LiveVector()", liveOutput]);
var livePath = Path.Combine(liveOutput, "Extracted.lean");
RequireDecoded(File.ReadAllText(livePath), "UnreachableTail::LiveVector");
var vectorTemplate = Path.Combine(deadDirectory, "VectorTemplate");
Run(["dotnet", ExtractorPath, "templates", vectorTemplate, liveOutput]);
var vectorPath = Path.Combine(vectorTemplate, "Templates.lean");
File.AppendAllText(vectorPath, """

    /-- The decoded template retains the opaque slot needed by live vector creation. -/
    theorem live_vector_template_frame (profile : CIL.FeatureProfile) (environment : CIL.LayoutEnvironment) :
        (Templates.method0 profile environment).opaqueVectorLocals = [0] := rfl
    #print axioms live_vector_template_frame

    """);
CheckLean(vectorPath);
File.AppendAllText(livePath, """

    namespace Extracted
    /-- A live scalar-unsafe creation requires the vector slot even with a dead final return. -/
    theorem live_vector_frame : And (method0.opaqueVectorLocals = [0])
        (And (method0.code[4]? = some (.unadmitted 42))
          (CIL.Extraction.OpaqueLocalsValid method0Closed method0)) :=
      .intro rfl (.intro rfl method0_opaque_validated)
    #print axioms live_vector_frame
    end Extracted

    """);
CheckLean(livePath);

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
CheckLean(Path.Combine(trace, "Extracted.lean"));
Console.WriteLine("PASS get_Both binds to its template and TraceGated's frame checks");

static void CheckLean(string path)
{
    var output = Run(["lake", "env", "lean", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException($"Admitted declaration in {path}.");
}

static void RequireDecoded(string source, string name, int number = 0)
{
    if (!IsDecodedMethod(source, number)) throw new InvalidOperationException($"{name} must decode.");
}

static void CheckClassAddress(string directory)
{
    var bytes = File.ReadAllBytes(At("Examples/Assembly/bin/Examples.dll"));
    var hash = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes));
    using var pinned = new PinnedAssemblies(bytes, hash, []);
    var module = pinned.Selected;
    var definition = new MethodDefinition("M", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
    module.GetType("Examples.Objects").Methods.Add(definition);
    definition.GenericParameters.Add(new GenericParameter("T", definition));
    definition.Body.GetILProcessor().Emit(OpCodes.Ret);
    var address = new GenericInstanceMethod(definition);
    address.GenericArguments.Add(module.GetType("Examples.Account"));
    var target = new MethodSpecialization(module).Instantiate(address);
    var classAddress = Path.Combine(directory, "ClassAddress.lean");
    File.WriteAllText(classAddress, $$"""
        import CIL.Extraction.ValueDecoding

        /-! The literal and decoded identities of a static method specialized at a class. -/
        open CIL CIL.Extraction

        /-- Both paths retain the class argument, excluding the same name encoded as an atom. -/
        theorem class_address_identity :
            let scope := {{System.Text.Json.JsonSerializer.Serialize(module.Assembly.Name.FullName)}}
            let account := TypeExpr.object scope "Examples.Account"
            let site : CallSite := {
              declared := { convention := 0x10 }, name := "M", typeArguments := [account],
              target := .managed {{target.MetadataToken.ToUInt32()}}, parameterCount := 0, returnsValue := false,
              method := {
                owner := .object scope "Examples.Objects", name := name!"M", hasThis := false,
                genericArity := 1, returnType := .void, parameters := [] } }
            let literal : ManagedIdentity := {{ManagedPointers.IdentityEvidence(target)}}
            Instruction.ofRaw? none ⟨0, 0xfe06, .call site⟩ =
                some (.ldftn literal ⟨.void, []⟩) ∧
              literal.arguments ≠ [.atom scope "Examples.Account"] := by
              constructor
              · rfl
              · decide +kernel
        #print axioms class_address_identity
        """);
    CheckLean(classAddress);
}

static void CheckReceiverMethods(string directory)
{
    var assembly = At("Examples/Assembly/bin/Examples.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    (string Owner, string[] Names)[] families =
    [
        ("Objects", ["DepositBoth", "DepositFrom", "DepositTimes"]),
        ("SampleArrays", ["CountAfterDeposit"]),
        ("VirtualCalls", ["DogLegs", "LegsOf", "LoudnessOf"]),
        ("ItemPool", ["Rent"]),
        ("IndirectValues", ["Generic", "Record", "Reference", "Vector"]),
        ("GenericOwners", ["Address"]),
        ("ManagedDispatch", ["LocalEscape"])
    ];
    foreach (var profile in new[] { "scalar", "x64-v3", "arm64-advsimd" })
    {
        var requests = families.SelectMany(family => family.Names.Select(name =>
        {
            var owner = module.GetType($"Examples.{family.Owner}");
            var method = owner.Methods.Single(candidate => candidate.Name == name);
            var output = Path.Combine(directory, profile, family.Owner, name);
            return new GeneratedExtraction(assembly, method.FullName, output, profile);
        })).ToArray();
        ExtractBatch("extract", null, requests);
        foreach (var request in requests)
        {
            var path = Path.Combine(request.Output, "Extracted.lean");
            RequireDecoded(File.ReadAllText(path), request.Entry);
            CheckLean(path);
        }
    }
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
