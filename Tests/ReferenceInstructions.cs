#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AllowUnsafeBlocks=true
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var root = At("artifacts/ReferenceInstructions");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
var assembly = Path.Combine(root, "Examples.dll");
var cases = new[]
{
    (Name: "ReferenceEqual", Arguments: 1, Expected: 1),
    (Name: "ObjectNullEqual", Arguments: 0, Expected: 1),
    (Name: "NullBranch", Arguments: 0, Expected: 1),
    (Name: "LiveBranch", Arguments: 1, Expected: 1),
    (Name: "EqualBranch", Arguments: 1, Expected: 1),
    (Name: "UnequalBranch", Arguments: 2, Expected: 1)
};
var additions = new[]
{
    (Name: "Offset32Reference", Native: false, Pointer: false),
    (Name: "OffsetNativeReference", Native: true, Pointer: false),
    (Name: "Offset32Pointer", Native: false, Pointer: true),
    (Name: "OffsetNativePointer", Native: true, Pointer: true)
};

// Emit real CLI bodies so compiler folding cannot remove the opcodes under test.
using (var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
{
    var type = new TypeDefinition("Examples", "ReferenceInstructions",
        Mono.Cecil.TypeAttributes.Public | Mono.Cecil.TypeAttributes.Abstract |
        Mono.Cecil.TypeAttributes.Sealed, module.TypeSystem.Object);
    module.Types.Add(type);
    foreach (var (name, arguments, _) in cases)
    {
        var method = new MethodDefinition(name,
            Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
        for (var index = 0; index < arguments; index++)
            method.Parameters.Add(new ParameterDefinition(new ByReferenceType(module.TypeSystem.Int32)));
        type.Methods.Add(method);
        var il = method.Body.GetILProcessor();
        il.Emit(arguments == 0 ? OpCodes.Ldnull : OpCodes.Ldarg_0);
        if (name is "ReferenceEqual" or "ObjectNullEqual" or "EqualBranch" or "UnequalBranch")
            il.Emit(name == "ObjectNullEqual" ? OpCodes.Ldnull :
                name == "UnequalBranch" ? OpCodes.Ldarg_1 : OpCodes.Ldarg_0);
        if (name is "ReferenceEqual" or "ObjectNullEqual")
            il.Emit(OpCodes.Ceq);
        else
        {
            var success = Instruction.Create(OpCodes.Ldc_I4_1);
            il.Emit(name switch
            {
                "NullBranch" => OpCodes.Brfalse,
                "LiveBranch" => OpCodes.Brtrue,
                "EqualBranch" => OpCodes.Beq,
                _ => OpCodes.Bne_Un
            }, success);
            il.Emit(OpCodes.Ldc_I4_0);
            il.Emit(OpCodes.Ret);
            il.Append(success);
        }
        il.Emit(OpCodes.Ret);
    }
    foreach (var (name, native, pointer) in additions)
        AddOffset(name, native ? module.TypeSystem.IntPtr : module.TypeSystem.Int32,
            pointer, OpCodes.Add);
    AddOffset("InvalidInt64Offset", module.TypeSystem.Int64, true, OpCodes.Add);
    AddOffset("InvalidReferenceSum", new ByReferenceType(module.TypeSystem.Int64), false, OpCodes.Add);
    AddOffset("InvalidReversedSubtract", module.TypeSystem.Int32, true, OpCodes.Sub);

    void AddOffset(string name, TypeReference offset, bool pointer, OpCode operation)
    {
        var method = new MethodDefinition(name,
            Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
        method.Parameters.Add(new ParameterDefinition(offset));
        method.Parameters.Add(new ParameterDefinition(pointer ? new PointerType(module.TypeSystem.Byte) :
            new ByReferenceType(module.TypeSystem.Int64)));
        type.Methods.Add(method);
        var body = method.Body.GetILProcessor();
        body.Emit(OpCodes.Ldarg_0);
        body.Emit(OpCodes.Ldarg_1);
        body.Emit(operation);
        body.Emit(OpCodes.Ldind_U1);
        body.Emit(OpCodes.Ret);
    }

    var throws = new MethodDefinition("NullMessageThrow",
        Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
    type.Methods.Add(throws);
    var original = (MethodReference)module.GetType("Examples.Throws").Methods
        .Single(method => method.Name == "ThrowDivideByZero").Body.Instructions[0].Operand;
    var constructor = new MethodReference(".ctor", module.TypeSystem.Void, original.DeclaringType)
        { HasThis = true };
    constructor.Parameters.Add(new ParameterDefinition(module.TypeSystem.String));
    var throwBody = throws.Body.GetILProcessor();
    throwBody.Emit(OpCodes.Ldnull);
    throwBody.Emit(OpCodes.Newobj, constructor);
    throwBody.Emit(OpCodes.Throw);
    module.Write(assembly);
}

var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.ReferenceInstructions")!;
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.Safety.Execution", "Tests.ReferenceTests");
foreach (var (name, count, expected) in cases)
{
    var inputs = Enumerable.Range(0, count).Select(index => (object)(index + 1)).ToArray();
    if (!Equals(runtime.GetMethod(name)!.Invoke(null, inputs), expected))
        throw new Exception("Unexpected runtime reference result: " + name);
    var output = Path.Combine(root, name);
    var signature = string.Join(',', Enumerable.Repeat("System.Int32&", count));
    Run(["dotnet", ExtractorPath, "extract", assembly, $"ReferenceInstructions::{name}({signature})", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var arguments = string.Join(", ", Enumerable.Range(0, count)
        .Select(index => $".reference (.address ⟨0, {index * 4}⟩)"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨8, 1, []⟩, true, []⟩ else none
          cells := fun _ _ => ⟨0, false⟩
          views := []
          nextIdentity := 1 }
        theorem reference_result :
            CIL.Safety.invoke Extracted.program 16 0 [{{arguments}}] inputMemory =
              .ok (inputMemory, [.scalar (.i32 {{expected}})]) := rfl
        #print axioms reference_result
        """);
    if (name == "ReferenceEqual")
    {
        var narrowed = NarrowEvidence(source, "method0_scalars_validated");
        File.AppendAllText(proof, "\n" + CheckedEvidenceControl(source, narrowed, ["method0_scalars_validated"], 0));
        if (!narrowed.Contains(".eq", StringComparison.Ordinal)) throw new Exception("Missing equality mutation target");
        var forged = Path.Combine(root, "ForgedEquality.lean");
        File.WriteAllText(forged, narrowed.Replace(".eq", ".lt", StringComparison.Ordinal));
        rejected.Add(forged, "PASS independent forged reference equality rejection", "ScalarFlowValid");
    }
    evidence.Add(proof, "PASS runtime, certificate and reference execution: " + name);
}

string AdditionSignature(string name, bool native, bool pointer) =>
    $"ReferenceInstructions::{name}({(native ? "System.IntPtr" : "System.Int32")}," +
    (pointer ? "System.Byte*)" : "System.Int64&)");
ExtractBatch("extract", null, additions.Select(item => new GeneratedExtraction(assembly,
    AdditionSignature(item.Name, item.Native, item.Pointer), Path.Combine(root, item.Name))));
foreach (var (name, native, pointer) in additions)
{
    var method = runtime.GetMethod(name)!;
    foreach (var (origin, offset, expected) in new[] { (0, 0, 1), (0, 1, 2), (0, 7, 8), (4, -1, 4) })
    {
        unsafe
        {
            long value = 0x0807060504030201;
            object count = native ? (object)(nint)offset : offset;
            ref var reference = ref System.Runtime.CompilerServices.Unsafe.AddByteOffset(ref value, (nint)origin);
            var actual = pointer ? method.Invoke(null, [count, Pointer.Box((byte*)&value + origin, typeof(byte*))]) :
                native ? method.CreateDelegate<NativeOffset>()((nint)offset, ref reference) :
                method.CreateDelegate<Int32Offset>()(offset, ref reference);
            if (!Equals(actual, expected))
                throw new Exception("Unexpected runtime commuted addition: " + name);
        }
    }
    var source = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
          cells := fun _ offset => ⟨BitVec.ofNat 8 (offset + 1), true⟩
          views := [⟨0, 0, 8, true, false⟩]
          nextIdentity := 1 }
        theorem commuted_reference_result :
            ([(0, 0, 1), (0, 1, 2), (0, 7, 8), (4, -1, 4)] : List (Nat × Int × Nat)).all
              (fun (origin, offset, expected) =>
                ((CIL.Safety.invoke Extracted.program 16 0
                  [.scalar (.i{{(native ? 64 : 32)}} (BitVec.ofInt {{(native ? 64 : 32)}} offset)),
                    .reference (.address ⟨0, origin⟩)] inputMemory).map Prod.snd).toOption ==
                  some [.scalar (.i32 (BitVec.ofNat 32 expected))]) = true :=
          by decide +kernel
        #print axioms commuted_reference_result
        """);
    if (name == "Offset32Reference")
    {
        var narrowed = NarrowEvidence(source, "method0_scalars_validated");
        File.AppendAllText(proof, "\n" + CheckedEvidenceControl(source, narrowed, ["method0_scalars_validated"], 0));
        const string target = ".memory (.add 1 true)";
        foreach (var (mutation, replacement) in new[]
        {
            ("scalar", ".add"), ("subtract", ".sub"),
            ("stride", ".memory (.add 2 true)"), ("unsigned", ".memory (.add 1 false)")
        })
        {
            if (!narrowed.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing commuted add target");
            var forged = Path.Combine(root, "ForgedAdd-" + mutation + ".lean");
            File.WriteAllText(forged, narrowed.Replace(target, replacement, StringComparison.Ordinal));
            rejected.Add(forged, "PASS independent forged commuted addition: " + mutation, "ScalarFlowValid");
        }
    }
    evidence.Add(proof, "PASS runtime, certificate and commuted reference addition: " + name);
}
foreach (var signature in new[]
{
    "InvalidInt64Offset(System.Int64,System.Byte*)", "InvalidReferenceSum(System.Int64&,System.Int64&)",
    "InvalidReversedSubtract(System.Int32,System.Byte*)"
})
{
    var rejection = Execute(["dotnet", ExtractorPath, "extract", assembly,
        "ReferenceInstructions::" + signature, Path.Combine(root, "InvalidAdd")]);
    if (rejection.Code == 0 || !rejection.Output.Contains("Unsupported reference arithmetic operand types",
            StringComparison.Ordinal))
        throw new Exception("Expected reference arithmetic rejection: " + signature + "\n" + rejection.Output);
    Console.WriteLine("PASS invalid reference arithmetic rejected: " + signature);
}

try
{
    runtime.GetMethod("NullMessageThrow")!.Invoke(null, null);
    throw new Exception("Null-message exception fixture returned");
}
catch (TargetInvocationException exception) when (exception.InnerException is DivideByZeroException) { }
var throwOutput = Path.Combine(root, "NullMessageThrow");
Run(["dotnet", ExtractorPath, "extract", assembly, "ReferenceInstructions::NullMessageThrow()", throwOutput]);
var throwSource = File.ReadAllText(Path.Combine(throwOutput, "Extracted.lean"));
var throwProof = Path.Combine(root, "NullMessageThrow.lean");
File.WriteAllText(throwProof, throwSource + """

    theorem null_message_raises :
        CIL.Safety.invoke Extracted.program 16 0 [] ⟨fun _ => none, fun _ _ => ⟨0, false⟩, [], 0, [], 0⟩ =
          .error ⟨0, 2, .thrown "System.DivideByZeroException"⟩ := rfl
    #print axioms null_message_raises
    """);
evidence.Add(throwProof, "PASS existing null-message throw folding, runtime and certificate");


evidence.Check(replay: false);
rejected.Check();

delegate int Int32Offset(int offset, ref long value);
delegate int NativeOffset(nint offset, ref long value);
