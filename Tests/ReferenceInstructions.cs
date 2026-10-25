#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var root = At("artifacts/ReferenceInstructions");
Directory.CreateDirectory(root);
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
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.Safety.Execution", "Tests.ReferenceTests"]);
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
    var result = Run(["lake", "env", "lean", proof]);
    if (result.Contains("sorryAx", StringComparison.Ordinal)) throw new Exception("Untrusted reference proof");
    Console.WriteLine("PASS runtime, certificate and reference execution: " + name);
    if (name != "ReferenceEqual") continue;
    if (!source.Contains(".eq", StringComparison.Ordinal)) throw new Exception("Missing equality mutation target");
    var forged = Path.Combine(root, "ForgedEquality.lean");
    File.WriteAllText(forged, source.Replace(".eq", ".lt", StringComparison.Ordinal));
    var rejection = Execute(["lake", "env", "lean", forged]);
    if (rejection.Code == 0 || !rejection.Output.Contains("ScalarFlowValid", StringComparison.Ordinal))
        throw new Exception("Forged reference equality was not rejected by scalar evidence: " + rejection.Output);
    Console.WriteLine("PASS independent forged reference equality rejection");
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
var throwResult = Run(["lake", "env", "lean", throwProof]);
if (throwResult.Contains("sorryAx", StringComparison.Ordinal)) throw new Exception("Untrusted throw proof");
Console.WriteLine("PASS existing null-message throw folding, runtime and certificate");

