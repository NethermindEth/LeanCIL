#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var root = At("artifacts/ReadOnlyArrayReferences");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var assembly = Path.Combine(root, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
{
    var type = module.GetType("Examples.ArrayElementReferences");
    var element = type.Methods.Single(method => method.Name == "Element");
    var address = element.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Ldelema);
    element.Body.GetILProcessor().InsertBefore(address, Instruction.Create(OpCodes.Readonly));
    var readReference = new MethodDefinition("ReadReference",
        Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
    readReference.Parameters.Add(new ParameterDefinition(new ByReferenceType(module.TypeSystem.Int32)));
    var helper = readReference.Body.GetILProcessor();
    helper.Emit(OpCodes.Ldarg_0);
    helper.Emit(OpCodes.Ldind_I4);
    helper.Emit(OpCodes.Ret);
    type.Methods.Add(readReference);
    var read = type.Methods.Single(method => method.Name == "Read");
    read.Body.Instructions.Clear();
    read.Body.Variables.Clear();
    read.Body.Variables.Add(new VariableDefinition(new ByReferenceType(module.TypeSystem.Int32)));
    read.Body.InitLocals = true;
    var il = read.Body.GetILProcessor();
    il.Emit(OpCodes.Ldarg_0);
    il.Emit(OpCodes.Ldarg_1);
    il.Emit(OpCodes.Call, element);
    il.Emit(OpCodes.Stloc_0);
    il.Emit(OpCodes.Ldloc_0);
    il.Emit(OpCodes.Call, readReference);
    il.Emit(OpCodes.Ret);
    module.Write(assembly);
}
RequireLeanFixtures("CIL.Extraction.Translation");
CheckLeanFixture("Tests.ReadOnlyArrayReferences");
var runtime = Assembly.LoadFile(assembly).GetType("Examples.ArrayElementReferences")!;
foreach (var name in new[] { "Element", "Read", "Write" })
{
    var write = name == "Write";
    if (!write && !Equals(runtime.GetMethod(name)!.Invoke(null, [new[] { 3, 5 }, 1]), 5))
        throw new Exception("Incorrect runtime readonly read: " + name);
    var signature = "System.Int32[],System.Int32" + (write ? ",System.Int32" : "");
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"ArrayElementReferences::{name}({signature})", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    var extra = write ? ", .scalar (.i32 7)" : "";
    var result = name == "Element" ? ".readOnlyReference (.address ⟨0, 4⟩)" : ".scalar (.i32 5)";
    var observation = write
        ? "false"
        : $"outcome.2 == [{result}] && (outcome.1.cells 0 4).bits == 5";
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.managedHeap, ⟨8, 4, []⟩, true, [8]⟩ else none
          cells := fun _ offset => ⟨if offset == 4 then 5 else 0, true⟩
          views := [⟨0, 0, 8, true, true⟩]
          nextIdentity := 1 }
        theorem readonly_composition :
            (match CIL.Safety.invoke Extracted.program 128 0
              [.array ⟨.address ⟨0, 0⟩, 2, .signed32⟩, .scalar (.i32 1){{extra}}] inputMemory with
             | .ok outcome => {{observation}}
             | .error fault => {{(write ? "fault.fault == .memory .unwritable (.address ⟨0, 4⟩) 4" : "false")}})
              = true := by decide +kernel
        #print axioms readonly_composition
        """);
    evidence.Add(proof, "PASS certified readonly reference composition: " + name);
    if (name != "Element") continue;
    const string target = ".arrayAddress .signed32 false";
    if (!source.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing readonly mutation target");
    var forged = Path.Combine(root, "ForgedWritable.lean");
    File.WriteAllText(forged, source.Replace(target, ".arrayAddress .signed32 true", StringComparison.Ordinal));
    var rejection = Execute(["lake", "env", "lean", forged]);
    if (rejection.Code == 0 || !rejection.Output.Contains("ScalarFlowValid", StringComparison.Ordinal))
        throw new Exception("Writable forgery did not fail scalar validation: " + rejection.Output);
}
foreach (var branch in new[] { false, true })
{
    using var module = ModuleDefinition.ReadModule(assembly);
    var method = module.GetType("Examples.ArrayElementReferences").Methods.Single(method => method.Name == "Element");
    var prefix = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Readonly);
    var address = prefix.Next;
    var il = method.Body.GetILProcessor();
    if (branch) il.InsertBefore(prefix, Instruction.Create(OpCodes.Br, address));
    else il.InsertAfter(prefix, Instruction.Create(OpCodes.Nop));
    var malformed = Path.Combine(root, branch ? "Branch.dll" : "Separated.dll");
    module.Write(malformed);
    var rejection = Execute(["dotnet", ExtractorPath, "extract", malformed,
        "ArrayElementReferences::Element(System.Int32[],System.Int32)", Path.Combine(root, "Rejected")]);
    var expected = branch ? "Branch enters an array address" : "Readonly prefix requires";
    if (rejection.Code == 0 || !rejection.Output.Contains(expected, StringComparison.Ordinal))
        throw new Exception("Wrong readonly-prefix rejection: " + rejection.Output);
    Console.WriteLine("PASS malformed readonly prefix: " + expected);
}

evidence.Check(replay: false);
