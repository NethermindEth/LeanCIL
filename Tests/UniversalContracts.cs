#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/UniversalContracts");

foreach (var (owner, name, selector, proofName) in new[]
{
    ("Arithmetic", "Choose", "Arithmetic::Choose(bool,ulong,ulong)", "Choose"),
    ("GenericMethods", "Identity64", "GenericMethods::Identity64(ulong)", "GenericIdentity"),
    ("Arithmetic", "Struct", "Arithmetic::Struct(ulong)", "Struct")
})
{
    var proof = At($"Examples/Proofs/{proofName}.lean");
    verification.Verify(assembly, "Examples", selector, proof, Path.Combine(root, name));
    Console.WriteLine($"PASS universal {name}: arbitrary inputs and caller memory with preservation");

    var wrong = Path.Combine(root, "Wrong" + name);
    Directory.CreateDirectory(wrong);
    var dll = Path.Combine(wrong, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples." + owner).Methods.Single(method => method.Name == name);
        if (name == "Choose")
        {
            foreach (var instruction in method.Body.Instructions)
                if (instruction.OpCode == OpCodes.Ldarg_1) instruction.OpCode = OpCodes.Ldarg_2;
                else if (instruction.OpCode == OpCodes.Ldarg_2) instruction.OpCode = OpCodes.Ldarg_1;
        }
        else
        {
            var target = name == "Struct"
                ? method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Stfld &&
                    ((FieldReference)instruction.Operand).Name == "Payload")
                : method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ret);
            var il = method.Body.GetILProcessor();
            il.InsertBefore(target, Instruction.Create(OpCodes.Ldc_I8, 1L));
            il.InsertBefore(target, Instruction.Create(OpCodes.Add));
        }
        module.Write(dll);
    }

    // Confirm the mutant is executable and has an actual wrong result, including wraparound.
    var runtime = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples." + owner)!
        .GetMethod(name, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static)!;
    object[] inputs = name == "Choose" ? [true, ulong.MaxValue, 0UL] : [ulong.MaxValue];
    if ((ulong)runtime.Invoke(null, inputs)! == ulong.MaxValue)
        throw new InvalidOperationException("Mutation did not change the result: " + name);

    // Extraction must succeed: the unchanged contract must reject supported, incorrect CIL.
    Run(Extract("extract", dll, "Examples", selector, wrong));
    File.WriteAllText(Path.Combine(wrong, "verified.json"), "stale report");
    var rejected = false;
    try
    {
        verification.Verify(dll, "Examples", selector, proof, wrong, existingArtifacts: true);
    }
    catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
    {
        rejected = true;
    }
    if (!rejected || File.Exists(Path.Combine(wrong, "verified.json")))
        throw new InvalidOperationException("Incorrect implementation accepted: " + name);
    Console.WriteLine($"PASS unchanged universal {name} contract rejects incorrect compiled CIL");
}
