#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var extractor = Assembly.LoadFrom(ExtractorPath);
var resolve = extractor.GetType("Nethermind.LeanCIL.ConstrainedCalls", throwOnError: true)!
    .GetMethod("Resolve", BindingFlags.Static | BindingFlags.NonPublic)!;

object Index(MethodDefinition method) => Activator.CreateInstance(
    extractor.GetType("Nethermind.LeanCIL.InstructionIndex", true)!,
    BindingFlags.Instance | BindingFlags.NonPublic, null, [method], null)!;

foreach (var (receiverName, methodName) in new[]
{
    ("CounterValue", "Read"),
    ("ExplicitCounterValue", "Examples.ICounterValue.Read")
})
{
    using var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll"));
    var method = module.GetType("Examples.ConstrainedCalls").Methods.Single(method => method.Name == "Read");
    var receiver = module.GetType("Examples." + receiverName);
    var prefix = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Constrained);
    prefix.Operand = receiver;
    var resolution = resolve.Invoke(null, [method, prefix.Next, Index(method), "scalar"])!;
    var target = (MethodDefinition)resolution.GetType().GetProperty("Target")!.GetValue(resolution)!;
    if (target.DeclaringType != receiver || target.Name != methodName)
        throw new Exception("Incorrect concrete constrained implementation: " + target.FullName);
    Console.WriteLine("PASS constrained resolution: " + receiverName);
}

foreach (var (mutation, marker) in new[]
{
    ("branch", "Branch bypasses constrained receiver prefix"),
    ("switch", "Branch bypasses constrained receiver prefix"),
    ("reference", "concrete same-assembly struct"),
    ("missing", "no unique struct implementation"),
    ("ordinary", "adjacent concrete constrained receiver"),
    ("generic-direct", "require a non-generic interface slot")
})
{
    using var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll"));
    var method = module.GetType("Examples.ConstrainedCalls").Methods.Single(method => method.Name == "Read");
    var receiver = module.GetType("Examples.CounterValue");
    var prefix = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Constrained);
    var call = prefix.Next;
    prefix.Operand = receiver;
    switch (mutation)
    {
        case "branch":
            method.Body.GetILProcessor().InsertBefore(prefix, Instruction.Create(OpCodes.Br, call));
            break;
        case "switch":
            method.Body.GetILProcessor().InsertBefore(prefix, Instruction.Create(OpCodes.Switch, [call, call]));
            break;
        case "reference": prefix.Operand = module.GetType("Examples.ConstrainedCalls"); break;
        case "missing": receiver.Methods.Remove(receiver.Methods.Single(method => method.Name == "Read")); break;
        case "ordinary": prefix.OpCode = OpCodes.Nop; prefix.Operand = null; break;
        case "generic-direct":
            var definition = module.GetType("Examples.GenericCounterValue`1");
            var generic = new GenericInstanceType(definition);
            generic.GenericArguments.Add(module.TypeSystem.Int32);
            prefix.Operand = generic;
            call.Operand = definition.Methods.Single(member => member.Name == "Read" && !member.HasGenericParameters);
            break;
    }
    try
    {
        resolve.Invoke(null, [method, call, Index(method), "scalar"]);
        throw new Exception("Constrained resolver accepted " + mutation);
    }
    catch (TargetInvocationException error) when
        (error.InnerException is InvalidDataException rejected && rejected.Message.Contains(marker, StringComparison.Ordinal))
    {
        Console.WriteLine("PASS constrained rejection: " + mutation);
    }
}
