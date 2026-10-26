#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var extractor = Assembly.LoadFrom(ExtractorPath);
var contextType = extractor.GetType("Nethermind.LeanCIL.StaticValues+Context", true)!;
var resolve = contextType.GetMethod("Resolve", BindingFlags.Instance | BindingFlags.NonPublic)!;
object Context(ModuleDefinition module) => Activator.CreateInstance(contextType,
    BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic, null, [module], null)!;
object Resolve(object context, FieldDefinition field) => resolve.Invoke(context, [field, "scalar"])!;
void Reject(Action action, string marker)
{
    try { action(); }
    catch (TargetInvocationException error) when (
        error.InnerException!.Message.Contains(marker, StringComparison.Ordinal))
    { return; }
    throw new Exception("Expected static initializer rejection: " + marker);
}
MethodDefinition Method(TypeDefinition type, string name, params Instruction[] code)
{
    var method = new MethodDefinition(name, Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static,
        type.Module.TypeSystem.Void);
    foreach (var instruction in code) method.Body.Instructions.Add(instruction);
    type.Methods.Add(method);
    return method;
}
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var context = Context(module);
    foreach (var field in module.GetType("Examples.StaticScalars").Fields)
    {
        var value = Resolve(context, field);
        var bytes = (byte[])value.GetType().GetProperty("Bytes")!.GetValue(value)!;
        if (bytes.Length == 0) throw new Exception("Missing scalar bytes");
    }
}
foreach (var scenario in new[] { "twice", "flow", "branch", "switch", "foreign", "outside", "address", "fresh" })
{
    using var module = ModuleDefinition.ReadModule(assembly);
    var type = module.GetType("Examples.StaticScalars");
    var field = type.Fields.Single(field => field.Name == "Byte");
    var constructor = type.Methods.Single(method => method.IsConstructor);
    var code = constructor.Body.Instructions;
    var store = code.Single(instruction => instruction.OpCode.Code == Code.Stsfld &&
        ((FieldReference)instruction.Operand).Name == field.Name);
    var context = Context(module);
    string marker;
    if (scenario == "twice")
    {
        code.Add(Instruction.Create(OpCodes.Stsfld, field));
        marker = "stores it 2 times";
    }
    else if (scenario == "flow")
    {
        code.Insert(0, Instruction.Create(OpCodes.Br, store));
        marker = "Control flow precedes its store";
    }
    else if (scenario is "branch" or "switch" or "foreign")
    {
        var target = scenario == "foreign" ? Instruction.Create(OpCodes.Nop) : store;
        code.Add(scenario == "switch" ? Instruction.Create(OpCodes.Switch, new[] { target, target }) :
            Instruction.Create(OpCodes.Br, target));
        marker = "A branch re-enters";
    }
    else if (scenario == "address")
    {
        var helper = Method(type, "AddressHelper", Instruction.Create(OpCodes.Ldsflda, field),
            Instruction.Create(OpCodes.Pop), Instruction.Create(OpCodes.Ret));
        code.Add(Instruction.Create(OpCodes.Call, helper));
        marker = "Its address is taken during initialization, in " + helper.FullName;
    }
    else
    {
        if (scenario == "fresh")
        {
            Resolve(context, field);
            field = type.Fields.Single(field => field.Name == "Short");
        }
        var writer = Method(type, "FirstWriter", Instruction.Create(OpCodes.Stsfld, field),
            Instruction.Create(OpCodes.Ret));
        Method(type, "SecondWriter", Instruction.Create(OpCodes.Stsfld, field),
            Instruction.Create(OpCodes.Ret));
        marker = "It is also stored outside its static constructor, in " + writer.FullName;
        if (scenario == "fresh") context = Context(module);
    }
    Reject(() => Resolve(context, field), marker);
}
Console.WriteLine("PASS scalar copies, control flow, switch/foreign targets, outside writes and fresh contexts");
foreach (var errorFirst in new[] { false, true })
{
    using var module = ModuleDefinition.ReadModule(assembly);
    var type = module.GetType("Examples.StaticScalars");
    var field = type.Fields.Single(field => field.Name == "Byte");
    var absent = new AssemblyNameReference("MissingStaticIndexAssembly", new Version(1, 0));
    var unknown = new FieldReference("Unknown", module.TypeSystem.Int32,
        new TypeReference("Missing", "Owner", module, absent));
    var broken = Method(type, "BrokenWriter", Instruction.Create(OpCodes.Stsfld, unknown),
        Instruction.Create(OpCodes.Ret));
    var writer = Method(type, "KnownWriter", Instruction.Create(OpCodes.Stsfld, field),
            Instruction.Create(OpCodes.Ret));
    if (!errorFirst)
    {
        type.Methods.Remove(broken);
        type.Methods.Add(broken);
    }
    Reject(() => Resolve(Context(module), field), errorFirst ? "MissingStaticIndexAssembly" :
        "It is also stored outside its static constructor, in " + writer.FullName);
}
Console.WriteLine("PASS indexed scans preserve resolution-error versus first-writer ordering");
