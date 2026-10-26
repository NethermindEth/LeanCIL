#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var extractor = Assembly.LoadFrom(ExtractorPath);
var indexType = extractor.GetType("Nethermind.LeanCIL.InstructionIndex", true)!;
var position = indexType.GetMethod("Position", BindingFlags.Instance | BindingFlags.NonPublic)!;
var isTarget = indexType.GetMethod("IsTarget", BindingFlags.Instance | BindingFlags.NonPublic)!;
var validate = extractor.GetType("Nethermind.LeanCIL.Arrays", true)!
    .GetMethod("ValidateReadOnly", BindingFlags.Static | BindingFlags.NonPublic)!;
object Index(MethodDefinition method) => Activator.CreateInstance(indexType,
    BindingFlags.Instance | BindingFlags.NonPublic, null, [method], null)!;
using var module = ModuleDefinition.CreateModule("Indexes", ModuleKind.Dll);
var method = new MethodDefinition("Body", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
var first = Instruction.Create(OpCodes.Nop);
var prefix = Instruction.Create(OpCodes.Readonly);
var address = Instruction.Create(OpCodes.Ldelema, module.TypeSystem.Int32);
var branch = Instruction.Create(OpCodes.Br, prefix);
foreach (var instruction in new[] { first, branch, prefix, address, Instruction.Create(OpCodes.Ret) })
    method.Body.Instructions.Add(instruction);
var index = Index(method);
for (var offset = 0; offset < method.Body.Instructions.Count; offset++)
    if ((int)position.Invoke(index, [method.Body.Instructions[offset]])! != offset)
        throw new Exception("Instruction position used byte offsets instead of identity");
if ((int)position.Invoke(index, [Instruction.Create(OpCodes.Nop)])! != -1)
    throw new Exception("Foreign instruction was admitted");
validate.Invoke(null, [index, prefix]);
foreach (var switched in new[] { false, true })
{
    branch.OpCode = switched ? OpCodes.Switch : OpCodes.Br;
    branch.Operand = switched ? new[] { address, address } : address;
    index = Index(method);
    if (!(bool)isTarget.Invoke(index, [address])!) throw new Exception("Missing prefix-bypass target");
    try
    {
        validate.Invoke(null, [index, prefix]);
        throw new Exception("Accepted a branch bypassing readonly");
    }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
        rejected.Message.Contains("Branch enters an array address", StringComparison.Ordinal)) { }
}
method.Body.Instructions.Insert(0, Instruction.Create(OpCodes.Nop));
if ((int)position.Invoke(Index(method), [first])! != 1)
    throw new Exception("Fresh traversal retained stale instruction positions");
Console.WriteLine("PASS instruction identity, missing targets, fresh indexes and readonly branch/switch rejection");

var owner = new TypeDefinition("", "Methods", Mono.Cecil.TypeAttributes.Public, module.TypeSystem.Object);
module.Types.Add(owner);
var caller = new MethodDefinition("Caller", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
var callee = new MethodDefinition("Callee", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
owner.Methods.Add(caller);
owner.Methods.Add(callee);
callee.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
var call = Instruction.Create(OpCodes.Call, callee);
caller.Body.Instructions.Add(call);
caller.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
var translate = extractor.GetType("Nethermind.LeanCIL.InstructionTranslation", true)!
    .GetMethod("Translate", BindingFlags.Static | BindingFlags.NonPublic)!;
var methods = new Dictionary<MethodDefinition, int> { [caller] = 0, [callee] = 1 };
string Translate(Instruction instruction) => (string)translate.Invoke(null,
    [instruction, caller, methods, 0, Index(caller), null, null, null, null])!;
if (Translate(call) != ".call 1 0") throw new Exception("Incorrect call index");
methods.Remove(callee);
try
{
    Translate(call);
    throw new Exception("Unresolved method was assigned a call index");
}
catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
    rejected.Message.Contains("Unsupported or unresolved call", StringComparison.Ordinal)) { }
methods.Add(callee, 1);
caller.Body.Instructions.Clear();
var destination = Instruction.Create(OpCodes.Ret);
var choose = Instruction.Create(OpCodes.Switch, [destination, destination]);
caller.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I4_0));
caller.Body.Instructions.Add(choose);
caller.Body.Instructions.Add(destination);
if (Translate(choose) != ".switch [2, 2]") throw new Exception("Switch target order or duplicates changed");
Console.WriteLine("PASS translated method indexes reject missing callees and preserve switch target order");